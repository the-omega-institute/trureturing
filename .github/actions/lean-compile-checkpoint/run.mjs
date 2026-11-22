import { DefaultArtifactClient } from '@actions/artifact';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, statSync } from 'node:fs';
import { join } from 'node:path';

const env = process.env;
const stage = env.STAGE;
if (!['common', '0', '1', '2', '3'].includes(stage)) throw new Error('unknown compiler stage');
const targets = (env.LEAN_LAYER_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const tmp = mkdtempSync(join(env.RUNNER_TEMP, 'layer-progress-'));
const archiveDir = join(env.RUNNER_TEMP, 'lean-compile');
const api = 'tools/scripts/worktree/lean_compile_layers.py';
const helper = '.github/actions/lean-report-compile-checkpoint/progress.py';
const options = ['--stage', stage, '--artifacts', archiveDir, ...(targets.length ? ['--target', ...targets] : [])];
const recovery = env.LEAN_LAYER_RECOVERY === 'true';
const recoveryTool = '.github/actions/lean-compile-checkpoint/recovery.py';
const checkout = execFileSync('git', ['rev-parse', 'HEAD'], {encoding: 'utf8'}).trim();
env.PROJECT_SEED = createHash('sha256').update(JSON.stringify([checkout, stage, targets])).digest('hex');
const dependencyPins = execFileSync('git', ['ls-tree', 'HEAD', '--', 'lean-toolchain', 'lake-manifest.json']);
env.DEPENDENCY_SEED = createHash('sha256').update(dependencyPins).digest('hex');
mkdirSync(archiveDir, {recursive: true});

function progress(command, dir, context = {}) {
  execFileSync('python3', ['-B', helper, command, dir], {stdio: 'inherit', env: {...env, ...context}});
}
function compiler(seconds, probe, out, batch) {
  const command = ['tools/scripts/report/report-supervisor.sh',
    '--role', 'lean-layer-' + stage, '--', 'python3', ...(batch ? [recoveryTool, 'build', ...batch] : [api, 'build', ...options])];
  return new Promise((resolve, reject) => {
    // The supervisor owns the compiler's process group and reaps it before packing.
    const proc = spawn('bash', probe ? command : ['.github/actions/lean-compile-layer/measure.sh', 'bash', ...command], {
      env: {...env, STRATALINT_BUILD_TIMEOUT_SECONDS: String(seconds)}, stdio: 'inherit'
    });
    let cut = false;
    const watch = probe ? setInterval(() => {
      if (!cut && spawnSync('python3', ['-B', helper, 'changed', out], {stdio: 'ignore'}).status === 0) {
        cut = proc.kill('SIGTERM');
      }
    }, 1000) : undefined;
    proc.once('error', error => { clearInterval(watch); reject(error); });
    proc.once('exit', (status, signal) => {
      clearInterval(watch);
      resolve({status: cut && (status !== 0 || signal) ? 124 : status, cut});
    });
  });
}

const [repositoryOwner, repositoryName] = env.GITHUB_REPOSITORY.split('/');
const findBy = {token: env.GH_TOKEN, repositoryOwner, repositoryName, workflowRunId: Number(env.GITHUB_RUN_ID)};
const prefix = 'lean-compile-progress-' + env.GITHUB_RUN_ID + '-' + stage + '-';
const client = new DefaultArtifactClient();
async function restore(run, external) {
  const apiPath = 'repos/' + env.GITHUB_REPOSITORY + '/actions/runs/' + run;
  const pages = JSON.parse(execFileSync('gh', ['api', '--paginate', '--slurp', apiPath + '/artifacts?per_page=100'], {encoding: 'utf8'}));
  const binding = 'lean-compile-progress-' + run + '-' + stage + '-';
  const previous = pages.flatMap(page => page.artifacts)
    .filter(a => !a.expired && a.name.startsWith(binding))
    .map(a => {
      const suffix = a.name.slice(binding.length).match(/^([1-9]\d*)-([1-9]\d*)$/);
      if (!suffix || !/^sha256:[0-9a-f]{64}$/.test(a.digest || '')) throw new Error('invalid progress artifact');
      return {...a, attempt: Number(suffix[1]), round: Number(suffix[2])};
    }).filter(a => external || a.attempt < Number(env.GITHUB_RUN_ATTEMPT))
    .sort((a,b) => a.attempt - b.attempt || a.round - b.round);
  let context = {};
  if (external) {
    const source = JSON.parse(execFileSync('gh', ['api', apiPath], {encoding: 'utf8'}));
    if (source.head_sha !== checkout || source.event !== 'workflow_dispatch'
        || source.path !== '.github/workflows/ci-publication-verify.yml'
        || !source.head_branch.startsWith('diagnostic/lean-compile-progress-')
        || source.head_repository.full_name !== env.GITHUB_REPOSITORY) throw new Error('incompatible checkpoint producer');
    const branch = JSON.parse(execFileSync('gh', ['api', 'repos/' + env.GITHUB_REPOSITORY + '/branches/' + encodeURIComponent(source.head_branch)], {encoding: 'utf8'}));
    if (!branch.protected || branch.commit.sha !== checkout) throw new Error('checkpoint source branch is not pinned');
    context = {GITHUB_RUN_ID: run, GITHUB_SHA: checkout, GITHUB_REF: 'refs/heads/' + source.head_branch};
    if (stage === 'common' && !previous.length) throw new Error('no previous shared compiler outputs');
  }
  for (const a of previous) {
    const dir = join(tmp, 'input-' + a.id);
    const response = await client.downloadArtifact(a.id, {findBy: {...findBy, workflowRunId: Number(run)}, path: dir, expectedHash: a.digest});
    if (response.digestMismatch) throw new Error('progress artifact digest mismatch: ' + a.id);
    console.log('LEAN_LAYER_PROGRESS restoring=' + a.id + ' bytes=' + a.size_in_bytes + ' stage=' + stage);
    progress('restore', dir, context);
    rmSync(dir, {recursive: true});
  }
  return previous.length;
}
if (recovery && stage === 'common') await restore(env.LEAN_LAYER_PARENT_RUN, true);
const restored = await restore(env.GITHUB_RUN_ID, false);
const batches = [];
if (recovery) {
  const plan = join(tmp, 'batches.json');
  execFileSync('python3', ['-B', recoveryTool, 'plan', stage, plan], {stdio: 'inherit'});
  batches.push(...JSON.parse(readFileSync(plan)));
}
const probe = env.LEAN_LAYER_INTERRUPT_PROBE === 'true' && restored === 0;
const interval = recovery ? 120 : 900;
let seconds = interval;
for (let round = 1; ; ++round) {
  const out = join(tmp, 'round-' + round);
  progress('mark', out);
  const batch = batches[0];
  const result = await compiler(seconds, probe, out, batch);
  if (result.status === 0) {
    if (probe) throw new Error('The diagnostic compiler finished before it could be interrupted.');
    if (!batch) break;
    batches.shift();
  }
  if (result.status !== 0 && result.status !== 124) throw new Error('layer compilation failed: ' + result.status);
  progress('save', out);
  const manifest = join(out, 'manifest.json');
  if (!existsSync(manifest)) {
    seconds = result.status === 0 ? interval : Math.min(21600, seconds * 2);
    continue;
  }
  const payload = join(out, 'outputs.tar.gz');
  const name = prefix + env.GITHUB_RUN_ATTEMPT + '-' + round;
  const artifact = await client.uploadArtifact(name, [manifest, payload], out, {compressionLevel: 0, retentionDays: 7});
  if (!artifact.id) throw new Error('progress artifact was not confirmed');
  console.log('LEAN_LAYER_PROGRESS saved=' + artifact.id + ' bytes=' + statSync(payload).size
    + ' stage=' + stage + ' cut=' + result.cut + ' groups=' + JSON.parse(readFileSync(manifest)).groups);
  rmSync(out, {recursive: true});
  if (probe) throw new Error('Controlled compiler interruption persisted. Rerun failed jobs to verify recovery.');
  seconds = interval;
}
