import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, readFile, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const action = fileURLToPath(new URL('run.mjs', import.meta.url));
const manifest = new URL('action.yml', import.meta.url);
const workflow = new URL('../../workflows/ci-current.yml', import.meta.url);
const bytes = '{"target":"A","complete":true}';
const digest = createHash('sha256').update(bytes).digest('hex');

async function fixture(t) {
  const root = await mkdtemp(join(tmpdir(), 'generation-transport-'));
  t.after(() => rm(root, { recursive: true, force: true }));
  const bin = join(root, 'bin');
  const sdk = join(bin, 'sdk');
  await mkdir(join(sdk, 'internal'), { recursive: true });
  // Install a recording cache SDK at exactly the path resolved by the action.
  await writeFile(join(bin, 'npm'), `#!/bin/sh
set -eu
echo install >> "$(dirname "$0")/installs"
mkdir -p node_modules/@actions/cache
cp -R "$(dirname "$0")/sdk" node_modules/@actions/cache/lib
`, { mode: 0o755 });
  await writeFile(join(sdk, 'internal/cacheUtils.js'),
    'exports.getCompressionMethod = async () => "zstd"; exports.getCacheVersion = () => "sdk-version";\n');
  await writeFile(join(sdk, 'cache.js'), `
const fs = require("node:fs");
const assert = require("node:assert/strict");
const wire = 'build/lean-cache/generation/index.json';
exports.restoreCache = async function(paths, key, prefixes, options) {
  const path = key.startsWith("lean-shard-index-")
    ? (key.includes("-snapshot-") ? "build/lean-cache/shards/index.json"
      : "build/lean-cache/shards/payload/" + key.split("-").pop() + ".tar.gz") : wire;
  assert.deepEqual(paths, [path]);
  assert.deepEqual(prefixes, []);
  fs.appendFileSync("requests", "get " + key + "\\n");
  if (!fs.existsSync(key)) return undefined;
  if (!options?.lookupOnly) { fs.mkdirSync(require("node:path").dirname(path), {recursive: true}); fs.copyFileSync(key, path); }
  return key;
};
exports.saveCache = async function(paths, key) {
  assert.deepEqual(paths, [wire]);
  fs.appendFileSync("requests", "put " + key + "\\n");
  fs.copyFileSync(wire, key, fs.constants.COPYFILE_EXCL);
  return 1;
};`);
  const env = {
    ...process.env,
    PATH: bin + ':' + process.env.PATH,
    GITHUB_WORKSPACE: root,
    RUNNER_TEMP: root,
    GITHUB_OUTPUT: join(root, 'outputs'),
    GITHUB_SHA: 'b'.repeat(40),
    GH_TOKEN: 'test',
    PYTHONPATH: process.env.LEAN_GENERATION_TEST_TOOLS || fileURLToPath(new URL('../../../tools/scripts/worktree', import.meta.url)),
    GITHUB_REF: 'refs/heads/dev',
    GITHUB_REF_PROTECTED: 'true',
    GITHUB_REPOSITORY: 'owner/repo',
    GITHUB_WORKFLOW_REF: 'owner/repo/.github/workflows/cache-release-publish.yml@refs/heads/dev',
    STRATALINT_CACHE_WRITES: 'true',
  };
  await writeFile(join(root, 'input.json'), bytes);
  await writeFile(join(root, 'requests'), '');
  const requests = () => readFile(join(root, 'requests'), 'utf8');
  const run = (event, operation, sha = digest, file = 'output.json') =>
    spawnSync(process.execPath, [action, operation, sha, file], {
      encoding: 'utf8', cwd: root, env: { ...env, GITHUB_EVENT_NAME: event },
    });
  return { root, requests, run, env };
}

for (const event of ['push', 'pull_request']) {
  test(event + ' hit, miss and post-job perform zero cache writes', async t => {
    const { root, requests, run } = await fixture(t);
    const published = 'lean-generation-v1-' + digest;
    await writeFile(join(root, published), bytes);
    const hit = run(event, 'generation-get');
    assert.equal(hit.status, 0, hit.stderr);
    assert.equal(await readFile(join(root, 'output.json'), 'utf8'), bytes);
    const miss = run(event, 'generation-get', '0'.repeat(64));
    assert.equal(miss.status, 4);
    assert.match(miss.stderr, /missing Actions generation index/);
    const forbidden = run(event, 'generation-put', digest, 'input.json');
    assert.equal(forbidden.status, 1);
    assert.match(forbidden.stderr, /require the protected dev Release publisher/);
    assert.deepEqual((await requests()).trim().split('\n'), [
      'get ' + published,
      'get lean-generation-v1-' + '0'.repeat(64),
    ]);
    const actionYaml = await readFile(manifest, 'utf8');
    assert.doesNotMatch(actionYaml, /^\s*post(?:-if)?:/m);
    const current = await readFile(workflow, 'utf8');
    assert.match(current, /operation: restore-published/);
    assert.doesNotMatch(current, /uses:\s*actions\/cache(?:@|\/save@)/);
    for (const setup of current.matchAll(/uses:\s*actions\/setup-dotnet@[^\n]*\n((?: {8,}[^\n]*\n)+)/g)) {
      assert.match(setup[1], /^\s*cache: false$/m);
    }
  });
}

test('publisher retries verify existing bytes and conflicting contents fail', async t => {
  const { root, requests, run } = await fixture(t);
  for (const event of ['schedule', 'workflow_dispatch']) {
    const result = run(event, 'generation-put', digest, 'input.json');
    assert.equal(result.status, 0, result.stderr);
  }
  assert.equal((await requests()).split('\n').filter(line => line.startsWith('put ')).length, 1);
  assert.equal(await readFile(join(root, 'bin/installs'), 'utf8'), 'install\n');
  await writeFile(join(root, 'lean-generation-v1-' + digest), 'different');
  const corruptRead = run('push', 'generation-get');
  assert.equal(corruptRead.status, 5);
  const conflict = run('schedule', 'generation-put', digest, 'input.json');
  assert.equal(conflict.status, 1);
  assert.match(conflict.stderr, /corrupt Actions generation index/);
  assert.equal((await requests()).split('\n').filter(line => line.startsWith('put ')).length, 1);
});

test('migration pins the newest complete verified owner and checks each streamed payload', async t => {
  const { root, requests, run } = await fixture(t);
  await symlink(fileURLToPath(new URL('../../', import.meta.url)), join(root, '.github'));
  await mkdir(join(root, 'tools/scripts/worktree'), { recursive: true });
  const hash = value => createHash('sha256').update(value).digest('hex');
  const prefix = 'lean-shard-index-v1-' + hash('{}') + '-';
  const material = prefix + 'material-' + digest;
  const commit = 'a'.repeat(40);
  const group = hash('[["A"]]');
  const inventory = [];
  const row = (key, id) => ({ key, version: 'sdk-version', ref: 'refs/heads/dev',
    created_at: '2026-01-0' + id + 'T12:00:00Z' });
  for (const id of ['1', '2', '3']) {
    const key = prefix + 'snapshot-' + id + '-1';
    const index = {
      state: id === '3' ? 'resume' : 'complete', binding: {},
      owner: { commit, ref: 'refs/heads/dev', run: id, attempt: '1' },
      entries: { [group]: id === '2' ? 'e'.repeat(64) : digest },
      required: { [group]: ['lib/lean/A.olean'] }, layout: { [group]: [['A']] },
      sources: { A: digest }, fingerprints: { [group]: digest },
    };
    await writeFile(join(root, key), JSON.stringify(index));
    inventory.push(row(key, id));
  }
  inventory.push(row(material, '1'));
  await writeFile(join(root, 'bin/git'), '#!/bin/sh\necho "' + 'b'.repeat(40) + '"\n', { mode: 0o755 });
  await writeFile(join(root, material), bytes);
  await writeFile(join(root, 'inventory'), inventory.map(i => JSON.stringify(i)).join('\n'));
  await writeFile(join(root, 'bin/gh'), `#!/bin/sh
case "$*" in
  *git/ref/tags/lean-generation-bootstrap-v1*) if test -f pin-ref; then cat pin-ref; else echo '{"status":"404"}'; exit 1; fi ;;
  *git/blobs*--method*) jq '. + {sha:"blob",size:(.content|@base64d|length)}' > seed-blob; echo '{"sha":"blob"}' ;;
  *git/tags*--method*) jq '. + {object:{sha:.object,type:.type}}' > seed-tag; echo '{"sha":"tag"}' ;;
  *git/refs*--method*) jq '. + {object:{sha:.sha,type:"tag"}}' > pin-ref; cat pin-ref ;;
  *git/tags/tag*) cat seed-tag ;;
  *git/blobs/blob*) cat seed-blob ;;
  *actions/caches*) cat inventory ;;
  *branches/dev*) echo '{"protected":true,"commit":{"sha":"${commit}"}}' ;;
  *actions/runs/1/attempts/1*) echo '{"id":1,"run_attempt":1,"status":"completed","conclusion":"success","event":"push","head_branch":"dev","head_sha":"${commit}","head_repository":{"full_name":"owner/repo"},"path":".github/workflows/lean-cache-publish.yml"}' ;;
  *compare/*) echo '{"ancestor":"${commit}"}' ;;
  *) exit 2 ;;
esac
`, { mode: 0o755 });
  const chosen = run('schedule', 'latest-seed');
  assert.equal(chosen.status, 0, chosen.stderr);
  const base = join(root, 'lean-generation-base');
  const pin = JSON.parse(await readFile(join(base, 'seed.json')));
  assert.equal(pin.key, prefix + 'snapshot-1-1');
  assert.equal(pin.index_sha256, hash(await readFile(join(base, 'index.json'))));
  await rm(join(root, pin.key));
  await rm(join(root, 'inventory'));
  await rm(base, { recursive: true });
  const retry = run('schedule', 'latest-seed');
  assert.equal(retry.status, 0, retry.stderr);
  assert.deepEqual(JSON.parse(await readFile(join(base, 'seed.json'))), pin);
  assert.equal(hash(await readFile(join(base, 'index.json'))), pin.index_sha256);
  await writeFile(join(root, 'tools/scripts/worktree/lean_generation_seed.py'), `
import json
from pathlib import Path
print(json.dumps({"request": ["${digest}"]}), flush=True)
verified = json.loads(input())
assert verified == (["${digest}"] if not Path("corrupt").exists() else [])
assert Path("build/lean-cache/shards/payload/${digest}.tar.gz").is_file()
print(json.dumps({"result": {"verified": len(verified)}}), flush=True)
`);
  const migration = run('schedule', 'migrate-seed');
  assert.equal(migration.status, 0, migration.stderr);
  await assert.rejects(readFile(join(root, 'build/lean-cache/shards/payload', digest + '.tar.gz')), { code: 'ENOENT' });
  await writeFile(join(root, material), 'corrupt bytes');
  await writeFile(join(root, 'corrupt'), '');
  const corrupt = run('schedule', 'migrate-seed');
  assert.equal(corrupt.status, 0, corrupt.stderr);
  assert.match(corrupt.stdout, /"verified":0/);
  assert.doesNotMatch(await requests(), /^put /m);
});

test('handover disables the legacy ID before draining and recovers the original dev pin', async t => {
  const { root } = await fixture(t);
  const tip = 'b'.repeat(40);
  const earlier = 'a'.repeat(40);
  await writeFile(join(root, 'bin/gh'), `#!/bin/sh
case "$*" in
  *actions/runs/7) echo '{"workflow_id":2,"path":".github/workflows/cache-release-publish.yml","head_branch":"dev"}' ;;
  *actions/workflows/lean-cache-publish.yml) if test -f disabled; then state=disabled_manually; else state=active; fi
    echo '{"id":1,"path":".github/workflows/lean-cache-publish.yml","state":"'"$state"'"}' ;;
  *PUT*actions/workflows/1/disable) touch disabled ;;
  *actions/workflows/1) if test -f disabled && ! test -f deny-disable; then state=disabled_manually; else state=active; fi
    echo '{"id":1,"path":".github/workflows/lean-cache-publish.yml","state":"'"$state"'"}' ;;
  *actions/workflows/1/runs*status=queued*) test -f disabled || exit 3; echo '[{"workflow_runs":[{"id":4}]}]' ;;
  *actions/workflows/1/runs*status=in_progress*) echo '[{"workflow_runs":[{"id":4}]}]' ;;
  *actions/workflows/1/runs*status=*) echo '[{"workflow_runs":[]}]' ;;
  'run watch 4 '*) echo watch >> watched ;;
  *actions/runs/7/artifacts*) if test -f pin-exists; then echo '[{"artifacts":[{"name":"generation-pin-7","expired":false}]}]'; else echo '[{"artifacts":[]}]'; fi ;;
  *actions/runs/7/jobs*) if test -f pin-was-successful; then echo '[{"jobs":[{"name":"pin","conclusion":"success"}]}]'; else echo '[{"jobs":[{"name":"pin","conclusion":"failure"}]}]'; fi ;;
  *branches/dev*) echo '{"protected":true,"commit":{"sha":"${tip}"}}' ;;
  'run download 7 '*) echo '${earlier}' > pin/source ;;
  *compare/*) echo '${earlier}' ;;
  *) echo "Unexpected request $*" >&2; exit 2 ;;
esac
`, { mode: 0o755 });
  const command = fileURLToPath(new URL('handover.py', import.meta.url));
  const invoke = () => spawnSync('python3', ['-B', command], { cwd: root, encoding: 'utf8', env: {
    ...process.env, PATH: join(root, 'bin') + ':' + process.env.PATH,
    GITHUB_RUN_ID: '7', GITHUB_RUN_ATTEMPT: '2', GITHUB_REPOSITORY: 'owner/repo', GITHUB_REF_PROTECTED: 'true',
    RUNNER_TEMP: root, GITHUB_OUTPUT: join(root, 'outputs'),
  }});
  // The first attempt failed before it could upload its pin.
  await writeFile(join(root, 'deny-disable'), '');
  assert.equal(invoke().status, 1);
  await assert.rejects(readFile(join(root, 'watched')), { code: 'ENOENT' });
  await rm(join(root, 'deny-disable'));
  const retry = invoke();
  assert.equal(retry.status, 0, retry.stderr);
  assert.equal(await readFile(join(root, 'watched'), 'utf8'), 'watch\n');
  assert.equal(await readFile(join(root, 'outputs'), 'utf8'), 'source=' + tip + '\nupload=true\n');
  await writeFile(join(root, 'pin-was-successful'), '');
  assert.equal(invoke().status, 1);
  await writeFile(join(root, 'pin-exists'), '');
  const resume = invoke();
  assert.equal(resume.status, 0, resume.stderr);
  assert.match(await readFile(join(root, 'outputs'), 'utf8'), new RegExp('source=' + earlier + '\\nupload=false\\n$'));
});

test('ordinary push and PR restore a scoped generation from cold workspaces', async t => {
  for (const [event, evict] of [['push', false], ['pull_request', true]]) {
    const { root, requests, run, env } = await fixture(t);
    const dir = join(root, 'tools/scripts/worktree');
    await mkdir(dir, { recursive: true });
    const prepare = spawnSync('python3', ['-B', '-c', `
from pathlib import Path
from lean_generation_index import encode
from test_lean_cache_generation import Generations
generation = Generations()
generation.setUp()
try:
    generation.commit(generation.plan, None, [generation.receipt])
    store = generation.remote
    Path("plan").write_bytes(encode(generation.plan))
    Path("marker").write_bytes(encode(store.marker))
    digest = store.marker["index"]
    Path("release-index").write_bytes(store.indexes["release"][digest])
    Path("lean-generation-v1-" + digest).write_bytes(store.indexes["ci"][digest])
    for address, data in store.volumes.items():
        Path(address).write_bytes(data)
finally:
    generation.doCleanups()
`], { cwd: root, env, encoding: 'utf8' });
    assert.equal(prepare.status, 0, prepare.stderr);
    const marker = JSON.parse(await readFile(join(root, 'marker')));
    if (evict) await rm(join(root, 'lean-generation-v1-' + marker.index));
    await writeFile(join(dir, 'lean_cache_generation.py'), `
import os, subprocess, sys
from pathlib import Path
sys.path.insert(0, os.environ["PYTHONPATH"])
import lean_cache_generation as cli
from lean_generation_index import read, sha
class Transport:
    deadline = None
    def __init__(self, root, deadline): pass
    def current(self): return "verified", read("marker")
    def get_index(self, digest, output, transport):
        if transport == "ci":
            subprocess.run(["node", ${JSON.stringify(action)}, "generation-get", digest, str(output)], check=True)
        else:
            output.write_bytes(Path("release-index").read_bytes())
        assert sha(output.read_bytes()) == digest
        return read(output)
    def volume(self, digest, size): return Path(digest)
    def blocks(self, path, start, size): yield path.read_bytes()[start:start + size]
cli.GitHub = Transport
cli.checkout_plan = lambda root: read("plan")
sys.exit(cli.main())
`);
    env.INPUT_TARGETS = 'B';
    const recovered = run(event, 'restore-published');
    assert.equal(recovered.status, 0, recovered.stderr);
    assert.equal(await readFile(join(root, '.lake/build/lib/lean/A.olean'), 'utf8'), 'library');
    assert.equal(await readFile(join(root, '.lake/build/lib/lean/B.olean'), 'utf8'), 'consumer');
    assert.equal(await requests(), 'get lean-generation-v1-' + marker.index + '\n');
  }
});
