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
    PYTHONPATH: fileURLToPath(new URL('../../../tools/scripts/worktree', import.meta.url)),
    GITHUB_REF: 'refs/heads/dev',
    GITHUB_REF_PROTECTED: 'true',
    GITHUB_REPOSITORY: 'owner/repo',
    GITHUB_WORKFLOW_REF: 'owner/repo/.github/workflows/lean-cache-publish.yml@refs/heads/dev',
    STRATALINT_CACHE_WRITES: 'true',
  };
  await writeFile(join(root, 'input.json'), bytes);
  await writeFile(join(root, 'requests'), '');
  const requests = () => readFile(join(root, 'requests'), 'utf8');
  const run = (event, operation, sha = digest, file = 'output.json') =>
    spawnSync(process.execPath, [action, operation, sha, file], {
      encoding: 'utf8', cwd: root, env: { ...env, GITHUB_EVENT_NAME: event },
    });
  return { root, requests, run };
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
    assert.equal(miss.status, 1);
    assert.match(miss.stderr, /missing or corrupt/);
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
  await writeFile(join(root, 'lean-generation-v1-' + digest), 'different');
  const conflict = run('schedule', 'generation-put', digest, 'input.json');
  assert.equal(conflict.status, 1);
  assert.match(conflict.stderr, /missing or corrupt/);
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
