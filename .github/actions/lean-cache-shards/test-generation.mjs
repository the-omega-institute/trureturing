import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, readdir, readFile, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath, pathToFileURL } from 'node:url';

const action = fileURLToPath(new URL('run.mjs', import.meta.url));
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
mkdir -p node_modules/@actions/cache node_modules/@actions/core
echo "exports.warning = console.warn; exports.error = console.error;" > node_modules/@actions/core/index.js
cp -R "$(dirname "$0")/sdk" node_modules/@actions/cache/lib
`, { mode: 0o755 });
  await writeFile(join(sdk, 'internal/cacheUtils.js'),
    'exports.getCompressionMethod = async () => "zstd"; exports.getCacheVersion = () => "sdk-version";\n');
  await writeFile(join(sdk, 'cache.js'), `
const fs = require("node:fs");
const assert = require("node:assert/strict");
const wire = 'build/lean-cache/generation/index.json';
function checkpointStorage(paths, key) {
  const kind = key.split("-")[2];
  assert.deepEqual(paths, ["build/lean-cache/shards/compiler-checkpoints/" + kind]);
  assert.equal(fs.realpathSync(process.env.GITHUB_WORKSPACE), fs.realpathSync("."));
  return require("node:path").join(process.env.CHECKPOINT_STORE, key);
}
exports.restoreCache = async function(paths, key, prefixes, options) {
  if (key.startsWith("lean-compiler-")) {
    const storage = checkpointStorage(paths, key);
    assert.deepEqual(prefixes, []);
    if (process.env.RESTORE_DIAGNOSTIC) {
      require("@actions/core")[process.env.RESTORE_DIAGNOSTIC]("cache service failure");
      return undefined;
    }
    if (process.env.THROTTLE_ONCE && !fs.existsSync(storage + ".throttled")) {
      fs.writeFileSync(storage + ".throttled", "");
      require("@actions/core").warning("Failed to GetCacheEntryDownloadURL: Rate limited: Failed request: (429) Too Many Requests: rate limit exceeded");
      return undefined;
    }
    if (fs.existsSync(storage + ".reserved")) {
      fs.renameSync(storage + ".reserved", storage);
      return undefined;
    }
    if (!fs.existsSync(storage)) return undefined;
    fs.copyFileSync(storage, paths[0]);
    return key;
  }
  if (paths[0].startsWith("build/lean-cache/modules/")) {
    const storage = key + "." + paths[0].split("/")[3];
    fs.appendFileSync("requests", "get " + key + "\\n");
    if (!fs.existsSync(storage)) return undefined;
    if (!options?.lookupOnly) fs.copyFileSync(storage, paths[0]);
    return key;
  }
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
  if (key.startsWith("lean-compiler-")) {
    const storage = checkpointStorage(paths, key);
    if (fs.existsSync(storage) || fs.existsSync(storage + ".reserved")) return -1;
    fs.copyFileSync(paths[0], storage, fs.constants.COPYFILE_EXCL);
    return 1;
  }
  if (paths[0].startsWith("build/lean-cache/modules/")) {
    fs.appendFileSync("requests", "put " + key + "\\n");
    fs.copyFileSync(paths[0], key + "." + paths[0].split("/")[3], fs.constants.COPYFILE_EXCL);
    return 1;
  }
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
  test(event + ' hit and miss perform zero cache writes', async t => {
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

test('compiler checkpoints cross runners, verify reserved entries and rebuild only on eviction', async t => {
  const publisher = await fixture(t);
  const worker = await fixture(t);
  const storage = join(publisher.root, 'cache');
  await mkdir(storage);
  const env = { CHECKPOINT_STORE: storage, GITHUB_EVENT_NAME: 'push' };
  const invoke = (runner, args, overrides = {}) => spawnSync(process.execPath, [action, ...args], {
    cwd: runner.root, env: { ...runner.env, ...env, ...overrides }, encoding: 'utf8',
  });
  const size = Buffer.byteLength(bytes);
  const input = join(publisher.root, 'input.json');
  const output = join(worker.root, 'restored');
  await writeFile(join(worker.root, 'bin/gh'), `#!/bin/sh
case "$*" in
  *actions/caches*ref=refs/heads/dev*key=lean-compiler-*) cat inventory ;;
  *) exit 2 ;;
esac
`, { mode: 0o755 });
  for (const kind of ['unit', 'catalog']) {
    const id = kind === 'catalog' ? digest : 'a'.repeat(64);
    const address = [kind, id, digest, String(size)];
    const key = ['lean-compiler', kind, 'v1', id, digest, size].join('-');
    const put = ['compiler-cache-put', ...address, input];
    const get = ['compiler-cache-get', ...address, output];
    assert.equal(invoke(publisher, put, { GITHUB_EVENT_NAME: 'pull_request' }).status, 1);
    const stored = invoke(publisher, put);
    assert.equal(stored.status, 0, stored.stderr);
    const row = { key, version: 'sdk-version', ref: 'refs/heads/dev' };
    const inventory = [row, { ...row, ref: 'refs/heads/pr' }, { ...row, version: 'different' },
      { ...row, key: key + 'x' }, { ...row, key: key.replace(digest, 'bad') }];
    await writeFile(join(worker.root, 'inventory'), inventory.map(r => JSON.stringify(r)).join('\n'));
    const listFile = join(worker.root, 'listed.json');
    const listed = invoke(worker, ['compiler-cache-list', kind, listFile]);
    assert.equal(listed.status, 0, listed.stderr);
    assert.deepEqual(JSON.parse(await readFile(listFile)), [{ id, sha256: digest, bytes: size }]);
    const restored = invoke(worker, get);
    assert.equal(restored.status, 0, restored.stderr);
    assert.equal(await readFile(output, 'utf8'), bytes);
    await rm(output);
    const cacheFile = join(storage, key);
    if (kind === 'unit') {
      const throttled = invoke(worker, get, { THROTTLE_ONCE: 'true' });
      assert.equal(throttled.status, 0, throttled.stderr);
      assert.match(throttled.stderr, /429.*Too Many Requests/);
      assert.equal(await readFile(output, 'utf8'), bytes);
      await rm(output);
    }
    await writeFile(cacheFile, 'x'.repeat(size));
    assert.match(invoke(worker, get).stderr, /checksum or length mismatch/);
    assert.match(invoke(publisher, put).stderr, /checksum or length mismatch/);
    await assert.rejects(readFile(output), { code: 'ENOENT' });
    await rm(cacheFile);
    assert.equal(invoke(worker, get).status, 4);
    for (const level of ['warning', 'error']) {
      const outage = invoke(worker, get, { RESTORE_DIAGNOSTIC: level });
      assert.equal(outage.status, 1, outage.stderr);
      assert.match(outage.stderr, /cache service failure/);
    }
    await writeFile(cacheFile + '.reserved', bytes);
    const race = invoke(publisher, put);
    assert.equal(race.status, 0, race.stderr);
  }
  const invalidCatalog = invoke(publisher, ['compiler-cache-put', 'catalog', 'a'.repeat(64), digest, String(size), input]);
  assert.match(invalidCatalog.stderr, /invalid compiler checkpoint address/);
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

test('publisher pins dev directly and recovers the original source on retry', async t => {
  const { root } = await fixture(t);
  const tip = 'b'.repeat(40);
  const earlier = 'a'.repeat(40);
  await writeFile(join(root, 'bin/gh'), `#!/bin/sh
case "$*" in
  *actions/runs/7/artifacts*) if test -f pin-exists; then echo '[{"artifacts":[{"name":"generation-pin-7","expired":false}]}]'; else echo '[{"artifacts":[]}]'; fi ;;
  *actions/runs/7/jobs*) if test -f pin-was-successful; then echo '[{"jobs":[{"name":"pin","conclusion":"success"}]}]'; else echo '[{"jobs":[{"name":"pin","conclusion":"failure"}]}]'; fi ;;
  *branches/dev*) echo '{"protected":true,"commit":{"sha":"${tip}"}}' ;;
  'run download 7 '*) echo '${earlier}' > pin/source ;;
  *compare/*) echo '${earlier}' ;;
  *) echo "Unexpected request $*" >&2; exit 2 ;;
esac
`, { mode: 0o755 });
  const command = fileURLToPath(new URL('pin-source.py', import.meta.url));
  const invoke = (attempt) => spawnSync('python3', ['-B', command], { cwd: root, encoding: 'utf8', env: {
    ...process.env, PATH: join(root, 'bin') + ':' + process.env.PATH,
    GITHUB_RUN_ID: '7', GITHUB_RUN_ATTEMPT: attempt, GITHUB_REPOSITORY: 'owner/repo',
    RUNNER_TEMP: root, GITHUB_OUTPUT: join(root, 'outputs'),
  }});
  const first = invoke('1');
  assert.equal(first.status, 0, first.stderr);
  assert.equal(await readFile(join(root, 'outputs'), 'utf8'), 'source=' + tip + '\nupload=true\n');
  await rm(join(root, 'outputs'));
  // A retry can pin dev if the previous attempt failed before saving its pin.
  const retry = invoke('2');
  assert.equal(retry.status, 0, retry.stderr);
  assert.equal(await readFile(join(root, 'outputs'), 'utf8'), 'source=' + tip + '\nupload=true\n');
  await writeFile(join(root, 'pin-was-successful'), '');
  assert.equal(invoke('2').status, 1);
  await writeFile(join(root, 'pin-exists'), '');
  const resume = invoke('2');
  assert.equal(resume.status, 0, resume.stderr);
  assert.match(await readFile(join(root, 'outputs'), 'utf8'), new RegExp('source=' + earlier + '\\nupload=false\\n$'));
});

test('truth publication follows the completed release on protected dev and keeps its first pin', async t => {
  const { root, env } = await fixture(t);
  const pinned = 'b'.repeat(40);
  const marker = join(root, 'marker.json');
  const ref = 'refs/heads/lean-modules-published-report';
  const outputs = join(root, 'outputs');
  await writeFile(join(root, 'bin/gh'), `#!/bin/sh
case "$*" in
  *actions/runs/7/artifacts*) cat artifacts.json ;;
  *git/matching-refs/heads/lean-modules-published-report) cat marker.json ;;
  *branches/dev*) echo '{"protected":true,"commit":{"sha":"${pinned}"}}' ;;
  'run download 7 '*) echo '${pinned}' > pin/source ;;
  *) exit 2 ;;
esac
`, { mode: 0o755 });
  const command = fileURLToPath(new URL('pin-source.py', import.meta.url));
  const invoke = (name, attempt = '1') => spawnSync('python3', ['-B', command, '--published', 'report'], {
    cwd: root, encoding: 'utf8', env: { ...env, GITHUB_EVENT_NAME: name,
      GITHUB_RUN_ID: '7', GITHUB_RUN_ATTEMPT: attempt, GITHUB_OUTPUT: outputs },
  });
  await writeFile(join(root, 'artifacts.json'), '[{"artifacts":[]}]');
  await writeFile(marker, JSON.stringify([{ ref: ref + '-old', object: { sha: pinned } }]));
  const absent = invoke('schedule');
  assert.equal(absent.status, 0, absent.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=\nupload=false\n');
  await rm(outputs);
  await writeFile(marker, JSON.stringify([{ ref, object: { sha: pinned } }]));
  for (const name of ['schedule', 'workflow_run', 'workflow_dispatch']) {
    const result = invoke(name);
    assert.equal(result.status, 0, result.stderr);
    assert.equal(await readFile(outputs, 'utf8'), `source=${pinned}\nupload=true\n`);
    await rm(outputs);
  }
  await writeFile(marker, JSON.stringify([{ ref, object: { sha: 'bad-source' } }]));
  assert.match(invoke('schedule').stderr, /lowercase 40-hex string/);
  await rm(marker);
  await writeFile(join(root, 'artifacts.json'), '[{"artifacts":[{"name":"generation-pin-7","expired":false}]}]');
  const resume = invoke('schedule', '2');
  assert.equal(resume.status, 0, resume.stderr);
  assert.equal(await readFile(outputs, 'utf8'), `source=${pinned}\nupload=false\n`);
});

test('the report publisher pins the latest compatible compiler release and reuses its pin on retry', async t => {
  const { root, env } = await fixture(t);
  const first = 'a'.repeat(40);
  const latest = 'b'.repeat(40);
  const ref = 'refs/heads/lean-modules-published';
  const outputs = join(root, 'outputs');
  const json = (name, data) => writeFile(join(root, name), JSON.stringify(data));
  await writeFile(join(root, 'bin/gh'), `#!/bin/sh
set -eu
case "$*" in
  *actions/runs/*/artifacts*) cat artifacts.json ;;
  *git/matching-refs/heads/lean-modules-published) cat refs.json ;;
  *git/matching-refs/heads/lean-modules-published-report) cat report-refs.json ;;
  *branches/dev*) cat dev.json ;;
  *compare/${first}...${latest}*--jq*) echo '${first}' ;;
  *compare/${first}...${latest}*) echo '{"status":"ahead"}' ;;
  *compare/${latest}...${first}*) cat retry-comparison.json ;;
  'release download '*) test "$3" = "lean-modules-$(cat release-source)" && cp index.json "$9/index.json" ;;
  'run download '*) cp pinned-source pin/source ;;
  *) exit 2 ;;
esac
`, { mode: 0o755 });
  const command = fileURLToPath(new URL('pin-source.py', import.meta.url));
  const invoke = async (run = '7', attempt = '1', args = ['--published', 'compiler']) => {
    await rm(outputs, { force: true });
    return spawnSync('python3', ['-B', command, ...args], {
      cwd: root, encoding: 'utf8', env: { ...env, GITHUB_EVENT_NAME: 'workflow_run',
        GITHUB_RUN_ID: run, GITHUB_RUN_ATTEMPT: attempt, GITHUB_OUTPUT: outputs },
    });
  };
  const index = (source, fields) => ({
    source, version: 'lean-modules-' + source, schema: 'lean-module-shards-v1', ...fields,
  });
  const publish = async source => {
    await json('refs.json', [{ ref, object: { sha: source } }]);
    await json('dev.json', { protected: true, commit: { sha: source } });
    await writeFile(join(root, 'release-source'), source);
    await json('index.json', index(source, { kind: 'compiler' }));
  };
  await json('artifacts.json', [{ artifacts: [] }]);
  // GitHub's matching-refs endpoint can return only the sibling report marker.
  await json('refs.json', [{ ref: ref + '-report', object: { sha: first } }]);
  let result = await invoke();
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=\nupload=false\n');

  await publish(first);
  await json('index.json', index(first, {}));
  result = await invoke();
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=\nupload=false\n');
  for (const [fields, error] of [
    [{ kind: 'report' }, /expected a published compiler index/],
    [{ kind: 'compiler', schema: 'unexpected' }, /marker and index differ/],
    [{ kind: 'compiler', source: latest }, /marker and index differ/],
  ]) {
    await json('index.json', index(first, fields));
    const invalid = await invoke();
    assert.notEqual(invalid.status, 0);
    assert.match(invalid.stderr, error);
    await assert.rejects(readFile(outputs), { code: 'ENOENT' });
  }
  await publish(first);
  result = await invoke();
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=' + first + '\nupload=true\n');
  const skipReport = ['--published', 'compiler', '--skip-published', 'report'];
  await json('report-refs.json', []);
  result = await invoke('7', '1', skipReport);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=' + first + '\nupload=true\n');
  await json('report-refs.json', [{ ref: ref + '-report', object: { sha: first } }]);
  result = await invoke('7', '1', skipReport);
  assert.equal(result.status, 0, result.stderr);
  assert.match(await readFile(outputs, 'utf8'), /^already_published=true$/m);
  await writeFile(join(root, 'pinned-source'), await readFile(join(root, 'pin/source')));
  await publish(latest);
  result = await invoke('8');
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=' + latest + '\nupload=true\n');
  await json('artifacts.json', [{ artifacts: [{ name: 'generation-pin-7', expired: false }] }]);
  result = await invoke('8', '1', skipReport);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=' + latest + '\nupload=true\n');
  result = await invoke('8', '1', ['--skip-published', 'compiler']);
  assert.equal(result.status, 0, result.stderr);
  assert.match(await readFile(outputs, 'utf8'), /^already_published=true$/m);
  result = await invoke('7', '2');
  assert.equal(result.status, 0, result.stderr);
  assert.equal(await readFile(outputs, 'utf8'), 'source=' + first + '\nupload=false\n');
  await json('report-refs.json', [{ ref: ref + '-report', object: { sha: latest } }]);
  await json('retry-comparison.json', { status: 'behind' });
  for (const args of [skipReport, ['--skip-published', 'compiler']]) {
    result = await invoke('7', '2', args);
    assert.equal(result.status, 0, result.stderr);
    assert.equal(await readFile(outputs, 'utf8'), 'source=' + first + '\nupload=false\nsuperseded=true\n');
    assert.equal((await readFile(join(root, 'pin/source'), 'utf8')).trim(), first);
  }
  await json('retry-comparison.json', { status: 'diverged' });
  result = await invoke('7', '2', skipReport);
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /incompatible histories/);
  await assert.rejects(readFile(outputs), { code: 'ENOENT' });
});

test('the truth reader copies only named report ZIPs from an inherited split Release', async t => {
  const root = await mkdtemp(join(tmpdir(), 'published reports '));
  t.after(() => rm(root, { recursive: true, force: true }));
  const source = 'b'.repeat(40);
  const compiler = 'lean-modules-' + source;
  const tag = compiler + '-report';
  const inherited = 'lean-modules-' + 'a'.repeat(40) + '-report-part-2';
  const asset = 'old-D5.Example.tar.gz-report';
  await mkdir(join(root, tag));
  await mkdir(join(root, inherited));
  const pack = spawnSync('python3', ['-c', `
import io, sys, tarfile, zipfile
report = io.BytesIO()
with zipfile.ZipFile(report, 'w') as z:
    z.writestr('report.json', '{}')
with tarfile.open(sys.argv[1], 'w:gz') as archive:
    for name, data in {
        'lean-inspector/modules/D5.Example.zip': report.getvalue(),
        'lean-inspector/modules/D5.Example.zip.hash': b'hash',
        'lean-inspector/modules/D5.Example.zip.trace': b'trace',
        'lean-inspector/modules/D5.Other.zip': b'outside shard membership',
        'lib/lean/D5/Example.olean': b'compiler output',
        '../outside.zip': b'traversal',
    }.items():
        member = tarfile.TarInfo(name)
        member.size = len(data)
        archive.addfile(member, io.BytesIO(data))
`, join(root, inherited, asset)], { encoding: 'utf8' });
  assert.equal(pack.status, 0, pack.stderr);
  const contents = await readFile(join(root, inherited, asset));
  await writeFile(join(root, tag, 'index.json'), JSON.stringify({
    schema: 'lean-module-shards-v1', mathlib: 'fixture', kind: 'report', compiler_version: compiler,
    source, version: tag,
    targets: { 'D5.Example': { key: digest, report_inputs: [], shard: 'split' } },
    shards: { split: { version: inherited, asset, key: asset, artifact_kind: 'report',
      members: ['D5.Example'], sha256: createHash('sha256').update(contents).digest('hex'), bytes: contents.length } },
  }));
  const reader = fileURLToPath(new URL('../../scripts/read-module-reports.py', import.meta.url));
  const destination = join(root, '.lake/build/lean-inspector/modules');
  const read = spawnSync('python3', ['-B', reader, pathToFileURL(root).href, tag, destination], { encoding: 'utf8' });
  assert.equal(read.status, 0, read.stderr);
  const verify = spawnSync('python3', ['-c', 'import sys, zipfile; print(zipfile.ZipFile(sys.argv[1]).read("report.json").decode())',
    join(destination, 'D5.Example.zip')], { encoding: 'utf8' });
  assert.equal(verify.status, 0, verify.stderr);
  assert.equal(verify.stdout.trim(), '{}');
  assert.deepEqual(await readdir(destination), ['D5.Example.zip']);
  assert.deepEqual((await readdir(root)).sort(), ['.lake', inherited, tag].sort());
});

test('the same readable module key retrieves either version and readers cannot publish', async t => {
  const { root, requests, env } = await fixture(t);
  const key = 'v4.35.0-D5.S0.tar.gz';
  const entry = (event, operation, hash, path) => spawnSync(process.execPath, [action, operation, key, hash, path], {
    cwd: root, encoding: 'utf8', env: { ...env, GITHUB_EVENT_NAME: event },
  });
  const versions = new Map();
  for (const body of ['first archive', 'updated archive']) {
    const hash = createHash('sha256').update(body).digest('hex');
    versions.set(hash, body);
    await writeFile(join(root, 'shard.tar.gz'), body);
    const saved = entry('workflow_dispatch', 'module-put', hash, 'shard.tar.gz');
    assert.equal(saved.status, 0, saved.stderr);
    const repeated = entry('workflow_dispatch', 'module-put', hash, 'shard.tar.gz');
    assert.equal(repeated.status, 0, repeated.stderr);
  }
  env.GITHUB_WORKFLOW_REF = 'owner/repo/.github/workflows/ci-current.yml@refs/heads/dev';
  for (const [hash, body] of versions) {
    const lookup = entry('pull_request', 'module-get', hash, 'restored');
    assert.equal(lookup.status, 0, lookup.stderr);
    assert.equal(await readFile(join(root, 'restored'), 'utf8'), body);
    assert.equal(entry('push', 'module-put', hash, 'restored').status, 1);
  }
  assert.equal(entry('push', 'module-get', '0'.repeat(64), 'restored').status, 4);
  assert.equal((await requests()).split('\n').filter(line => line.startsWith('put ')).length, 2);
  const [hash] = versions.keys();
  await writeFile(join(root, key + '.' + hash), 'damaged');
  assert.equal(entry('push', 'module-get', hash, 'restored').status, 5);
});

test('the two protected publishers feed type-specific plans to their workers', async t => {
  const { root, env, run } = await fixture(t);
  const dir = join(root, 'tools/scripts/worktree');
  await mkdir(dir, { recursive: true });
  await writeFile(join(dir, 'lean_module_cache.py'), `
import argparse, os
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument("command")
for option in ["kind", "capacity", "workers", "output", "plan", "lane", "version", "targets-file"]:
    parser.add_argument("--" + option)
parser.add_argument("--prepare-release", action="store_true")
parser.add_argument("--stage-only", action="store_true")
parser.add_argument("--staged", action="store_true")
parser.add_argument("--legacy-checkpoints", action="store_true")
parser.add_argument("--compiler-dag", action="store_true")
args = parser.parse_args()
assert os.environ["LEAN_MODULE_ACTIONS_CACHE"] == "1"
kind = os.environ["INPUT_KIND"]
if args.command == "plan":
    assert args.kind == kind and args.prepare_release and int(args.capacity) == 32 * 1024**2
    assert args.compiler_dag == (kind == "compiler")
    assert args.workers == (os.environ.get("LEAN_COMPILER_WORKERS", "64") if kind == "compiler" else None)
    Path(args.output).write_text(kind)
elif args.command == "worker":
    assert Path(args.plan).read_text() == kind and args.lane == "2"
    Path("shard").write_text(kind)
elif args.command == "finish":
    assert args.stage_only
    assert Path(args.plan).read_text() == Path("shard").read_text() == kind
    Path(args.output).write_text(kind)
elif args.command == "promote":
    assert args.kind == kind and Path("module-index.json").read_text() == kind
    assert args.version == "lean-modules-" + "b" * 40 + ("-report" if kind == "report" else "")
elif args.command == "restore":
    assert args.staged == (os.environ.get("INPUT_STAGED") == "true")
    assert Path(args.targets_file).read_text() == "D5.A\\n"
    assert (args.kind or "") == kind
    if args.version is None or Path("missing-index").exists():
        raise SystemExit(3)
    assert args.version == "lean-modules-" + "b" * 40 + ("-report" if kind == "report" else "")
    Path("pinned-restore").write_text(args.version)
else:
    raise AssertionError(args.command)
`);
  env.SHARD_MIB = '32';
  env.MODULE_LANE = '2';
  const source = 'b'.repeat(40);
  await writeFile(join(root, 'target-list'), 'D5.A\n');
  env['INPUT_TARGETS-FILE'] = join(root, 'target-list');
  for (const [kind, workflow, event] of [
    ['compiler', 'cache-release-publish.yml', 'push'],
    ['report', 'report-release-publish.yml', 'workflow_run'],
  ]) {
    env.INPUT_KIND = kind;
    env.GITHUB_WORKFLOW_REF = 'owner/repo/.github/workflows/' + workflow + '@refs/heads/dev';
    if (kind === 'compiler') {
      delete env.LEAN_COMPILER_WORKERS;
      const defaultPlan = run(event, 'module-plan');
      assert.equal(defaultPlan.status, 0, defaultPlan.stderr);
      for (const invalid of ['0', '257', '8.5', 'unlimited']) {
        env.LEAN_COMPILER_WORKERS = invalid;
        assert.match(run(event, 'module-plan').stderr, /between 1 and 256/);
      }
      env.LEAN_COMPILER_WORKERS = '256';
    }
    for (const operation of ['module-plan', 'module-worker', 'module-stage']) {
      const result = run(event, operation);
      assert.equal(result.status, 0, result.stderr);
    }
    assert.equal(await readFile(join(root, 'module-index.json'), 'utf8'), kind);
    assert.equal(run('pull_request', 'module-plan').status, 1);
    env.INPUT_KIND = kind === 'compiler' ? 'report' : 'compiler';
    assert.equal(run('schedule', 'module-plan').status, 1);
    env.INPUT_KIND = kind;
    env.INPUT_VERSION = 'lean-modules-' + source + (kind === 'report' ? '-report' : '');
    env.INPUT_STAGED = 'true';
    const staged = run('workflow_run', 'restore-published');
    assert.equal(staged.status, 0, staged.stderr);
    delete env.INPUT_STAGED;
    const promoted = run(event, 'module-promote');
    assert.equal(promoted.status, 0, promoted.stderr);
    assert.notEqual(run('pull_request', 'module-promote').status, 0);
    const pinned = run('pull_request', 'restore-published');
    assert.equal(pinned.status, 0, pinned.stderr);
    assert.equal(await readFile(join(root, 'pinned-restore'), 'utf8'), env.INPUT_VERSION);
    await writeFile(join(root, 'missing-index'), '');
    assert.notEqual(run('pull_request', 'restore-published').status, 0);
    await rm(join(root, 'missing-index'));
  }
  env.INPUT_KIND = '';
  delete env.INPUT_VERSION;
  const empty = run('push', 'restore-published');
  assert.equal(empty.status, 0, empty.stderr);
  assert.match(empty.stdout, /No published module cache yet/);
});
