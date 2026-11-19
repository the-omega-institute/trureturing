import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, readFile, rm, stat, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { dirname, join, resolve } from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const stage = 'build/lean-cache/shards';
const indexPath = join(stage, 'index.json');
const operation = process.env.INPUT_OPERATION;
const state = process.env.INPUT_STATE || 'complete';
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const anchor = process.env.INPUT_ANCHOR;
const requireComplete = process.env['INPUT_REQUIRE-COMPLETE'] === 'true';
// A nested JavaScript action may inherit the enclosing composite's action path.
const actionPath = dirname(fileURLToPath(import.meta.url));
const targetArgs = targets.flatMap(target => ['--target', target]);
const pythonTool = 'tools/scripts/worktree/lean_actions_shards.py';

function python(command, extra = []) {
  const output = execFileSync('python3', ['-B', pythonTool, command, '--state', state, ...extra], {
    encoding: 'utf8',
    maxBuffer: 40 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'inherit'],
  }).trimEnd().split('\n');
  for (const line of output.slice(0, -1)) console.log(line);
  return JSON.parse(output.at(-1));
}

async function loadCacheClient() {
  const install = resolve(stage, 'client');
  await mkdir(install, { recursive: true });
  for (const file of ['package.json', 'package-lock.json']) {
    await copyFile(join(actionPath, file), join(install, file));
  }
  const env = { PATH: process.env.PATH, HOME: process.env.HOME };
  execFileSync('npm', ['ci', '--ignore-scripts', '--omit=dev', '--no-audit', '--no-fund'], {
    cwd: install, env, stdio: 'inherit', timeout: 120000,
  });
  const library = join(install, 'node_modules/@actions/cache/lib');
  const cache = await import(pathToFileURL(join(library, 'cache.js')).href);
  const utils = await import(pathToFileURL(join(library, 'internal/cacheUtils.js')).href);
  const compression = await utils.getCompressionMethod();
  return { cache, cacheVersion: path => utils.getCacheVersion([path], compression) };
}

function payloadPath(digest) {
  if (!/^[0-9a-f]{64}$/.test(digest)) throw new Error('invalid shard payload address');
  return join(stage, 'payload', digest + '.tar.gz');
}

function payloadKey(identity, digest) {
  return identity.prefix + 'material-' + digest;
}

function indexKey(identity) {
  const { run, attempt } = identity.owner;
  return identity.prefix + 'snapshot-' + run + '-' + attempt;
}

function matchIndex(identity, matched, record) {
  const expected = identity.prefix + 'snapshot-' + record.owner.run + '-' + record.owner.attempt;
  if (matched !== expected) throw new Error('Actions index did not match the producing run');
}

async function paced(items, parallelism, perMinute, invoke) {
  const interval = 60000 / perMinute;
  let nextPermit = performance.now();
  let position = 0;
  await Promise.all(Array.from({ length: Math.min(items.length, parallelism) }, async () => {
    while (position < items.length) {
      const item = items[position++];
      const now = performance.now();
      const scheduled = Math.max(now, nextPermit);
      nextPermit = scheduled + interval;
      if (scheduled > now) await delay(scheduled - now);
      await invoke(item);
    }
  }));
}

async function fetchIndex(cache, cacheVersion, identity) {
  const ref = process.env.GITHUB_BASE_REF ? 'refs/heads/' + process.env.GITHUB_BASE_REF : identity.owner.ref;
  const refs = state === 'resume' ? [ref] : [...new Set([ref, 'refs/heads/dev'])];
  await rm(indexPath, { force: true });
  for (const candidateRef of refs.filter(value => /^refs\/heads\/(dev|integration-[A-Za-z0-9._/-]+)$/.test(value))) {
    const prefix = identity.prefix + 'snapshot-';
    const rows = visibleEntries(candidateRef, prefix)
      .filter(row => row.key.startsWith(prefix) && /^[1-9][0-9]*-[1-9][0-9]*$/.test(row.key.slice(prefix.length))
        && row.version === cacheVersion(indexPath))
      .sort((left, right) => right.key.localeCompare(left.key, 'en', { numeric: true }));
    for (const row of rows.slice(0, 3)) {
      const matched = await cache.restoreCache([indexPath], row.key, []);
      if (matched !== row.key) continue;
      const record = JSON.parse(await readFile(indexPath, 'utf8'));
      matchIndex(identity, matched, record);
      if (record.owner.ref !== candidateRef) throw new Error('Actions index owner ref mismatch');
      return matched;
    }
  }
}

async function restore(cache, cacheVersion, identity) {
  const started = performance.now();
  const matched = await fetchIndex(cache, cacheVersion, identity);
  if (!matched) {
    console.log('LEAN_ACTIONS_SHARDS no compatible index was found');
    return;
  }
  const needed = python('restore-plan', ['--index', indexPath, ...targetArgs]);
  const digests = [...new Set(Object.values(needed))];
  let transferred = 0;
  await paced(digests, 24, 1200, async digest => {
    const path = payloadPath(digest);
    await rm(path, { force: true });
    try {
      const key = payloadKey(identity, digest);
      if (await cache.restoreCache([path], key, []) === key) {
        const { size } = await stat(path);
        transferred += size;
      }
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS restore failed for ' + digest + ': ' + error.message);
    }
  });
  const installArgs = ['--index', indexPath, ...targetArgs];
  if (requireComplete) installArgs.push('--require-complete');
  const result = python('install', installArgs);
  await Promise.all(digests.map(digest => rm(payloadPath(digest), { force: true })));
  console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
    operation: 'restore', requested: digests.length, restored: result.available,
    bytes: transferred, seconds: (performance.now() - started) / 1000,
  }));
  await setOutputs({ key: matched, available: result.available, missing: result.missing.length,
    complete: result.complete });
}

function visibleEntries(ref, prefix) {
  const repository = process.env.GITHUB_REPOSITORY;
  if (!process.env.GH_TOKEN || !repository) throw new Error('Actions cache inventory credentials are missing');
  const listing = execFileSync('gh', [
    'api', '--paginate', '--method', 'GET', 'repos/' + repository + '/actions/caches',
    '-f', 'ref=' + ref, '-f', 'per_page=100', '-f', 'key=' + prefix, '--jq', '.actions_caches[] | {key, ref, version}',
  ], { encoding: 'utf8', timeout: 90000, maxBuffer: 4 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  return listing.trim().split('\n').filter(Boolean).map(line => JSON.parse(line)).filter(row => row.ref === ref);
}

function matches(entries, key, version) {
  return entries.some(row => row.key === key && row.version === version);
}

async function digestFile(path) {
  const hash = createHash('sha256');
  for await (const chunk of createReadStream(path)) hash.update(chunk);
  return hash.digest('hex');
}

async function save(cache, cacheVersion, identity) {
  const started = performance.now();
  const prefix = identity.prefix + 'material-';
  const ownerRef = identity.owner.ref;
  const before = visibleEntries(ownerRef, identity.prefix);
  const savedIndex = before.filter(row => row.key.startsWith(identity.prefix + 'snapshot-')
    && row.version === cacheVersion(indexPath)).sort((left, right) =>
      right.key.localeCompare(left.key, 'en', { numeric: true }))[0];
  await rm(indexPath, { force: true });
  const extra = ['--anchor', anchor, ...targetArgs];
  const known = new Set();
  let previous;
  if (savedIndex && await cache.restoreCache([indexPath], savedIndex.key, []) === savedIndex.key) {
    const record = JSON.parse(await readFile(indexPath, 'utf8'));
    matchIndex(identity, savedIndex.key, record);
    previous = record;
    if (record.owner.ref !== ownerRef) throw new Error('Actions index owner ref mismatch');
    for (const digest of Object.values(record.entries)) {
      if (matches(before, payloadKey(identity, digest), cacheVersion(payloadPath(digest)))) known.add(digest);
    }
    const available = join(stage, 'visible-material.json');
    await writeFile(available, JSON.stringify([...known]));
    extra.push('--index', indexPath, '--available', available);
  }

  const record = python('prepare', extra);
  const digests = [...new Set(Object.values(record.entries))];
  const confirmed = new Set(digests.filter(digest => known.has(digest)));
  const pending = digests.filter(digest => !confirmed.has(digest));
  if (state === 'complete' && previous && pending.length === 0
      && Object.keys(previous.entries).length === Object.keys(record.entries).length
      && Object.entries(record.entries).every(([key, digest]) => previous.entries[key] === digest)) {
    console.log('LEAN_ACTIONS_SHARDS reuse current verified material');
    await setOutputs({ key: savedIndex.key, available: confirmed.size, missing: 0, complete: true });
    return;
  }
  await paced(pending, 8, 170, async digest => {
    const path = payloadPath(digest);
    const key = payloadKey(identity, digest);
    try {
      if (!matches(before, key, cacheVersion(path)) && await cache.saveCache([path], key) >= 0) {
        confirmed.add(digest);
        return;
      }
      // A collision is accepted only when the stored bytes match the key.
      await rm(path, { force: true });
      if (await cache.restoreCache([path], key, []) === key && await digestFile(path) === digest) {
        confirmed.add(digest);
      }
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS save failed for ' + digest + ': ' + error.message);
    }
  });
  const after = visibleEntries(ownerRef, prefix);
  const visible = new Set(after.map(row => row.key + '/' + row.version));
  for (const digest of confirmed) {
    if (!visible.has(payloadKey(identity, digest) + '/' + cacheVersion(payloadPath(digest)))) confirmed.delete(digest);
  }
  const missing = digests.length - confirmed.size;
  if (state === 'complete' && missing) throw new Error('complete cache index is missing ' + missing + ' shards');
  if (!confirmed.size) throw new Error('no shard was confirmed on its producer ref');
  record.entries = Object.fromEntries(Object.entries(record.entries).filter(([, digest]) => confirmed.has(digest)));
  record.fingerprints = Object.fromEntries(
    Object.entries(record.fingerprints).filter(([id]) => id in record.entries),
  );
  const encoded = JSON.stringify(record) + '\n';
  await writeFile(indexPath, encoded);
  const key = indexKey(identity);
  if (await cache.saveCache([indexPath], key) < 0
      && (!matches(visibleEntries(ownerRef, key), key, cacheVersion(indexPath))
        || await cache.restoreCache([indexPath], key, []) !== key
        || await readFile(indexPath, 'utf8') !== encoded)) {
    throw new Error('Actions did not publish the intended shard index');
  }
  if (!matches(visibleEntries(ownerRef, key), key, cacheVersion(indexPath))) {
    throw new Error('Actions index is not visible on its producer ref');
  }
  console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
    operation: 'save', requested: digests.length, previous: digests.length - pending.length,
    confirmed: confirmed.size, seconds: (performance.now() - started) / 1000,
  }));
  await setOutputs({ key, available: confirmed.size, missing, complete: state === 'complete' });
}

async function setOutputs(fields) {
  const lines = Object.entries(fields).map(([key, value]) => key + '=' + value).join('\n') + '\n';
  await writeFile(process.env.GITHUB_OUTPUT, lines, { flag: 'a' });
}

try {
  if (!['save', 'restore'].includes(operation) || !['complete', 'resume'].includes(state)) {
    throw new Error('invalid Actions shard operation or state');
  }
  if (operation === 'save' && !anchor) throw new Error('Actions cache writes require a pinned history anchor');
  const { cache, cacheVersion } = await loadCacheClient();
  const identity = python('identity');
  await mkdir(stage, { recursive: true });
  if (operation === 'save') await save(cache, cacheVersion, identity);
  else await restore(cache, cacheVersion, identity);
} catch (error) {
  process.exitCode = 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
