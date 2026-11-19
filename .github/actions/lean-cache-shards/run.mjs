import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, readdir, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { dirname, join, resolve } from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const stage = 'build/lean-cache/shards';
const indexPath = join(stage, 'index.json');
const operation = process.argv[2] || process.env.INPUT_OPERATION;
const state = process.env.INPUT_STATE || 'complete';
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const anchor = process.env.INPUT_ANCHOR;
const requireComplete = process.env['INPUT_REQUIRE-COMPLETE'] === 'true';
const shardedAdoption = process.env['INPUT_SHARDED-ADOPTION'] === 'true';
// A nested JavaScript action may inherit the enclosing composite's action path.
const actionPath = dirname(fileURLToPath(import.meta.url));
const targetArgs = targets.flatMap(target => ['--target', target]);
const pythonTool = 'tools/scripts/worktree/lean_actions_shards.py';
const preparationTool = 'tools/scripts/worktree/lean_pr_cache.py';

function preparationCommand(command, args) {
  execFileSync('python3', ['-B', preparationTool, command, '--repository', workspace, ...args], { stdio: 'inherit' });
}

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

function waitForCacheQuota() {
  return delay(60000 + Math.floor(Math.random() * 10000));
}

async function fetchIndex(cache, cacheVersion, identity, protectedOnly = false) {
  const ref = process.env.GITHUB_BASE_REF ? 'refs/heads/' + process.env.GITHUB_BASE_REF : identity.owner.ref;
  const refs = state === 'resume' || protectedOnly ? [ref] : [...new Set([ref, 'refs/heads/dev'])];
  await rm(indexPath, { force: true });
  let retry;
  const restoreExactIndex = async row => {
    const matched = await cache.restoreCache([indexPath], row.key, []);
    if (matched !== row.key) return;
    const record = JSON.parse(await readFile(indexPath, 'utf8'));
    matchIndex(identity, matched, record);
    if (record.owner.ref !== row.ref) throw new Error('Actions index owner ref mismatch');
    return matched;
  };
  for (const candidateRef of refs.filter(value => /^refs\/heads\/(dev|integration-[A-Za-z0-9._/-]+)$/.test(value))) {
    const prefix = identity.prefix + 'snapshot-';
    const rows = optionalInventory(candidateRef, prefix)
      .filter(row => row.key.startsWith(prefix) && /^[1-9][0-9]*-[1-9][0-9]*$/.test(row.key.slice(prefix.length))
        && row.version === cacheVersion(indexPath))
      .sort((left, right) => right.key.localeCompare(left.key, 'en', { numeric: true }));
    retry ||= rows[0];
    for (const row of rows.slice(0, 3)) {
      const matched = await restoreExactIndex(row);
      if (matched) return matched;
    }
  }
  if (retry) {
    await waitForCacheQuota();
    return restoreExactIndex(retry);
  }
}

async function restorePayloads(cache, cacheVersion, identity, index, preparation) {
  const started = performance.now();
  const needed = python('restore-plan', ['--index', index, ...targetArgs]);
  const digests = [...new Set(Object.values(needed))];
  const bundled = new Set(preparation
    ? await readdir(join(preparation, 'shards')).catch(error => {
      if (error.code === 'ENOENT') return [];
      throw error;
    })
    : []);
  let transferred = 0;
  const remote = digests.filter(digest => !bundled.has(digest + '.tar.gz'));
  const downloaded = new Set();
  const download = async digest => {
    const path = payloadPath(digest);
    await rm(path, { force: true });
    try {
      const key = payloadKey(identity, digest);
      if (await cache.restoreCache([path], key, []) === key) {
        const { size } = await stat(path);
        transferred += size;
        downloaded.add(digest);
      }
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS restore failed for ' + digest + ': ' + error.message);
    }
  };
  let pending = remote;
  let retries = 0;
  for (const rate of [600, 300, 150]) {
    if (pending.length === 0) break;
    if (retries > 0) {
      console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
        operation: 'retry-download', attempt: retries, requested: pending.length, perMinute: rate,
      }));
      await waitForCacheQuota();
    }
    await paced(pending, 24, rate, download);
    pending = pending.filter(digest => !downloaded.has(digest));
    if (pending.length === 0 || retries === 2) break;
    if (retries === 0) {
      const { owner } = JSON.parse(await readFile(index, 'utf8'));
      const material = optionalInventory(owner.ref, identity.prefix + 'material-');
      const visible = new Set(material.map(row => row.key + '/' + row.version));
      pending = pending.filter(digest => visible.has(payloadKey(identity, digest) + '/' + cacheVersion(payloadPath(digest))));
    }
    retries += 1;
  }
  const installArgs = ['--index', index, ...targetArgs];
  if (preparation) installArgs.push('--preparation', preparation);
  if (requireComplete || preparation) installArgs.push('--require-complete');
  const result = python('install', installArgs);
  await Promise.all(remote.map(digest => rm(payloadPath(digest), { force: true })));
  console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
    operation, requested: digests.length, remote: remote.length, downloaded: downloaded.size,
    restored: result.available, missing: result.missing.length,
    bytes: transferred, seconds: (performance.now() - started) / 1000,
  }));
  return result;
}

async function restore(cache, cacheVersion, identity) {
  const matched = await fetchIndex(cache, cacheVersion, identity);
  if (!matched) {
    console.log('LEAN_ACTIONS_SHARDS no compatible index was found');
    return;
  }
  const result = await restorePayloads(cache, cacheVersion, identity, indexPath);
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

function optionalInventory(ref, prefix) {
  try {
    return visibleEntries(ref, prefix);
  } catch (error) {
    console.log('LEAN_ACTIONS_SHARDS inventory unavailable for ' + ref + ': ' + error.message);
    return [];
  }
}

function matches(entries, key, version) {
  return entries.some(row => row.key === key && row.version === version);
}

async function packPreparation(directory) {
  if (!anchor) throw new Error('sharded preparation requires a pinned history anchor');
  const args = ['--directory', directory, '--anchor', anchor];
  try {
    const { cache, cacheVersion } = await loadCacheClient();
    if (await fetchIndex(cache, cacheVersion, python('identity'), true)) {
      args.push('--previous-index', indexPath);
    }
  } catch (error) {
    console.log('LEAN_ACTIONS_SHARDS prior layout unavailable: ' + error.message);
  }
  preparationCommand('pack', args);
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

  if (!previous && process.env['INPUT_REQUIRE-EXISTING-INDEX'] === 'true') {
    throw new Error('indexed publication requires the previous layout; the long producer can bootstrap');
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
  const upload = async (digest, inventory) => {
    const path = payloadPath(digest);
    const key = payloadKey(identity, digest);
    try {
      if (!matches(inventory, key, cacheVersion(path)) && await cache.saveCache([path], key) >= 0) {
        confirmed.add(digest);
        return;
      }
      // The cache version uses the original path. Preserve the packed bytes
      // while checking the remote entry so a failed check can be retried.
      const original = path + '.upload';
      await rename(path, original);
      try {
        if (await cache.restoreCache([path], key, []) === key && await digestFile(path) === digest) {
          confirmed.add(digest);
        }
      } finally {
        await rename(original, path);
      }
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS save failed for ' + digest + ': ' + error.message);
    }
  };
  const reconcile = () => {
    const rows = visibleEntries(ownerRef, prefix);
    const visible = new Set(rows.map(row => row.key + '/' + row.version));
    for (const digest of confirmed) {
      if (!visible.has(payloadKey(identity, digest) + '/' + cacheVersion(payloadPath(digest)))) confirmed.delete(digest);
    }
    return rows;
  };
  // GitHub allows 200 uploads per repository per minute. Leave room for
  // another producer and the repository's ordinary cache writes.
  await paced(pending, 8, 85, digest => upload(digest, before));
  reconcile();
  if (pending.some(digest => !confirmed.has(digest))) {
    await waitForCacheQuota();
    const inventory = reconcile();
    const retry = pending.filter(digest => !confirmed.has(digest));
    console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
      operation: 'retry-upload', requested: retry.length, perMinute: 50,
    }));
    await paced(retry, 8, 50, digest => upload(digest, inventory));
    reconcile();
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

async function main() {
  if (operation === 'adopt-preparation') {
    const args = shardedAdoption ? ['--cache-action', process.execPath, fileURLToPath(import.meta.url)] : [];
    preparationCommand('adopt', args);
    return;
  }
  if (operation === 'pack-preparation') {
    await packPreparation(join(process.env.RUNNER_TEMP, 'pr-preparation'));
    return;
  }
  if (operation === 'restore-preparation') {
    const directory = process.argv[3];
    const { cache, cacheVersion } = await loadCacheClient();
    const result = await restorePayloads(cache, cacheVersion, python('identity'), join(directory, 'project.json'), directory);
    if (!result.complete) process.exitCode = 3;
    return;
  }
  if (!['save', 'restore'].includes(operation) || !['complete', 'resume'].includes(state)) {
    throw new Error('invalid Actions shard operation or state');
  }
  if (operation === 'save' && !anchor) throw new Error('Actions cache writes require a pinned history anchor');
  const { cache, cacheVersion } = await loadCacheClient();
  const identity = python('identity');
  await mkdir(stage, { recursive: true });
  if (operation === 'save') await save(cache, cacheVersion, identity);
  else await restore(cache, cacheVersion, identity);
}

try {
  await main();
} catch (error) {
  process.exitCode = 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
