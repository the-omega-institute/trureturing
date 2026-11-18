import { execFileSync } from 'node:child_process';
import { copyFile, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { join, resolve } from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import { pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const stage = 'build/lean-cache/shards';
const indexPath = join(stage, 'index.json');
const operation = process.env.INPUT_OPERATION;
const state = process.env.INPUT_STATE || 'complete';
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const anchor = process.env.INPUT_ANCHOR;
const requireComplete = process.env['INPUT_REQUIRE-COMPLETE'] === 'true';
const actionPath = process.env.GITHUB_ACTION_PATH || new URL('.', import.meta.url).pathname;
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
  return import(pathToFileURL(join(install, 'node_modules/@actions/cache/lib/cache.js')).href);
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

async function restore(cache, identity) {
  await rm(indexPath, { force: true });
  const matched = await cache.restoreCache([indexPath], indexKey(identity), [identity.prefix + 'snapshot-']);
  if (!matched) {
    console.log('LEAN_ACTIONS_SHARDS no compatible index was found');
    return;
  }
  const needed = python('restore-plan', ['--index', indexPath, ...targetArgs]);
  matchIndex(identity, matched, JSON.parse(await readFile(indexPath, 'utf8')));
  const digests = [...new Set(Object.values(needed))];
  await paced(digests, 24, 1200, async digest => {
    const path = payloadPath(digest);
    await rm(path, { force: true });
    try {
      await cache.restoreCache([path], payloadKey(identity, digest), [], {});
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS restore failed for ' + digest + ': ' + error.message);
    }
  });
  const installArgs = ['--index', indexPath, ...targetArgs];
  if (requireComplete) installArgs.push('--require-complete');
  const result = python('install', installArgs);
  await Promise.all(digests.map(digest => rm(payloadPath(digest), { force: true })));
  await setOutputs({ key: matched, available: result.available, missing: result.missing.length,
    complete: result.complete });
}

function visibleMaterial(identity) {
  const repository = process.env.GITHUB_REPOSITORY;
  const ref = identity.owner.ref;
  if (!process.env.GH_TOKEN || !repository) return new Set();
  const prefix = identity.prefix + 'material-';
  try {
    const listing = execFileSync('gh', [
      'api', '--paginate', '--method', 'GET', 'repos/' + repository + '/actions/caches',
      '-f', 'ref=' + ref, '-f', 'per_page=100', '-f', 'key=' + prefix, '--jq', '.actions_caches[].key',
    ], { encoding: 'utf8', timeout: 90000, stdio: ['ignore', 'pipe', 'pipe'] });
    return new Set(listing.split('\n').filter(key => key.startsWith(prefix)));
  } catch (error) {
    console.log('LEAN_ACTIONS_SHARDS cache inventory unavailable: ' + error.message.split('\n')[0]);
    return new Set();
  }
}

async function save(cache, identity) {
  const known = visibleMaterial(identity);
  await rm(indexPath, { force: true });
  const previous = await cache.restoreCache([indexPath], indexKey(identity), [identity.prefix + 'snapshot-']);
  const extra = ['--anchor', anchor, ...targetArgs];
  if (previous) {
    const record = JSON.parse(await readFile(indexPath, 'utf8'));
    matchIndex(identity, previous, record);
    const available = join(stage, 'visible-material.json');
    await writeFile(available, JSON.stringify(
      Object.values(record.entries).filter(digest => known.has(payloadKey(identity, digest))),
    ));
    extra.push('--index', indexPath, '--available', available);
  }
  const record = python('prepare', extra);
  const digests = [...new Set(Object.values(record.entries))];
  const confirmed = new Set(digests.filter(digest => known.has(payloadKey(identity, digest))));
  const pending = digests.filter(digest => !confirmed.has(digest));
  await paced(pending, 8, 170, async digest => {
    const path = payloadPath(digest);
    const key = payloadKey(identity, digest);
    try {
      if (await cache.restoreCache([path], key, [], { lookupOnly: true }) === key
          || await cache.saveCache([path], key) >= 0) {
        confirmed.add(digest);
        return;
      }
      // A concurrent upload can reserve the same immutable content.
      if (await cache.restoreCache([path], key, [], { lookupOnly: true }) === key) confirmed.add(digest);
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS save failed for ' + digest + ': ' + error.message);
    }
  });
  const missing = digests.length - confirmed.size;
  if (state === 'complete' && missing) throw new Error('complete cache index is missing ' + missing + ' shards');
  record.entries = Object.fromEntries(Object.entries(record.entries).filter(([, digest]) => confirmed.has(digest)));
  record.fingerprints = Object.fromEntries(
    Object.entries(record.fingerprints).filter(([id]) => id in record.entries),
  );
  await writeFile(indexPath, JSON.stringify(record) + '\n');
  const key = indexKey(identity);
  if (await cache.saveCache([indexPath], key) < 0
      && await cache.restoreCache([indexPath], key, [], { lookupOnly: true }) !== key) {
    throw new Error('Actions did not publish the shard index');
  }
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
  const cache = await loadCacheClient();
  const identity = python('identity');
  await mkdir(stage, { recursive: true });
  if (operation === 'save') await save(cache, identity);
  else await restore(cache, identity);
} catch (error) {
  process.exitCode = 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
