import { execFileSync, spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { once } from 'node:events';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, mkdtemp, readdir, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline';
import { setTimeout as delay } from 'node:timers/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const stage = 'build/lean-cache/shards';
const operation = process.argv[2] || process.env.INPUT_OPERATION;
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const targetsFile = process.env['INPUT_TARGETS-FILE'];
// A nested JavaScript action may inherit the enclosing composite's action path.
const actionPath = dirname(fileURLToPath(import.meta.url));
const pythonTool = 'tools/scripts/worktree/lean_actions_shards.py';

function python(command, extra = []) {
  const output = execFileSync('python3', ['-B', pythonTool, command, '--state', 'complete', ...extra], {
    encoding: 'utf8',
    maxBuffer: 40 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'inherit'],
  }).trimEnd().split('\n');
  for (const line of output.slice(0, -1)) console.log(line);
  return JSON.parse(output.at(-1));
}

async function loadCacheClient() {
  const manifests = ['package.json', 'package-lock.json'];
  const hash = createHash('sha256').update([process.version, process.platform, process.arch].join('/'));
  for (const manifest of manifests) hash.update('\0').update(await readFile(join(actionPath, manifest)));
  const parent = join(process.env.RUNNER_TEMP, 'lean-actions-sdk');
  const install = join(parent, hash.digest('hex'));
  await mkdir(parent, { recursive: true });
  try {
    await stat(install);
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
    const temporary = await mkdtemp(join(parent, 'install-'));
    try {
      for (const file of manifests) await copyFile(join(actionPath, file), join(temporary, file));
      execFileSync('npm', ['ci', '--ignore-scripts', '--omit=dev', '--no-audit', '--no-fund'], {
        cwd: temporary, env: { PATH: process.env.PATH, HOME: process.env.HOME }, stdio: 'inherit', timeout: 120000,
      });
      // A completed installation becomes visible in a single rename. Other
      // processes can only observe an intact tree from the same package lock.
      try {
        await rename(temporary, install);
      } catch (error) {
        if (!['EEXIST', 'ENOTEMPTY'].includes(error.code)) throw error;
      }
    } finally {
      await rm(temporary, { recursive: true, force: true });
    }
  }
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

function payloadKey(prefix, digest) {
  return prefix + 'material-' + digest;
}

async function paced(items, parallelism, perMinute, invoke) {
  const interval = 60000 / perMinute;
  let next = performance.now();
  let position = 0;
  let failure;
  await Promise.all(Array.from({ length: Math.min(items.length, parallelism) }, async () => {
    while (!failure && position < items.length) {
      const item = items[position++];
      const now = performance.now();
      const scheduled = Math.max(now, next);
      next = scheduled + interval;
      if (scheduled > now) await delay(scheduled - now);
      if (failure) return;
      try {
        await invoke(item);
      } catch (error) {
        failure ??= error;
      }
    }
  }));
  if (failure) throw failure;
}

function waitForCacheQuota() {
  return delay(60000 + Math.floor(Math.random() * 10000));
}

async function visibleMaterial(prefix, index, cacheVersion) {
  const { owner } = JSON.parse(await readFile(index, 'utf8'));
  const visible = new Set(optionalInventory(owner.ref, prefix + 'material-').map(row => row.key + '/' + row.version));
  return digest => visible.has(payloadKey(prefix, digest) + '/' + cacheVersion(payloadPath(digest)));
}

async function restorePreparation(preparation) {
  const { cache, cacheVersion } = await loadCacheClient();
  const { prefix } = python('identity');
  const index = join(preparation, 'project.json');
  const started = performance.now();
  const needed = python('restore-plan', ['--index', index]);
  const digests = [...new Set(Object.values(needed))];
  const bundled = new Set(await readdir(join(preparation, 'shards')).catch(error => {
    if (error.code === 'ENOENT') return [];
    throw error;
  }));
  let transferred = 0;
  const remote = digests.filter(digest => !bundled.has(digest + '.tar.gz'));
  const downloaded = new Set();
  const download = async digest => {
    const path = payloadPath(digest);
    try {
      await rm(path, { force: true });
      const key = payloadKey(prefix, digest);
      if (await cache.restoreCache([path], key, []) === key) {
        const { size } = await stat(path);
        transferred += size;
        downloaded.add(digest);
      }
    } catch (error) {
      console.log('LEAN_ACTIONS_SHARDS restore failed for ' + digest + ': ' + error.message);
    }
  };
  try {
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
        pending = pending.filter(await visibleMaterial(prefix, index, cacheVersion));
      }
      retries += 1;
    }
    const result = python('install', ['--index', index, '--preparation', preparation, '--require-complete']);
    console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
      operation, requested: digests.length, remote: remote.length, downloaded: downloaded.size,
      restored: result.available, missing: result.missing.length,
      bytes: transferred, seconds: (performance.now() - started) / 1000,
    }));
    if (!result.complete) process.exitCode = 3;
  } finally {
    await Promise.all(remote.map(digest => rm(payloadPath(digest), { force: true })));
  }
}

function visibleEntries(ref, prefix) {
  const repository = process.env.GITHUB_REPOSITORY;
  if (!process.env.GH_TOKEN || !repository) throw new Error('Actions cache inventory credentials are missing');
  const listing = execFileSync('gh', [
    'api', '--paginate', '--method', 'GET', 'repos/' + repository + '/actions/caches',
    '-f', 'ref=' + ref, '-f', 'per_page=100', '-f', 'key=' + prefix, '--jq', '.actions_caches[] | {key, ref, version, created_at}',
  ], { encoding: 'utf8', timeout: 300000, maxBuffer: 64 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
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

async function digestFile(path) {
  const hash = createHash('sha256');
  for await (const chunk of createReadStream(path)) hash.update(chunk);
  return hash.digest('hex');
}

function requirePublisher() {
  const env = process.env;
  if (!['schedule', 'workflow_dispatch'].includes(env.GITHUB_EVENT_NAME)
      || env.GITHUB_REF !== 'refs/heads/dev' || env.GITHUB_REF_PROTECTED !== 'true'
      || env.STRATALINT_CACHE_WRITES !== 'true'
      || env.GITHUB_WORKFLOW_REF !== env.GITHUB_REPOSITORY + '/.github/workflows/cache-release-publish.yml@refs/heads/dev') {
    throw new Error('shared cache writes require the protected dev Release publisher');
  }
}

async function generationIndex(digest, file) {
  if (!/^[0-9a-f]{64}$/.test(digest) || !file) throw new Error('invalid generation index arguments');
  const put = operation === 'generation-put';
  if (put) {
    requirePublisher();
    if (await digestFile(file) !== digest) throw new Error('generation index digest mismatch');
  }
  // The Actions cache version includes the literal path. Every run and both
  // operations must use this workspace-relative name, regardless of caller.
  const path = 'build/lean-cache/generation/index.json';
  const key = 'lean-generation-v1-' + digest;
  const { cache } = await loadCacheClient();
  await mkdir(dirname(path), { recursive: true });
  if (put && await cache.restoreCache([path], key, [], { lookupOnly: true }) !== key) {
    if (resolve(file) !== resolve(path)) await copyFile(file, path);
    await cache.saveCache([path], key);
  }
  await rm(path, { force: true });
  if (await cache.restoreCache([path], key, []) !== key) {
    if (!put) process.exitCode = 4;
    throw new Error('missing Actions generation index ' + digest);
  }
  if (await digestFile(path) !== digest) {
    if (!put) process.exitCode = 5;
    throw new Error('corrupt Actions generation index ' + digest);
  }
  if (!put && resolve(file) !== resolve(path)) await copyFile(path, file);
}

async function moduleCacheEntry(key, digest, file) {
  const put = operation === 'module-put';
  if (put) requirePublisher();
  if (!key || key.length > 512 || /[,\r\n]/.test(key) || !/^[0-9a-f]{64}$/.test(digest) || !file) {
    throw new Error('invalid module cache address');
  }
  // The user-visible key stays stable. The Actions SDK binds the content-specific
  // relative path into its cache version so two revisions of a shard can coexist.
  const path = join('build/lean-cache/modules', digest, 'payload');
  const { cache } = await loadCacheClient();
  await mkdir(dirname(path), { recursive: true });
  try {
    if (put && await cache.restoreCache([path], key, [], { lookupOnly: true }) !== key) {
      if (await digestFile(file) !== digest) throw new Error('module cache upload checksum mismatch');
      await copyFile(file, path);
      await cache.saveCache([path], key);
    }
    await rm(path, { force: true });
    if (await cache.restoreCache([path], key, []) !== key) {
      process.exitCode = 4;
      throw new Error('module cache entry unavailable');
    }
    if (await digestFile(path) !== digest) {
      process.exitCode = 5;
      throw new Error('module cache entry checksum mismatch');
    }
    if (!put) await copyFile(path, file);
  } finally {
    await rm(path, { force: true });
  }
}

async function restorePublished(tool, env) {
  const args = ['-B', tool, 'restore'];
  if (targetsFile) args.push('--targets-file', targetsFile);
  else if (targets.length) args.push('--targets', ...targets);
  const child = spawn('python3', args, { env, stdio: ['ignore', 'pipe', 'inherit'] });
  let lastLine;
  createInterface({ input: child.stdout, crlfDelay: Infinity }).on('line', line => {
    console.log(line);
    if (line.trim()) lastLine = line;
  });
  const [code, signal] = await once(child, 'close');
  let requested = 0;
  let restored = 0;
  if (code === 3) {
    console.log('No published module cache yet. Continuing with the local Lean build.');
  } else {
    if (code !== 0) throw new Error('module cache restore failed: ' + (signal || code));
    ({ requested, restored } = JSON.parse(lastLine));
    if (!Number.isSafeInteger(requested) || !Number.isSafeInteger(restored) || restored < 0 || restored > requested) {
      throw new Error('invalid published module restore counts');
    }
  }
  if (process.env.GITHUB_OUTPUT) {
    const complete = restored > 0 && restored === requested;
    await writeFile(process.env.GITHUB_OUTPUT, `available=${restored}\ncomplete=${complete}\n`, { flag: 'a' });
  }
}

async function runModuleCache() {
  const temp = process.env.RUNNER_TEMP;
  const plan = join(temp, 'module-plan.json');
  const tool = 'tools/scripts/worktree/lean_module_cache.py';
  const env = { ...process.env, LEAN_MODULE_ACTIONS_CACHE: '1' };
  if (operation === 'restore-published') return restorePublished(tool, env);
  requirePublisher();
  let args;
  if (operation === 'module-plan') {
    const capacity = Number(process.env.SHARD_MIB || 256);
    if (!Number.isSafeInteger(capacity) || capacity < 1 || capacity >= 2048) {
      throw new Error('shard_mib must be between 1 and 2047');
    }
    args = ['plan', '--capacity', String(capacity * 1024 ** 2), '--output', plan, '--prepare-release'];
  } else if (operation === 'module-worker') {
    const lane = process.env.MODULE_LANE;
    if (!/^(0|[1-9][0-9]*)$/.test(lane)) throw new Error('invalid module lane');
    args = ['worker', '--plan', plan, '--lane', lane, '--output', join(temp, 'module-worker')];
  } else {
    args = ['finish', '--plan', plan, '--output', join(temp, 'module-index.json')];
  }
  execFileSync('python3', ['-B', tool, ...args], { stdio: 'inherit', env });
}

async function main() {
  if (['module-plan', 'module-worker', 'module-finish', 'restore-published'].includes(operation)) return runModuleCache();
  if (operation === 'module-get' || operation === 'module-put') return moduleCacheEntry(...process.argv.slice(3));
  if (operation === 'generation-get' || operation === 'generation-put') {
    return generationIndex(process.argv[3], process.argv[4]);
  }
  if (operation === 'restore-preparation') return restorePreparation(process.argv[3]);
  throw new Error('invalid Actions shard operation');
}

try {
  await main();
} catch (error) {
  process.exitCode ||= 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
