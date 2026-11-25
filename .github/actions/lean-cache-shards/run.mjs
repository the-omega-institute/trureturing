import { execFileSync, spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { once } from 'node:events';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, mkdtemp, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline';
import { fileURLToPath, pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const operation = process.argv[2] || process.env.INPUT_OPERATION;
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const targetsFile = process.env['INPUT_TARGETS-FILE'];
// A nested JavaScript action may inherit the enclosing composite's action path.
const actionPath = dirname(fileURLToPath(import.meta.url));

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
  return import(pathToFileURL(join(library, 'cache.js')).href);
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
  const cache = await loadCacheClient();
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
  const cache = await loadCacheClient();
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
  if (process.env.INPUT_VERSION) args.push('--version', process.env.INPUT_VERSION);
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
  throw new Error('invalid Actions shard operation');
}

try {
  await main();
} catch (error) {
  process.exitCode ||= 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
