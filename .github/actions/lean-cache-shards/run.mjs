import { execFileSync, spawn } from 'node:child_process';
import { once } from 'node:events';
import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, mkdtemp, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import { dirname, isAbsolute, join, resolve } from 'node:path';
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
  return { cache, packageFile: join(install, 'node_modules/@actions/cache/package.json'),
    cacheVersion: path => utils.getCacheVersion([path], compression) };
}

async function digestFile(path) {
  const hash = createHash('sha256');
  for await (const chunk of createReadStream(path)) hash.update(chunk);
  return hash.digest('hex');
}

function requirePublisher(kind, allowCompilerChild = false) {
  const env = process.env;
  const workflow = kind === 'report' ? 'report-release-publish.yml' : 'cache-release-publish.yml';
  const events = ['schedule', 'workflow_dispatch'];
  if (kind === 'compiler') events.push('push');
  if (kind === 'report') events.push('workflow_run');
  const path = env.GITHUB_REPOSITORY + '/.github/workflows/';
  const worker = allowCompilerChild && kind === 'compiler' && env.GITHUB_EVENT_NAME === 'workflow_dispatch'
    && env.GITHUB_WORKFLOW_REF === path + 'ci-lean-generation-compile.yml@refs/heads/dev';
  if (!events.includes(env.GITHUB_EVENT_NAME)
      || env.GITHUB_REF !== 'refs/heads/dev' || env.GITHUB_REF_PROTECTED !== 'true'
      || env.STRATALINT_CACHE_WRITES !== 'true'
      || (!worker && env.GITHUB_WORKFLOW_REF !== path + workflow + '@refs/heads/dev')) {
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
  if (put) requirePublisher(key?.endsWith('-report') ? 'report' : 'compiler', true);
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

function visibleEntries(ref, prefix) {
  const repository = process.env.GITHUB_REPOSITORY;
  if (!process.env.GH_TOKEN || !repository) throw new Error('Actions cache inventory credentials are missing');
  const listing = execFileSync('gh', [
    'api', '--paginate', '--method', 'GET', 'repos/' + repository + '/actions/caches',
    // Restores update last_accessed_at while other workers are paging through the same keys.
    '-f', 'sort=created_at', '-f', 'direction=asc', '-f', 'ref=' + ref, '-f', 'per_page=100', '-f', 'key=' + prefix,
    '--jq', '.actions_caches[] | {key, ref, version, created_at}',
  ], { encoding: 'utf8', timeout: 300000, maxBuffer: 64 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  return listing.trim().split('\n').filter(Boolean).map(line => JSON.parse(line)).filter(row => row.ref === ref);
}

// The SDK logs throttling and returns the same sentinel as a cache miss or
// a lost reservation. Respect the reported reset before retrying the operation.
async function checkpointRequest(core, request, succeeded, verifyReservation = false) {
  const { warning, error } = core;
  const deadline = performance.now() + 75000;
  let attempts = 0;
  for (;;) {
    let retrySeconds;
    let failure;
    const capture = log => (message, ...args) => {
      const detail = String(message);
      const reset = /rate limit will reset in (\d+) seconds?/i.exec(detail);
      if (reset) retrySeconds = Number(reset[1]);
      else if (/rate limited|too many requests|\b429\b/i.test(detail)) retrySeconds ??= 2;
      failure = detail;
      log(message, ...args);
    };
    core.warning = capture(warning);
    core.error = capture(error);
    let result;
    try {
      result = await request();
    } finally {
      core.warning = warning;
      core.error = error;
    }
    if (succeeded(result)) return result;
    if (retrySeconds === undefined) {
      if (failure && !verifyReservation) throw new Error(failure);
      return result;
    }
    const ms = 1000 * Math.max(retrySeconds, Math.min(16, 2 ** attempts)) + Math.random() * 2000;
    if (performance.now() + ms >= deadline) throw new Error(failure);
    console.log('Actions Cache throttled compiler checkpoint, retrying in ' + Math.ceil(ms / 1000) + 's');
    await delay(ms);
    attempts++;
  }
}

async function restoreCheckpoint(cache, core, path, key) {
  const matched = await checkpointRequest(core, () => cache.restoreCache([path], key, []), result => result === key);
  if (matched !== undefined && matched !== key) throw new Error('unexpected compiler checkpoint key ' + matched);
  return matched === key;
}

async function compilerCheckpoint(kind, ...args) {
  requirePublisher('compiler', kind === 'unit');
  if (!['unit', 'catalog'].includes(kind)) throw new Error('invalid compiler checkpoint kind');
  const prefix = 'lean-compiler-' + kind + '-v1-';
  // Every runner must use the same literal path to derive the SDK cache version.
  const path = join(stage, 'compiler-checkpoints', kind);
  const { cache, cacheVersion, packageFile } = await loadCacheClient();
  if (operation === 'compiler-cache-list') {
    const [output] = args;
    if (args.length !== 1 || !output) throw new Error('expected a compiler inventory destination');
    const version = cacheVersion(path);
    const rows = [];
    for (const entry of visibleEntries('refs/heads/dev', prefix)) {
      if (entry.version !== version || !entry.key.startsWith(prefix)) continue;
      const match = /^([0-9a-f]{64})-([0-9a-f]{64})-([1-9][0-9]*)$/.exec(entry.key.slice(prefix.length));
      if (!match || !Number.isSafeInteger(Number(match[3]))) continue;
      const [, id, sha256, bytes] = match;
      if (kind === 'catalog' && id !== sha256) continue;
      rows.push({ id, sha256, bytes: Number(bytes) });
    }
    await writeFile(output, JSON.stringify(rows));
    return;
  }
  const [id, sha256, bytes, file] = args;
  if (args.length !== 4 || !isAbsolute(file) || !/^[0-9a-f]{64}$/.test(id) || !/^[0-9a-f]{64}$/.test(sha256)
      || !/^[1-9][0-9]*$/.test(bytes) || !Number.isSafeInteger(Number(bytes))
      || (kind === 'catalog' && id !== sha256)) {
    throw new Error('invalid compiler checkpoint address');
  }
  const key = prefix + id + '-' + sha256 + '-' + bytes;
  const verify = async candidate => {
    if ((await stat(candidate)).size !== Number(bytes) || await digestFile(candidate) !== sha256) {
      throw new Error('compiler checkpoint checksum or length mismatch');
    }
  };
  const core = createRequire(packageFile)('@actions/core');
  // Concurrent operations in a single runner must not extract over one another.
  const temporary = await mkdtemp(join(process.env.RUNNER_TEMP, 'compiler-checkpoint-'));
  try {
    process.env.GITHUB_WORKSPACE = temporary;
    process.chdir(temporary);
    await mkdir(dirname(path), { recursive: true });
    if (operation === 'compiler-cache-put') {
      await copyFile(file, path);
      await verify(path);
      if (await checkpointRequest(core, () => cache.saveCache([path], key), id => id > 0, true) > 0) return;
      await rm(path, { force: true });
      // A competing reservation can be visible only after its upload finalizes.
      for (const ms of [0, 1000, 2000, 4000, 8000, 16000]) {
        if (ms) await delay(ms);
        if (await restoreCheckpoint(cache, core, path, key)) {
          await verify(path);
          return;
        }
      }
      throw new Error('Actions Cache did not publish compiler checkpoint ' + key);
    }
    if (!await restoreCheckpoint(cache, core, path, key)) {
      process.exitCode = 4;
      throw new Error('Actions compiler checkpoint unavailable: ' + key);
    }
    await verify(path);
    await copyFile(path, file);
  } finally {
    process.chdir(workspace);
    process.env.GITHUB_WORKSPACE = workspace;
    await rm(temporary, { recursive: true, force: true });
  }
}

async function runCompilerDispatch() {
  const assigned = operation === 'compiler-assigned';
  requirePublisher('compiler', assigned);
  const temp = process.env.RUNNER_TEMP;
  const plan = join(temp, 'module-plan.json');
  const resume = join(temp, 'compiler-resume');
  const tool = 'tools/scripts/worktree/lean_module_cache.py';
  const env = { ...process.env, LEAN_MODULE_ACTIONS_CACHE: '1' };
  const run = (script, ...args) => execFileSync('python3', ['-B', script, ...args], { env, stdio: 'inherit' });
  if (!assigned) {
    const controller = '.github/scripts/compiler-release-coordinator.py';
    if (operation === 'compiler-coordinate-prepare') {
      run(controller, '--prepare-only', '--plan', plan, '--directory', resume);
    } else {
      const args = ['--plan', join(resume, 'module-plan.json'), '--pending', join(resume, 'pending.json')];
      for (const [name, flag] of [['COMPILER_MAX_ACTIVE', '--max-active'],
        ['COMPILER_UNITS_PER_BATCH', '--units-per-batch'], ['COMPILER_SHARDS_PER_BATCH', '--shards-per-batch']]) {
        if (env[name]) args.push(flag, env[name]);
      }
      run(controller, ...args);
    }
    return;
  }
  if (env.GITHUB_EVENT_NAME !== 'workflow_dispatch' ||
      env.GITHUB_WORKFLOW_REF !== env.GITHUB_REPOSITORY + '/.github/workflows/ci-lean-generation-compile.yml@refs/heads/dev') {
    throw new Error('compiler assignment requires the protected child workflow');
  }
  const phase = env.COMPILER_PHASE;
  const units = phase === 'units';
  const assignments = JSON.parse(env.COMPILER_ASSIGNMENT);
  if ((!units && phase !== 'shards') || !Array.isArray(assignments) || !assignments.length ||
      new Set(assignments).size !== assignments.length || !assignments.every(value => units
        ? typeof value === 'string' && /^[0-9a-f]{64}$/.test(value)
        : Number.isSafeInteger(value) && value >= 0)) throw new Error('invalid compiler assignment');
  const directory = join(temp, 'compiler-result');
  await mkdir(directory, { recursive: true });
  const result = join(directory, 'result.json');
  const receipts = join(temp, 'compiler-receipts.json');
  run(tool, 'compiler-receipts', '--plan', plan, '--output', receipts);
  if (units) {
    const assignment = join(temp, 'compiler-assignment.json');
    await writeFile(assignment, JSON.stringify(assignments));
    run(tool, 'compiler-units', '--plan', plan, '--assignment', assignment, '--receipts', receipts, '--output', result);
  } else {
    for (const lane of assignments) {
      run(tool, 'worker', '--plan', plan, '--lane', String(lane), '--receipts', receipts,
        '--output', join(temp, 'compiler-shards-' + lane));
    }
    await writeFile(result, JSON.stringify({ lanes: assignments }));
  }
}

async function restorePublished(tool, env, kind) {
  const args = ['-B', tool, 'restore'];
  if (kind) args.push('--kind', kind);
  if (process.env.INPUT_STAGED === 'true') args.push('--staged');
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
  let restored = 0;
  let complete = false;
  if (code === 3 && !process.env.INPUT_VERSION) {
    console.log('No published module cache yet. Continuing with the local Lean build.');
  } else {
    if (code !== 0) throw new Error('module cache restore failed: ' + (signal || code));
    const result = JSON.parse(lastLine);
    const requested = result.requested;
    restored = result.restored;
    if (!Number.isSafeInteger(requested) || !Number.isSafeInteger(restored) || restored < 0 || restored > requested) {
      throw new Error('invalid published module restore counts');
    }
    complete = restored > 0 && restored === requested && !Object.hasOwn(result, 'report_error')
      && result.supporting_compilers_restored === result.supporting_compilers_requested;
  }
  if (process.env.GITHUB_OUTPUT) {
    await writeFile(process.env.GITHUB_OUTPUT, `available=${restored}\ncomplete=${complete}\n`, { flag: 'a' });
  }
}

async function runModuleCache() {
  const temp = process.env.RUNNER_TEMP;
  const plan = join(temp, 'module-plan.json');
  const tool = 'tools/scripts/worktree/lean_module_cache.py';
  const kind = process.env.INPUT_KIND || '';
  if (kind && !['compiler', 'report'].includes(kind)) throw new Error('invalid publication kind');
  const env = { ...process.env, LEAN_MODULE_ACTIONS_CACHE: '1' };
  if (operation === 'restore-published') return restorePublished(tool, env, kind);
  requirePublisher(kind || 'compiler');
  let args;
  if (operation === 'module-plan') {
    const capacity = Number(process.env.SHARD_MIB || 256);
    if (!Number.isSafeInteger(capacity) || capacity < 1 || capacity >= 2048) {
      throw new Error('shard_mib must be between 1 and 2047');
    }
    const publicationKind = kind || 'compiler';
    args = ['plan', '--kind', publicationKind, '--capacity', String(capacity * 1024 ** 2),
      '--output', plan, '--prepare-release'];
    if (publicationKind === 'compiler') {
      const workers = Number(process.env.LEAN_COMPILER_WORKERS || 64);
      if (!Number.isSafeInteger(workers) || workers < 1 || workers > 256) {
        throw new Error('LEAN_COMPILER_WORKERS must be an integer between 1 and 256');
      }
      args.push('--compiler-dag', '--workers', String(workers));
    }
  } else {
    if (operation === 'module-worker') {
      const lane = process.env.MODULE_LANE;
      if (!/^(0|[1-9][0-9]*)$/.test(lane)) throw new Error('invalid module lane');
      args = ['worker', '--plan', plan, '--lane', lane, '--output', join(temp, 'module-worker')];
    } else if (operation === 'module-stage') {
      args = ['finish', '--stage-only', '--plan', plan, '--output', join(temp, 'module-index.json')];
    } else {
      args = ['promote', '--kind', kind, '--version', process.env.INPUT_VERSION];
    }
  }
  execFileSync('python3', ['-B', tool, ...args], { stdio: 'inherit', env });
}

async function main() {
  if (['compiler-coordinate-prepare', 'compiler-coordinate', 'compiler-assigned'].includes(operation)) return runCompilerDispatch();
  if (['module-plan', 'module-worker', 'module-stage', 'module-promote', 'restore-published'].includes(operation)) return runModuleCache();
  if (['compiler-cache-list', 'compiler-cache-put', 'compiler-cache-get'].includes(operation)) {
    return compilerCheckpoint(...process.argv.slice(3));
  }
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
