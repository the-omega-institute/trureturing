import { execFileSync, spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { latestSeed, migrateSeed, selectSeed } from './legacy-seed.mjs';
import { createReadStream } from 'node:fs';
import { copyFile, mkdir, mkdtemp, readdir, readFile, rename, rm, stat, writeFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import { performance } from 'node:perf_hooks';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { createInterface } from 'node:readline';
import { setTimeout as delay } from 'node:timers/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';

const workspace = process.env.GITHUB_WORKSPACE;
process.chdir(workspace);

const stage = 'build/lean-cache/shards';
const indexPath = join(stage, 'index.json');
const operation = process.argv[2] || process.env.INPUT_OPERATION;
const state = process.env.INPUT_STATE || 'complete';
const targets = (process.env.INPUT_TARGETS || '').trim().split(/\s+/).filter(Boolean);
const targetsFile = process.env['INPUT_TARGETS-FILE'];
const anchor = process.env.INPUT_ANCHOR;
const resumeAfterAttempt = process.env['INPUT_RESUME-AFTER-ATTEMPT'] || '';
const requireComplete = process.env['INPUT_REQUIRE-COMPLETE'] === 'true';
const shardedAdoption = process.env['INPUT_SHARDED-ADOPTION'] === 'true';
// A nested JavaScript action may inherit the enclosing composite's action path.
const actionPath = dirname(fileURLToPath(import.meta.url));
const targetArgs = targetsFile ? ['--targets-file', targetsFile] : targets.flatMap(target => ['--target', target]);
const pythonTool = 'tools/scripts/worktree/lean_actions_shards.py';
const preparationTool = 'tools/scripts/worktree/lean_pr_cache.py';
const cacheWriteDenied = /cache write denied:|your cache is now read[ -]only/i;

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

function payloadPath(digest) {
  if (!/^[0-9a-f]{64}$/.test(digest)) throw new Error('invalid shard payload address');
  return join(stage, 'payload', digest + '.tar.gz');
}

function payloadKey(prefix, digest) {
  return prefix + 'material-' + digest;
}

function snapshotPrefix(identity) {
  return identity.snapshot_prefix || identity.prefix + 'snapshot-';
}

function indexKey(identity) {
  const { run, attempt } = identity.owner;
  return snapshotPrefix(identity) + run + '-' + attempt;
}

function snapshotRows(rows, prefix, version, anyConfiguration = false) {
  const suffix = anyConfiguration
    ? /^(?<config>[0-9a-f]{64})-(?<run>[1-9][0-9]*)-(?<attempt>[1-9][0-9]*)$/
    : /^(?<run>[1-9][0-9]*)-(?<attempt>[1-9][0-9]*)$/;
  return rows.flatMap(row => {
    if (row.version !== version || !row.key.startsWith(prefix)) return [];
    const match = suffix.exec(row.key.slice(prefix.length));
    return match ? [{ ...row, ...match.groups }] : [];
  }).sort((left, right) => right.run.localeCompare(left.run, 'en', { numeric: true })
    || right.attempt.localeCompare(left.attempt, 'en', { numeric: true }));
}

async function restoreIndex(cache, row) {
  if (await cache.restoreCache([indexPath], row.key, []) !== row.key) return;
  const record = JSON.parse(await readFile(indexPath, 'utf8'));
  if (record.owner.run !== row.run || record.owner.attempt !== row.attempt || record.owner.ref !== row.ref) {
    throw new Error('Actions index did not match the producing run or ref');
  }
  return record;
}

async function paced(items, parallelism, perMinute, invoke, schedule = { next: performance.now() }) {
  const interval = 60000 / perMinute;
  let position = 0;
  let failure;
  await Promise.all(Array.from({ length: Math.min(items.length, parallelism) }, async () => {
    while (!failure && position < items.length) {
      const item = items[position++];
      const now = performance.now();
      const scheduled = Math.max(now, schedule.next);
      schedule.next = scheduled + interval;
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

async function prepareBatches(args, consume) {
  const child = spawn('python3', ['-B', pythonTool, 'prepare', '--state', state, '--stream-payloads', ...args], {
    stdio: ['pipe', 'pipe', 'inherit'],
  });
  const finished = new Promise(resolve => {
    child.once('error', error => resolve(error));
    child.once('close', code => resolve(code === 0 ? null : new Error('shard preparation exited with ' + code)));
  });
  child.stdin.on('error', () => {});
  let record;
  try {
    for await (const line of createInterface({ input: child.stdout, crlfDelay: Infinity })) {
      const batchPrefix = 'SHARD_PAYLOAD_BATCH ';
      if (line.startsWith(batchPrefix)) {
        const batch = JSON.parse(line.slice(batchPrefix.length));
        await consume(batch);
        child.stdin.write('continue\n');
      } else if (line.startsWith('{')) {
        record = JSON.parse(line);
      } else {
        console.log(line);
      }
    }
    const error = await finished;
    if (error) throw error;
    if (!record) throw new Error('shard preparation returned no index');
    return record;
  } finally {
    child.stdin.end();
    if (child.exitCode === null) child.kill();
    await finished;
  }
}

function waitForCacheQuota() {
  return delay(60000 + Math.floor(Math.random() * 10000));
}

async function fetchIndex(cache, cacheVersion, identity, protectedOnly = false) {
  const ref = process.env.GITHUB_BASE_REF ? 'refs/heads/' + process.env.GITHUB_BASE_REF : identity.owner.ref;
  const refs = state === 'resume' || protectedOnly ? [ref] : [...new Set([ref, 'refs/heads/dev'])];
  await rm(indexPath, { force: true });
  let retry;
  const locations = [{ discovery: identity.prefix + 'snapshot-', exact: snapshotPrefix(identity) }];
  if (identity.legacy_prefix) {
    const legacy = identity.legacy_prefix + 'snapshot-';
    locations.push({ discovery: legacy, exact: legacy });
  }
  for (const candidateRef of refs.filter(value => /^refs\/heads\/(dev|integration-[A-Za-z0-9._/-]+)$/.test(value))) {
    for (const { discovery, exact } of locations) {
      const rows = snapshotRows(optionalInventory(candidateRef, discovery), exact, cacheVersion(indexPath))
        .filter(({ run, attempt }) => !resumeAfterAttempt || (run === identity.owner.run
          && BigInt(attempt) > BigInt(resumeAfterAttempt) && BigInt(attempt) < BigInt(identity.owner.attempt)));
      retry ||= rows[0];
      for (const row of rows.slice(0, 3)) {
        if (await restoreIndex(cache, row)) return row.key;
      }
    }
  }
  if (retry) {
    await waitForCacheQuota();
    if (await restoreIndex(cache, retry)) return retry.key;
  }
}

async function visibleMaterial(prefixes, index, cacheVersion) {
  const { owner } = JSON.parse(await readFile(index, 'utf8'));
  const visible = new Set(prefixes.flatMap(prefix => optionalInventory(owner.ref, prefix + 'material-')
    .map(row => row.key + '/' + row.version)));
  return digest => prefixes.some(prefix => visible.has(payloadKey(prefix, digest) + '/' + cacheVersion(payloadPath(digest))));
}

async function restorePayloads(cache, cacheVersion, prefixes, index, preparation) {
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
    try {
      await rm(path, { force: true });
      for (const prefix of prefixes) {
        const key = payloadKey(prefix, digest);
        if (await cache.restoreCache([path], key, []) === key) {
          const { size } = await stat(path);
          transferred += size;
          downloaded.add(digest);
          return;
        }
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
        pending = pending.filter(await visibleMaterial(prefixes, index, cacheVersion));
      }
      retries += 1;
    }
    const installArgs = ['--index', index, ...targetArgs];
    if (preparation) installArgs.push('--preparation', preparation);
    if (requireComplete || preparation) installArgs.push('--require-complete');
    const result = python('install', installArgs);
    console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
      operation, requested: digests.length, remote: remote.length, downloaded: downloaded.size,
      restored: result.available, missing: result.missing.length,
      bytes: transferred, seconds: (performance.now() - started) / 1000,
    }));
    return result;
  } finally {
    await Promise.all(remote.map(digest => rm(payloadPath(digest), { force: true })));
  }
}

async function restore(cache, cacheVersion, identity) {
  const matched = await fetchIndex(cache, cacheVersion, identity);
  if (!matched) {
    console.log('LEAN_ACTIONS_SHARDS no compatible index was found');
    return;
  }
  const prefix = identity.legacy_prefix && matched.startsWith(identity.legacy_prefix) ? identity.legacy_prefix : identity.prefix;
  if (operation === 'lookup') {
    const entries = python('restore-plan', ['--index', indexPath]);
    const digests = [...new Set(Object.values(entries))];
    const present = digests.filter(await visibleMaterial([prefix], indexPath, cacheVersion)).length;
    console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({ operation, requested: digests.length, visible: present }));
    await setOutputs({ key: matched, visible: present, complete: present > 0 && present === digests.length });
    return;
  }
  const result = await restorePayloads(cache, cacheVersion, [prefix], indexPath);
  await setOutputs({ key: matched, available: result.available, missing: result.missing.length,
    complete: result.complete });
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

async function runModuleCache() {
  const temp = process.env.RUNNER_TEMP;
  const plan = join(temp, 'module-plan.json');
  const tool = 'tools/scripts/worktree/lean_module_cache.py';
  const kind = process.env.INPUT_KIND || '';
  if (kind && !['compiler', 'report'].includes(kind)) throw new Error('invalid publication kind');
  let args;
  if (operation === 'restore-published') {
    if (targetsFile && !(await readFile(targetsFile, 'utf8')).trim()) return;
    args = ['restore'];
    if (kind) args.push('--kind', kind);
    if (process.env.INPUT_STAGED === 'true') args.push('--staged');
    if (process.env.INPUT_VERSION) args.push('--version', process.env.INPUT_VERSION);
    if (process.env['INPUT_LAKE-SEED'] === 'true' && process.env.GITHUB_EVENT_NAME === 'pull_request'
        && process.env.GITHUB_JOB === 'current' && kind !== 'report'
        && !process.env.INPUT_VERSION && process.env.INPUT_STAGED !== 'true') {
      args.push('--lake-seed');
    }
    if (targetsFile) args.push('--targets-file', targetsFile);
    else if (targets.length) args.push('--targets', ...targets);
  } else if (operation === 'module-plan') {
    requirePublisher(kind || 'compiler');
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
      args.push('--compiler-dag', '--legacy-checkpoints', '--workers', String(workers));
    }
  } else {
    requirePublisher(kind || 'compiler');
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
  try {
    execFileSync('python3', ['-B', tool, ...args], {
      stdio: 'inherit', env: { ...process.env, LEAN_MODULE_ACTIONS_CACHE: '1' },
    });
  } catch (error) {
    if (operation !== 'restore-published' || error.status !== 3 || process.env.INPUT_VERSION) throw error;
    console.log('No published module cache yet. Continuing with the local Lean build.');
  }
}

async function save(cache, cacheVersion, identity, packageFile) {
  // The pinned SDK reports both a denied reservation and a race as -1.
  // Observe its original diagnostic for this write operation only.
  const sdkRequire = createRequire(packageFile);
  const core = sdkRequire('@actions/core');
  const warning = core.warning;
  const writes = new AbortController();
  core.warning = (message, ...args) => {
    warning(message, ...args);
    if (cacheWriteDenied.test(message)) writes.abort(new Error(String(message)));
  };
  try {
    await saveShards(cache, cacheVersion, identity, writes.signal);
  } finally {
    core.warning = warning;
    // Preparation can have packed the next digest before it sent this batch.
    if (writes.signal.aborted) await rm(join(stage, 'payload'), { recursive: true, force: true });
  }
}

async function saveShards(cache, cacheVersion, identity, writes) {
  const saveEntry = async (path, key) => {
    writes.throwIfAborted();
    const result = await cache.saveCache([path], key);
    writes.throwIfAborted();
    return result;
  };
  const started = performance.now();
  const prefix = identity.prefix + 'material-';
  const ownerRef = identity.owner.ref;
  const before = visibleEntries(ownerRef, identity.prefix);
  const version = cacheVersion(indexPath);
  const current = snapshotRows(before, snapshotPrefix(identity), version);
  // A protected producer can retain a layout across Lake configurations. The
  // packer compares current output fingerprints before reusing a stable digest.
  const candidates = [...current];
  if (identity.legacy_prefix) {
    const compatible = snapshotRows(before, identity.prefix + 'snapshot-', version, true);
    candidates.push(...compatible.filter(row => !row.key.startsWith(snapshotPrefix(identity))));
  }
  await rm(indexPath, { force: true });
  const extra = ['--anchor', anchor, ...targetArgs];
  const known = new Set();
  let previous;
  for (const row of candidates.slice(0, 3)) {
    previous = await restoreIndex(cache, row);
    if (previous) break;
  }
  if (!previous && identity.legacy_prefix) {
    const legacy = identity.legacy_prefix + 'snapshot-';
    for (const row of snapshotRows(optionalInventory(ownerRef, legacy), legacy, version).slice(0, 3)) {
      previous = await restoreIndex(cache, row);
      if (previous) break;
    }
  }
  if (previous) {
    for (const digest of Object.values(previous.entries)) {
      if (matches(before, payloadKey(identity.prefix, digest), cacheVersion(payloadPath(digest)))) known.add(digest);
    }
    const available = join(stage, 'visible-material.json');
    await writeFile(available, JSON.stringify([...known]));
    extra.push('--index', indexPath, '--available', available);
  }

  if (!previous && process.env['INPUT_REQUIRE-EXISTING-INDEX'] === 'true') {
    throw new Error('indexed publication requires the previous layout; the long producer can bootstrap');
  }
  const confirmed = new Set(known);
  const upload = async (digest, inventory) => {
    const path = payloadPath(digest);
    const key = payloadKey(identity.prefix, digest);
    try {
      if (!matches(inventory, key, cacheVersion(path)) && await saveEntry(path, key) >= 0) {
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
      writes.throwIfAborted();
      console.log('LEAN_ACTIONS_SHARDS save failed for ' + digest + ': ' + error.message);
    }
  };
  const reconcile = () => {
    const rows = visibleEntries(ownerRef, prefix);
    const visible = new Set(rows.map(row => row.key + '/' + row.version));
    for (const digest of confirmed) {
      if (!visible.has(payloadKey(identity.prefix, digest) + '/' + cacheVersion(payloadPath(digest)))) confirmed.delete(digest);
    }
    return rows;
  };
  const prepareAndUpload = (args, perMinute, inventory) => {
    const schedule = { next: performance.now() };
    return prepareBatches(args, batch => paced(batch, 8, perMinute, async digest => {
      try {
        await upload(digest, inventory);
      } finally {
        await rm(payloadPath(digest), { force: true });
      }
    }, schedule));
  };
  // Leave headroom in GitHub's 200 uploads per repository per minute.
  const record = await prepareAndUpload(extra, 85, before);
  const digests = [...new Set(Object.values(record.entries))];
  const expected = new Set(digests);
  for (const digest of confirmed) {
    if (!expected.has(digest)) confirmed.delete(digest);
  }
  const previousCount = digests.filter(digest => known.has(digest)).length;
  reconcile();
  if (confirmed.size !== digests.length) {
    await waitForCacheQuota();
    const inventory = reconcile();
    const available = join(stage, 'visible-material.json');
    await writeFile(available, JSON.stringify([...confirmed]));
    await writeFile(indexPath, JSON.stringify(record));
    console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
      operation: 'retry-upload', requested: digests.length - confirmed.size, perMinute: 50,
    }));
    const retry = await prepareAndUpload(['--anchor', anchor, ...targetArgs,
      '--index', indexPath, '--available', available], 50, inventory);
    if (JSON.stringify(retry.entries) !== JSON.stringify(record.entries)) {
      throw new Error('shard material changed while retrying publication');
    }
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
  if (await saveEntry(indexPath, key) < 0
      && (!matches(visibleEntries(ownerRef, key), key, cacheVersion(indexPath))
        || await cache.restoreCache([indexPath], key, []) !== key
        || await readFile(indexPath, 'utf8') !== encoded)) {
    throw new Error('Actions did not publish the intended shard index');
  }
  if (!matches(visibleEntries(ownerRef, key), key, cacheVersion(indexPath))) {
    throw new Error('Actions index is not visible on its producer ref');
  }
  console.log('LEAN_ACTIONS_SHARDS ' + JSON.stringify({
    operation: 'save', requested: digests.length, previous: previousCount,
    confirmed: confirmed.size, seconds: (performance.now() - started) / 1000,
  }));
  await setOutputs({ key, available: confirmed.size, missing, complete: state === 'complete' });
}

async function setOutputs(fields) {
  const lines = Object.entries(fields).map(([key, value]) => key + '=' + value).join('\n') + '\n';
  await writeFile(process.env.GITHUB_OUTPUT, lines, { flag: 'a' });
}

// The cache SDK reports policy denials as warnings and returns the same miss
// sentinel as a reservation race. Keep its diagnostic and distinguish the two
// before a failed producer tries to stage a full archive for the same service.
async function saveContinuation() {
  const child = spawn(process.execPath, [fileURLToPath(import.meta.url), 'save'], {
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  let blocked;
  const relay = async (stream, destination) => {
    for await (const line of createInterface({ input: stream, crlfDelay: Infinity })) {
      destination.write(line + '\n');
      if (/\b(?:ENOSPC|no space left on device)\b/i.test(line)) blocked = 'disk-full';
      if (cacheWriteDenied.test(line)) blocked = 'cache-read-only';
    }
  };
  const finished = new Promise((resolve, reject) => {
    child.once('error', reject);
    child.once('close', resolve);
  });
  const [code] = await Promise.all([finished, relay(child.stdout, process.stdout), relay(child.stderr, process.stderr)]);
  if (code !== 0) {
    const fallback = code !== null && !blocked;
    console.error('LEAN_ACTIONS_SHARDS legacy continuation fallback=' + (blocked || (fallback ? 'allowed' : 'interrupted')));
    await setOutputs({ legacy_fallback: String(fallback) });
    process.exitCode = code || 1;
  }
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
  if (['latest-seed', 'restore-seed', 'migrate-seed'].includes(operation)) {
    const io = { ...await loadCacheClient(), visibleEntries, restoreIndex, payloadPath, indexPath, digestFile, paced };
    const directory = join(process.env.RUNNER_TEMP, 'lean-generation-base');
    if (operation === 'migrate-seed') return migrateSeed(io, directory);
    if (operation === 'latest-seed') requirePublisher();
    const seed = await latestSeed(io, directory, operation === 'latest-seed');
    if (!seed) {
      if (operation === 'latest-seed') throw new Error('no complete protected dev seed found');
      console.log('LEAN_GENERATION_SEED no complete seed available');
      return;
    }
    if (operation === 'latest-seed') {
      await setOutputs({ key: seed.key, producer: seed.commit });
      return;
    }
    const selected = join(directory, 'selected.json');
    if (selectSeed(join(directory, 'index.json'), selected)) await restorePayloads(io.cache, io.cacheVersion, [seed.prefix], selected);
    return;
  }
  if (operation === 'save') requirePublisher();
  if (operation === 'save-continuation' && state === 'resume') return saveContinuation();
  if (resumeAfterAttempt && (operation !== 'restore' || state !== 'resume' || !/^(0|[1-9][0-9]*)$/.test(resumeAfterAttempt))) {
    throw new Error('resume-after-attempt requires a continuation restore and a nonnegative attempt number');
  }
  if (targetsFile && (targets.length || operation !== 'restore')) {
    throw new Error('a target file requires restore without inline targets');
  }
  if (operation === 'adopt-preparation') {
    const args = shardedAdoption ? ['--cache-action', process.execPath, fileURLToPath(import.meta.url)] : [];
    if (process.env['INPUT_REQUIRE-PR-OPT-IN'] === 'true') args.push('--require-pr-opt-in');
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
    const identity = python('identity');
    const prefixes = [identity.prefix, identity.legacy_prefix].filter(Boolean);
    const result = await restorePayloads(cache, cacheVersion, prefixes, join(directory, 'project.json'), directory);
    if (!result.complete) process.exitCode = 3;
    return;
  }
  if (!['save', 'restore', 'lookup'].includes(operation) || !['complete', 'resume'].includes(state)) {
    throw new Error('invalid Actions shard operation or state');
  }
  if (operation === 'save' && !anchor) throw new Error('Actions cache writes require a pinned history anchor');
  const { cache, cacheVersion, packageFile } = await loadCacheClient();
  const identity = python('identity');
  await mkdir(stage, { recursive: true });
  if (operation === 'save') await save(cache, cacheVersion, identity, packageFile);
  else await restore(cache, cacheVersion, identity);
}

try {
  await main();
} catch (error) {
  process.exitCode ||= 1;
  console.error('LEAN_ACTIONS_SHARDS ' + error.message);
}
