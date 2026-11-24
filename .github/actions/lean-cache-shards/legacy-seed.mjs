import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { copyFile, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { createInterface } from 'node:readline';

const ref = 'refs/heads/dev';
const hex = '[0-9a-f]{64}';
const snapshot = new RegExp('^(lean-shard-index-v[12]-' + hex + '-)snapshot-(?:' + hex + '-)?([1-9][0-9]*)-([1-9][0-9]*)$');

function api(path, projection = '.') {
  return JSON.parse(execFileSync('gh', ['api', 'repos/' + process.env.GITHUB_REPOSITORY + '/' + path, '--jq', projection],
    { encoding: 'utf8', timeout: 90000 }));
}

const pinName = 'lean-generation-bootstrap-v1';

function gitApi(path, body) {
  const args = ['api', 'repos/' + process.env.GITHUB_REPOSITORY + '/git/' + path];
  if (body) args.push('--method', 'POST', '--input', '-');
  return JSON.parse(execFileSync('gh', args, {
    input: body ? JSON.stringify(body) : undefined, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024,
    timeout: 120000, stdio: ['pipe', 'pipe', 'pipe'],
  }));
}

async function pinnedSeed(io, directory) {
  let ref;
  try {
    ref = gitApi('ref/tags/' + pinName);
  } catch (error) {
    if (error.status && JSON.parse(error.stdout || '{}').status === '404') return;
    throw error;
  }
  if (ref.ref !== 'refs/tags/' + pinName || ref.object.type !== 'tag') throw new Error('invalid bootstrap ref');
  const tag = gitApi('tags/' + ref.object.sha);
  if (tag.tag !== pinName || tag.object.type !== 'blob') throw new Error('invalid bootstrap pin');
  const seed = JSON.parse(tag.message);
  const blob = gitApi('blobs/' + tag.object.sha);
  if (blob.sha !== tag.object.sha || blob.encoding !== 'base64' || blob.size > 32 * 1024 * 1024) {
    throw new Error('invalid bootstrap index blob');
  }
  await mkdir(directory, { recursive: true });
  await writeFile(join(directory, 'index.json'), Buffer.from(blob.content, 'base64'));
  await writeFile(join(directory, 'seed.json'), JSON.stringify(seed) + '\n');
  await validatePin(io, directory);
  return seed;
}

function persistSeed(seed, bytes) {
  const blob = gitApi('blobs', { content: bytes.toString('base64'), encoding: 'base64' });
  const tag = gitApi('tags', { tag: pinName, message: JSON.stringify(seed), object: blob.sha, type: 'blob' });
  gitApi('refs', { ref: 'refs/tags/' + pinName, sha: tag.sha });
}

function ownerMatches(seed, dev) {
  const { run, attempt, commit } = seed;
  if (!/^[0-9a-f]{40}$/.test(commit)) return false;
  const owner = api('actions/runs/' + run + '/attempts/' + attempt);
  if (owner.head_branch !== 'dev' || owner.head_sha !== commit || String(owner.id) !== run
      || String(owner.run_attempt) !== attempt || owner.head_repository?.full_name !== process.env.GITHUB_REPOSITORY
      || owner.path !== '.github/workflows/lean-cache-publish.yml' || owner.status !== 'completed'
      || owner.conclusion !== 'success' || !['push', 'workflow_dispatch'].includes(owner.event)) return false;
  const comparison = api('compare/' + commit + '...' + dev + '?per_page=1', '{ancestor: .merge_base_commit.sha}');
  return comparison.ancestor === commit;
}

const selectionTool = '.github/actions/lean-cache-shards/legacy-seed-selection.py';

function validateIndex(file) {
  return execFileSync('python3', ['-B', selectionTool, 'validate', file], { encoding: 'utf8' }).trim();
}

export function selectSeed(file, selected) {
  const result = spawnSync('python3', ['-B', selectionTool, 'select', file, selected], { stdio: 'inherit' });
  if (result.status === 3) return false;
  if (result.status !== 0) throw result.error || new Error('legacy seed selection failed');
  return true;
}

export async function latestSeed(io, directory, pin) {
  const prior = await pinnedSeed(io, directory);
  if (prior) return prior;
  const branch = api('branches/dev');
  if (branch.protected !== true) throw new Error('seed selection requires protected dev');
  const dev = ['schedule', 'workflow_dispatch'].includes(process.env.GITHUB_EVENT_NAME)
    ? execFileSync('git', ['rev-parse', '--verify', 'HEAD'], { encoding: 'utf8' }).trim() : branch.commit.sha;
  if (!/^[0-9a-f]{40}$/.test(dev)) throw new Error('expected a pinned protected dev commit');
  const rows = io.visibleEntries(ref, 'lean-shard-index-');
  const material = new Set(rows.map(row => row.key + '/' + row.version));
  const candidates = rows.flatMap(row => {
    const match = snapshot.exec(row.key);
    if (!match || row.version !== io.cacheVersion(io.indexPath)) return [];
    return [{ ...row, prefix: match[1], run: match[2], attempt: match[3] }];
  }).sort((a, b) => b.created_at.localeCompare(a.created_at)
    || b.run.localeCompare(a.run, 'en', { numeric: true })
    || b.attempt.localeCompare(a.attempt, 'en', { numeric: true }));
  await mkdir(directory, { recursive: true });
  for (const row of candidates) {
    let index;
    try {
      index = await io.restoreIndex(io.cache, row);
      if (!index || index.state !== 'complete' || validateIndex(io.indexPath) !== row.key) continue;
    } catch (error) {
      console.warn('Invalid legacy seed index ' + row.key + ': ' + error.message);
      continue;
    }
    const digests = new Set(Object.values(index.entries));
    if (![...digests].every(digest => material.has(row.prefix + 'material-' + digest + '/' + io.cacheVersion(io.payloadPath(digest))))) continue;
    const seed = { key: row.key, prefix: row.prefix, commit: index.owner.commit, run: row.run, attempt: row.attempt,
      index_sha256: await io.digestFile(io.indexPath) };
    if (!ownerMatches(seed, dev)) continue;
    await copyFile(io.indexPath, join(directory, 'index.json'));
    await writeFile(join(directory, 'seed.json'), JSON.stringify(seed) + '\n');
    console.log('LEAN_GENERATION_SEED ' + JSON.stringify({ ...seed, complete: true, entries: digests.size }));
    if (pin) {
      persistSeed(seed, await readFile(io.indexPath));
      return pinnedSeed(io, directory);
    }
    return seed;
  }
}

async function validatePin(io, directory) {
  const descriptor = JSON.parse(await readFile(join(directory, 'seed.json'), 'utf8'));
  const file = join(directory, 'index.json');
  const index = JSON.parse(await readFile(file, 'utf8'));
  if (descriptor.index_sha256 !== await io.digestFile(file) || validateIndex(file) !== descriptor.key
      || snapshot.exec(descriptor.key)?.[1] !== descriptor.prefix || index.owner.ref !== ref
      || index.owner.commit !== descriptor.commit || index.owner.run !== descriptor.run
      || index.owner.attempt !== descriptor.attempt) throw new Error('legacy seed pin mismatch');
  return { descriptor, index };
}

export async function migrateSeed(io, directory) {
  const { descriptor, index } = await validatePin(io, directory);
  const digests = new Set(Object.values(index.entries));
  const child = spawn('python3', ['-B', 'tools/scripts/worktree/lean_generation_seed.py',
    '--seed-root', 'build/seed-source', '--directory', directory], { stdio: ['pipe', 'pipe', 'inherit'] });
  const finished = new Promise(resolve => {
    child.once('error', resolve);
    child.once('exit', (code, signal) => resolve(code === 0 ? null : new Error('seed migration failed: ' + (signal || code))));
  });
  // A child which fails between request and acknowledgement may close stdin.
  child.stdin.on('error', () => {});
  let previous = [];
  let complete = false;
  const clean = async () => {
    await Promise.all(previous.map(digest => rm(io.payloadPath(digest), { force: true })));
    previous = [];
  };
  try {
    for await (const line of createInterface({ input: child.stdout })) {
      await clean();
      const message = JSON.parse(line);
      if (complete) throw new Error('unexpected output after seed migration result');
      if ('result' in message) {
        complete = true;
        console.log('LEAN_GENERATION_MIGRATION ' + JSON.stringify(message.result));
        continue;
      }
      const { request } = message;
      if (!Array.isArray(request) || request.length !== new Set(request).size
          || request.some(digest => !digests.has(digest))) throw new Error('migration requested an unpinned digest');
      previous = request;
      const verified = [];
      await io.paced(request, 6, 500, async digest => {
        const path = io.payloadPath(digest);
        const key = descriptor.prefix + 'material-' + digest;
        await rm(path, { force: true });
        try {
          if (await io.cache.restoreCache([path], key, []) === key && await io.digestFile(path) === digest) {
            verified.push(digest);
          }
        } catch (error) {
          console.warn('Unavailable legacy material ' + digest + ': ' + error.message);
        }
      });
      child.stdin.write(JSON.stringify(verified.sort()) + '\n');
    }
    const error = await finished;
    if (error) throw error;
    if (!complete) throw new Error('missing seed migration result');
  } finally {
    child.stdin.end();
    if (child.exitCode === null && child.signalCode === null) child.kill();
    await finished;
    await clean();
  }
}
