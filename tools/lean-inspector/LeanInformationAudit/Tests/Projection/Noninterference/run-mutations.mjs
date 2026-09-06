import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

// Run from the repository root, after make lean-cache-ensure.
// Each mutation is restored byte-for-byte before the next one is built.
const [phase, logDirectory, ...selection] = process.argv.slice(2);
assert(['before', 'after'].includes(phase) && logDirectory,
  'usage: node run-mutations.mjs before|after ABSOLUTE_LOG_DIRECTORY [CASE...]');
assert(path.isAbsolute(logDirectory));
const root = 'tools/lean-inspector/LeanInformationAudit';
const sealFile = `${root}/SealCommand.lean`;
const auditFile = `${root}/OutputOnlyAudit.lean`;
const fixture = `${root}/Tests/Projection/Noninterference/RealSeal.lean`;
const contract = `${root}/Tests/Projection/Noninterference/Contract.lean`;
const originals = new Map([sealFile, auditFile].map(file => [file, fs.readFileSync(file, 'utf8')]));
fs.mkdirSync(logDirectory, { recursive: true });
const priorPath = path.join(logDirectory, 'prior-analysis.json');
fs.writeFileSync(priorPath, '{"nodes":[],"prior_artifact":true}\n');
const results = [];

function replace(file, oldText, newText) {
  assert(oldText !== newText);
  const patch = `*** Begin Patch\n*** Update File: ${file}\n@@\n` +
    oldText.trimEnd().split('\n').map(line => `-${line}\n`).join('') +
    newText.trimEnd().split('\n').map(line => `+${line}\n`).join('') + '*** End Patch\n';
  const result = spawnSync('apply_patch', [patch], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stdout + result.stderr);
}

function changeOnce(source, anchor, replacement) {
  assert.equal(source.split(anchor).length, 2, `ambiguous mutation anchor: ${anchor}`);
  return source.replace(anchor, replacement);
}

function run(label, args, env = {}) {
  const result = spawnSync('lake', args, {
    encoding: 'utf8', env: { ...process.env, ...env }, maxBuffer: 64 * 1024 * 1024,
  });
  fs.writeFileSync(path.join(logDirectory, `${phase}-${label}.log`),
    result.stdout + result.stderr + `\nEXIT=${result.status}\n`);
  assert.equal(result.signal, null, `infrastructure signal: ${result.signal}`);
  return result;
}

const prefix = 'IE-C043 KernelProjectionUsedForAdmission';
const orderError = `${prefix} consumer=LeanInformationAudit.elabSealInformationTheory ` +
  'field=publication-order root=LeanInformationAudit.Tests.Projection.Noninterference.RealSeal catalog=system';
const cases = [
  ['readFile', 'IO.FS.readFile', `  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n`],
  ['prepublicationRead', 'IO.FS.readFile', '  prepublicationRead\n',
    `private def prepublicationRead : CommandElabM Unit := do\n  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n\n`],
  ['priorArtifact', 'IO.FS.readFile', '  priorArtifactProbe\n',
    `private def priorArtifactProbe : CommandElabM Unit := do\n  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n\n`],
  ['process', 'IO.Process.output', `  let _ ← liftIO <| IO.Process.output { cmd := "/bin/cat", args := #[${JSON.stringify(priorPath)}] }\n`],
  ['stdin', 'IO.getStdin', '  let _ ← liftIO IO.getStdin\n'],
  ['env', 'IO.getEnv', '  let _ ← liftIO <| IO.getEnv "IE_NONINTERFERENCE_INPUT"\n'],
];
if (phase === 'after') cases.push(
  ['namespaceProbe', 'IO.FS.readFile', '  _root_.ForeignPublicationProbe\n',
    `def _root_.ForeignPublicationProbe : CommandElabM Unit := do\n  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n\n`,
    'ForeignPublicationProbe'],
  ['ownedImplementedBy', 'LeanInformationAudit.overriddenProbe', '  overriddenProbe\n',
    'private def probeImplementation : CommandElabM Unit := pure ()\n' +
    '@[implemented_by probeImplementation]\nprivate def overriddenProbe : CommandElabM Unit := pure ()\n\n',
    'LeanInformationAudit.overriddenProbe'],
  ['ownedExtern', 'LeanInformationAudit.externProbe', '  externProbe\n',
    '@[extern "ie_noninterference_unused_probe"]\nprivate def externProbe : CommandElabM Unit := pure ()\n\n',
    'LeanInformationAudit.externProbe'],
  ['ownedPartial', 'LeanInformationAudit.partialProbe', '  partialProbe false\n',
    'private partial def partialProbe (again : Bool) : CommandElabM Unit := do\n' +
    '  if again then partialProbe false else pure ()\n\n',
    'LeanInformationAudit.partialProbe'],
);
const structuralNames = ['writeBeforePublication', 'mutateAfterWriter', 'pathThreaded',
  'allowlistTampered', 'ownedUnsafe'];
const available = [...cases.map(row => row[0]), ...(phase === 'after' ? structuralNames : [])];
assert(selection.every(label => available.includes(label)), 'unknown mutation selection');
const selected = label => selection.length === 0 || selection.includes(label);
const leanFile = file => ['env', 'lean', '--root=tools/lean-inspector', file];

try {
  for (const [label, capability, injected, helper = '', consumerOverride] of cases) {
    if (!selected(label)) continue;
    const source = originals.get(sealFile);
    let mutated = changeOnce(source, '  let baseEnv ← getEnv\n', injected + '  let baseEnv ← getEnv\n');
    if (helper) {
      const anchor = phase === 'before' ? 'private def prepareSealPublication' : 'def prepareSealPublication';
      mutated = changeOnce(mutated, anchor, helper + anchor);
    }
    const consumer = label === 'prepublicationRead' ? 'prepublicationRead' :
      label === 'priorArtifact' ? 'priorArtifactProbe' : 'prepareSealPublication';
    const expected = `${prefix} consumer=${consumerOverride ?? `LeanInformationAudit.${consumer}`} capability=${capability}`;
    replace(sealFile, source, mutated);
    try {
      const build = run(`${label}-build`, ['build', 'LeanInformationAudit.SealCommand']);
      assert.equal(build.status, 0, build.stdout + build.stderr);
      const output = path.join(logDirectory, `${phase}-${label}-exports`);
      assert(!fs.existsSync(output), `use a fresh log directory: ${output}`);
      const test = run(label, leanFile(fixture), {
        IE_EXPECT_SEAL_REJECTION: expected, IE_PROJECTION_OUTPUT_DIR: output,
      });
      const wantedExit = phase === 'before' ? 1 : 0;
      results.push({ label, capability, expected, build_exit: build.status, fixture_exit: test.status,
        expected_fixture_exit: wantedExit });
      assert.equal(test.status, wantedExit, test.stdout + test.stderr);
      if (phase === 'before') assert(test.stdout.includes('RealSeal expected rejection'));
      else assert(test.stdout.includes(`RealSeal rejected before publication and writes: ${expected}`));
    } finally {
      replace(sealFile, mutated, source);
    }
  }
  if (phase === 'after') {
    const structural = [
      ['writeBeforePublication', sealFile, source => changeOnce(source,
        '  let baseEnv ← getEnv\n',
        `  liftIO <| IO.FS.writeFile ${JSON.stringify(path.join(logDirectory, 'forbidden-early-write'))} "early"\n  let baseEnv ← getEnv\n`), orderError],
      ['mutateAfterWriter', auditFile, source => changeOnce(source,
        '  liftIO <| writeSealArtifacts stx plan\n',
        '  liftIO <| writeSealArtifacts stx plan\n  setEnv (← getEnv)\n'), orderError],
      ['pathThreaded', sealFile, source => changeOnce(source,
        'def prepareSealPublication (requested : List ArtifactKind)',
        'def prepareSealPublication (requested : List ArtifactKind) (_path : System.FilePath := "")'), null],
      ['allowlistTampered', auditFile, source => changeOnce(source,
        '[``IO.FS.writeFile, ``Lean.logInfo]',
        '[``IO.FS.writeFile, ``Lean.logInfo, ``IO.FS.readFile]'), null],
      ['ownedUnsafe', sealFile, source => {
        source = changeOnce(source, 'def prepareSealPublication', 'unsafe def prepareSealPublication');
        source = changeOnce(source, 'private def elabSealInformationTheory',
          'private unsafe def elabSealInformationTheory');
        return changeOnce(source, '| .ok () => elabSealInformationTheory stx',
          '| .ok () => unsafe elabSealInformationTheory stx');
      }, `${prefix} consumer=LeanInformationAudit.prepareSealPublication capability=LeanInformationAudit.prepareSealPublication`],
    ];
    for (const [label, file, mutate, expected] of structural) {
      if (!selected(label)) continue;
      const source = originals.get(file);
      const mutated = mutate(source);
      replace(file, source, mutated);
      try {
        const build = run(`${label}-build`, ['build', 'LeanInformationAudit.SealCommand']);
        assert.equal(build.status, 0, build.stdout + build.stderr);
        const output = path.join(logDirectory, `${phase}-${label}-exports`);
        const test = run(label, leanFile(expected ? fixture : contract), expected ? {
          IE_EXPECT_SEAL_REJECTION: expected, IE_PROJECTION_OUTPUT_DIR: output,
        } : {});
        results.push({ label, expected, build_exit: build.status, fixture_exit: test.status,
          expected_fixture_exit: expected ? 0 : 1 });
        assert.equal(test.status, expected ? 0 : 1, test.stdout + test.stderr);
        if (expected) assert(test.stdout.includes('RealSeal rejected before publication and writes:'));
        else assert(test.stdout.includes(label === 'pathThreaded' ? 'Type mismatch' :
          'did not evaluate to `true`'));
        if (label === 'pathThreaded') {
          const seal = run(`${label}-real-seal`, leanFile(fixture), {
            IE_EXPECT_SEAL_REJECTION: orderError, IE_PROJECTION_OUTPUT_DIR: output,
          });
          assert.equal(seal.status, 0, seal.stdout + seal.stderr);
          results.push({ label: 'pathThreaded-real-seal', expected: orderError, fixture_exit: seal.status });
        }
        assert(!fs.existsSync(path.join(logDirectory, 'forbidden-early-write')));
      } finally {
        replace(file, mutated, source);
      }
    }
  }
} finally {
  for (const [file, original] of originals) assert.equal(fs.readFileSync(file, 'utf8'), original);
  const restored = run('restored-build', ['build', 'LeanInformationAudit.SealCommand']);
  results.push({ label: 'restored-build', exit: restored.status });
  fs.writeFileSync(path.join(logDirectory, `${phase}-mutation-results.json`), JSON.stringify(results, null, 2) + '\n');
  assert.equal(restored.status, 0, restored.stdout + restored.stderr);
}
if (phase === 'after' && selection.length === 0) {
  const positive = run('positive-real-seal', leanFile(fixture), {
    IE_PROJECTION_OUTPUT_DIR: path.join(logDirectory, 'positive-exports'),
  });
  assert.equal(positive.status, 0, positive.stdout + positive.stderr);
  assert(positive.stdout.includes('RealSeal published and wrote all three artifacts'));
  const pin = run('positive-contract', leanFile(contract));
  assert.equal(pin.status, 0, pin.stdout + pin.stderr);
  results.push({ label: 'positive-real-seal', fixture_exit: positive.status },
    { label: 'positive-contract', fixture_exit: pin.status });
  fs.writeFileSync(path.join(logDirectory, `${phase}-mutation-results.json`), JSON.stringify(results, null, 2) + '\n');
}
console.log(JSON.stringify(results, null, 2));
