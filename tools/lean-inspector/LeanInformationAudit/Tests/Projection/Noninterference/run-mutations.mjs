import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

// Run from the repository root after make lean-cache-ensure. Every production
// mutation is restored byte-for-byte before the next build.
const [phase, logDirectory, ...selection] = process.argv.slice(2);
assert(['before', 'after'].includes(phase) && logDirectory,
  'usage: node run-mutations.mjs before|after ABSOLUTE_LOG_DIRECTORY [CASE...]');
assert(path.isAbsolute(logDirectory));

const root = 'tools/lean-inspector/LeanInformationAudit';
const sealFile = `${root}/SealCommand.lean`;
const auditFile = `${root}/Projection/OutputOnlyAudit.lean`;
const fixture = `${root}/Tests/Projection/Noninterference/RealSeal.lean`;
const contract = `${root}/Tests/Projection/Noninterference/Contract.lean`;
const mutableFiles = phase === 'after' ? [sealFile, auditFile] : [];
const originals = new Map(mutableFiles.map(file => [file, fs.readFileSync(file, 'utf8')]));
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

const leanFile = file => ['env', 'lean', '--root=tools/lean-inspector', file];
const fixtureRoot = 'LeanInformationAudit.Tests.Projection.Noninterference.RealSeal';
const diagnostic = (consumer, field) =>
  `IE-C043 KernelProjectionUsedForAdmission consumer=${consumer} field=${field} ` +
  `root=${fixtureRoot} catalog=system`;

if (phase === 'before') {
  const realSeal = run('two-command-contract-red', leanFile(fixture));
  const pin = run('type-contract-red', leanFile(contract));
  results.push({ label: 'two-command-contract-red', fixture_exit: realSeal.status },
    { label: 'type-contract-red', fixture_exit: pin.status });
  assert.notEqual(realSeal.status, 0, 'two-command fixture unexpectedly passed before implementation');
  assert.notEqual(pin.status, 0, 'type contract unexpectedly passed before implementation');
  fs.writeFileSync(path.join(logDirectory, 'before-mutation-results.json'),
    JSON.stringify(results, null, 2) + '\n');
  console.log(JSON.stringify(results, null, 2));
  process.exit(0);
}

const sealCases = [
  ['readFile', 'IO.FS.readFile',
    `  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n`],
  ['prepublicationRead', 'IO.FS.readFile', '  prepublicationRead\n',
    `private def prepublicationRead : CommandElabM Unit := do\n` +
      `  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n\n`],
  ['process', 'IO.Process.output',
    `  let _ ← liftIO <| IO.Process.output { cmd := "/bin/cat", args := #[${JSON.stringify(priorPath)}] }\n`],
  ['stdin', 'IO.getStdin', '  let _ ← liftIO IO.getStdin\n'],
  ['env', 'IO.getEnv', '  let _ ← liftIO <| IO.getEnv "IE_NONINTERFERENCE_INPUT"\n'],
  ['ambientGetRef', 'Lean.MonadRef.getRef', '  let _currentCommand ← getRef\n'],
  ['findOLean', 'Lean.findOLean', '  let _ ← liftIO <| Lean.findOLean `Lean\n'],
  ['readModuleData', 'Lean.readModuleData',
    `  let _ ← liftIO <| Lean.readModuleData ${JSON.stringify(priorPath)}\n`],
  ['readModuleDataParts', 'Lean.readModuleDataParts',
    `  let _ ← liftIO <| Lean.readModuleDataParts #[${JSON.stringify(priorPath)}]\n`],
  ['moduleSetupLoad', 'Lean.ModuleSetup.load',
    `  let _ ← liftIO <| Lean.ModuleSetup.load ${JSON.stringify(priorPath)}\n`],
  ['namespaceProbe', 'IO.FS.readFile', '  _root_.ForeignPublicationProbe\n',
    `def _root_.ForeignPublicationProbe : CommandElabM Unit := do\n` +
      `  let _ ← liftIO <| IO.FS.readFile ${JSON.stringify(priorPath)}\n\n`,
    'ForeignPublicationProbe'],
  ['ownedImplementedBy', 'LeanInformationAudit.overriddenProbe', '  overriddenProbe\n',
    'private def probeImplementation : CommandElabM Unit := pure ()\n' +
      '@[implemented_by probeImplementation]\n' +
      'private def overriddenProbe : CommandElabM Unit := pure ()\n\n'],
  ['ownedExtern', 'LeanInformationAudit.externProbe', '  externProbe\n',
    '@[extern "ie_noninterference_unused_probe"]\n' +
      'private def externProbe : CommandElabM Unit := pure ()\n\n'],
  ['ownedPartial', 'LeanInformationAudit.partialProbe', '  partialProbe false\n',
    'private partial def partialProbe (again : Bool) : CommandElabM Unit := do\n' +
      '  if again then partialProbe false else pure ()\n\n'],
];

const structuralNames = ['pathThreaded', 'allowlistTampered', 'ownedUnsafe', 'exportSetEnv'];
const available = [...sealCases.map(row => row[0]), ...structuralNames,
  'unsealedExport', 'positiveControl'];
assert(selection.every(label => available.includes(label)), 'unknown mutation selection');
const selected = label => selection.length === 0 || selection.includes(label);

try {
  for (const [label, capability, injected, helper = '', consumerOverride] of sealCases) {
    if (!selected(label)) continue;
    const source = originals.get(sealFile);
    let mutated = changeOnce(source, '  let baseEnv ← getEnv\n',
      injected + '  let baseEnv ← getEnv\n');
    if (helper) {
      mutated = changeOnce(mutated, 'def prepareSealPublication',
        helper + 'def prepareSealPublication');
    }
    const consumer = consumerOverride ?? (helper ?
      `LeanInformationAudit.${label === 'prepublicationRead' ? 'prepublicationRead' :
        label === 'namespaceProbe' ? 'ForeignPublicationProbe' :
        label === 'ownedImplementedBy' ? 'overriddenProbe' :
        label === 'ownedExtern' ? 'externProbe' : 'partialProbe'}` :
      'LeanInformationAudit.prepareSealPublication');
    const expected = diagnostic(consumer, `capability:${capability}`);
    replace(sealFile, source, mutated);
    try {
      const build = run(`${label}-build`, ['build', 'LeanInformationAudit.SealCommand']);
      assert.equal(build.status, 0, build.stdout + build.stderr);
      const output = path.join(logDirectory, `${label}-exports`);
      assert(!fs.existsSync(output), `use a fresh log directory: ${output}`);
      const test = run(label, leanFile(fixture), {
        IE_EXPECT_SEAL_REJECTION: expected, IE_PROJECTION_OUTPUT_DIR: output,
      });
      results.push({ label, capability, expected, build_exit: build.status,
        fixture_exit: test.status, expected_fixture_exit: 0 });
      assert.equal(test.status, 0, test.stdout + test.stderr);
      assert(test.stdout.includes(`RealSeal seal rejected before publication and writes: ${expected}`));
    } finally {
      replace(sealFile, mutated, source);
    }
  }

  const structural = [
    ['pathThreaded', sealFile, source => changeOnce(source,
      'def prepareSealPublication : CommandElabM Unit',
      'def prepareSealPublication (_path : System.FilePath := "") : CommandElabM Unit'), null],
    ['allowlistTampered', auditFile, source => changeOnce(source,
      'def sealIOAllowlist : List Name := [``Lean.logInfo]',
      'def sealIOAllowlist : List Name := [``Lean.logInfo, ``IO.FS.readFile]'), null],
    ['ownedUnsafe', sealFile, source => {
      source = changeOnce(source,
        'def prepareSealPublication', 'unsafe def prepareSealPublication');
      source = changeOnce(source,
        'private def elabSealInformationTheory',
        'private unsafe def elabSealInformationTheory');
      return changeOnce(source,
        '| .ok () => elabSealInformationTheory stx',
        '| .ok () => unsafe elabSealInformationTheory stx');
    },
      diagnostic('LeanInformationAudit.prepareSealPublication',
        'capability:LeanInformationAudit.prepareSealPublication')],
    ['exportSetEnv', sealFile, source => changeOnce(source,
      '  let env ← getEnv\n', '  setEnv (← getEnv)\n  let env ← getEnv\n'),
      diagnostic('LeanInformationAudit.prepareInformationAnalysisExport', 'capability:Lean.setEnv')],
  ];
  for (const [label, file, mutate, expected] of structural) {
    if (!selected(label)) continue;
    const source = originals.get(file);
    const mutated = mutate(source);
    replace(file, source, mutated);
    try {
      const build = run(`${label}-build`, ['build', 'LeanInformationAudit.SealCommand']);
      assert.equal(build.status, 0, build.stdout + build.stderr);
      const output = path.join(logDirectory, `${label}-exports`);
      const test = run(label, leanFile(expected ? fixture : contract), expected ? {
        [label === 'exportSetEnv' ? 'IE_EXPECT_EXPORT_REJECTION' : 'IE_EXPECT_SEAL_REJECTION']:
          expected,
        IE_PROJECTION_OUTPUT_DIR: output,
      } : {});
      results.push({ label, expected, build_exit: build.status, fixture_exit: test.status,
        expected_fixture_exit: expected ? 0 : 1 });
      assert.equal(test.status, expected ? 0 : 1, test.stdout + test.stderr);
      if (expected) assert(test.stdout.includes(expected));
      else assert(test.stdout.includes(label === 'pathThreaded' ? 'Type mismatch' :
        'did not evaluate to `true`'));
    } finally {
      replace(file, mutated, source);
    }
  }
} finally {
  for (const [file, original] of originals) {
    assert.equal(fs.readFileSync(file, 'utf8'), original, `${file} was not restored`);
  }
  const restored = run('restored-build', ['build', 'LeanInformationAudit.SealCommand']);
  results.push({ label: 'restored-build', exit: restored.status });
  fs.writeFileSync(path.join(logDirectory, 'after-mutation-results.json'),
    JSON.stringify(results, null, 2) + '\n');
  assert.equal(restored.status, 0, restored.stdout + restored.stderr);
}

if (selected('unsealedExport')) {
  const output = path.join(logDirectory, 'unsealed-export');
  const test = run('unsealed-export', leanFile(fixture), {
    IE_EXPORT_BEFORE_SEAL: '1', IE_PROJECTION_OUTPUT_DIR: output,
  });
  assert.equal(test.status, 0, test.stdout + test.stderr);
  assert(test.stdout.includes('RealSeal rejected export before seal: IE-C044 UnsealedAnalysisExport'));
  results.push({ label: 'unsealedExport', fixture_exit: test.status });
}

if (selected('positiveControl')) {
  const output = path.join(logDirectory, 'positive-exports');
  const positive = run('positive-real-seal', leanFile(fixture), {
    IE_PROJECTION_OUTPUT_DIR: output,
  });
  assert.equal(positive.status, 0, positive.stdout + positive.stderr);
  assert(positive.stdout.includes('RealSeal sealed once and exported byte-identical artifacts twice'));
  const pin = run('positive-contract', leanFile(contract));
  assert.equal(pin.status, 0, pin.stdout + pin.stderr);
  results.push({ label: 'positiveControl', fixture_exit: positive.status,
    contract_exit: pin.status });
}

fs.writeFileSync(path.join(logDirectory, 'after-mutation-results.json'),
  JSON.stringify(results, null, 2) + '\n');
console.log(JSON.stringify(results, null, 2));
