#!/usr/bin/env python3
"""Real B1 clients through Lake report facets and the canonical artifact consumer.

The command guard bounds infrastructure. No duration is a correctness criterion.
Each fixture source and artifact belongs solely to this invocation.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis
import publication
import native

MODULE = 'Reg.Support.AuricFibUniversalFixture'
SIBLING = 'Reg.Support.AuricFibUniversalSibling'
DATA = 'Reg.Support.AuricFibUniversalData'
PREFIX = 'AuricFibUniversalProduction.'
STATE = ROOT / '.lake/build/lean-inspector'


class UniversalProductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory(prefix='auric-fib-universal.')
        cls.directory = Path(cls.work.name)
        cls.sources = [ROOT / (name.replace('.', '/') + '.lean') for name in (MODULE, SIBLING, DATA)]
        cls.artifacts = [STATE / 'modules' / (name + '.zip') for name in (MODULE, SIBLING)]
        owned_outputs = [Path(str(path) + suffix) for path in cls.artifacts
                         for suffix in ('', '.pending', '.fib-previous')]
        if any(path.exists() for path in cls.sources + owned_outputs):
            raise RuntimeError('universal fixture is already owned; refusing takeover')
        cls.addClassCleanup(cls.cleanup)
        cls.environment = dict(os.environ, GIT_OPTIONAL_LOCKS='0',
            STRATALINT_LEAN_PRODUCER_DLL=str(ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'))
        cls.diagnostics = Path(os.environ.get('FIB_UNIVERSAL_DIAGNOSTICS', cls.directory))
        cls.diagnostics.mkdir(parents=True, exist_ok=True)
        cls.sequence = 0
        cls.source = '''import LeanInformationAuditInterface.Contract.AuricFib
namespace AuricFibUniversalData
private def acquired : Nat := 1
def mass : Nat := acquired
def denominator : Nat := 5
theorem source : type_of% D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=
  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution
end AuricFibUniversalData
'''
        # Keep the dynamically compiled package within Reg's dependency boundary.
        # Reuse the source-owned B1 clients and compile the verification data in
        # the same fixture module, without importing a downstream test package.
        fixture_root = ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/AuricFib'
        native_fixture = (fixture_root / 'CompiledFixture.lean').read_text()
        native_fixture = native_fixture.replace(
            'LeanInformationAuditRegTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled')
        generic_fixture = (fixture_root / 'UniversalFixture.lean').read_text().replace(
            'import LeanInformationAuditRegTests.AuricFib.CompiledFixture\n', '')
        generic_fixture = generic_fixture.replace(
            'LeanInformationAuditRegTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled').replace(
            'LeanInformationAuditRegTests.AuricFib.UniversalFixture', 'AuricFibUniversalProduction')
        generic_fixture = generic_fixture.replace('owner := `AuricFibUniversalProduction',
                                                  'owner := `' + MODULE)
        imports = [line for text in (native_fixture, generic_fixture) for line in text.splitlines()
                   if line.startswith('import ')]
        bodies = ['\n'.join(line for line in text.splitlines() if not line.startswith('import '))
                  for text in (native_fixture, generic_fixture)]
        cls.application = ('import ' + DATA + '\n' + '\n'.join(dict.fromkeys(imports)) + '\n'
                           + '\n'.join(bodies)) + '''
namespace AuricFibUniversalProduction
open LeanInformationAudit.AuricFib.Contract
def changedLaw : Application.{0,0,0,0,0,0} AuricFibUniversalData.source where
  evidence := .native { reconstruction := .exact }
    AuricFibUniversalCompiled.bridge
    (.declared "actual private compiled dependency" {
      nullMass := AuricFibUniversalData.mass, lowMass := 1, highMass := 1,
      endsMass := 1, middleMass := 1, denominator := AuricFibUniversalData.denominator,
      positive := by decide, normalized := by decide }) [] [.seam, .guard, .reply, .atom]
end AuricFibUniversalProduction
'''
        cls.sources[0].write_text(cls.application)
        cls.sources[1].write_text('import LeanInformationAuditInterface.Contract.AuricFib\n'
            'namespace AuricFibUniversalSibling\n'
            'def unchanged : LeanInformationAudit.AuricFib.Contract.Application.{0,0,0,0,0,0} '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution where\n'
            '  evidence := .unsupported "no acquired contract for this adapter"\n'
            'end AuricFibUniversalSibling\n')
        cls.sources[2].write_text(cls.source)
        cls.first = cls.build()

    @classmethod
    def cleanup(cls):
        for path in cls.sources:
            path.unlink(missing_ok=True)
        # Only invocation-owned fixture artifacts are removed; no shared report,
        # protected source-owned module, or other flight's artifact is touched.
        for name in (MODULE, SIBLING, DATA):
            for folder, suffixes in [('modules', ['.zip', '.zip.trace', '.zip.hash',
                                                  '.zip.pending', '.zip.fib-previous']),
                                     ('inputs', ['.json', '.json.sources.json']),
                                     ('judge-inputs', ['.json', '.json.trace', '.json.hash'])]:
                for suffix in suffixes:
                    (STATE / folder / (name + suffix)).unlink(missing_ok=True)
        cls.work.cleanup()

    @classmethod
    def command(cls, targets, *, full=False, expected=0):
        cls.sequence += 1
        log = cls.diagnostics / f'command-{cls.sequence}.log'
        activity = cls.diagnostics / f'activity-{cls.sequence}.jsonl'
        env = dict(cls.environment, STRATALINT_INSPECTOR_ACTIVITY=str(activity),
                   STRATALINT_INSPECTOR_PROFILE='1')
        if full:
            env['LAKE_ARTIFACT_CACHE'] = 'false'
        command = ['bash', 'tools/scripts/worktree/lean-cache-run.sh', 'lake', '-d',
                   'tools/lean-inspector-reg', 'build', *targets]
        with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
            sink.write(json.dumps(dict(command=command, stage='started', full=full, log=str(log))) + '\n')
        process = subprocess.Popen(command, cwd=ROOT, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=300)
        except subprocess.TimeoutExpired as error:
            # End only this invocation's process group; a timed-out compiler
            # must not continue writing after fixture cleanup.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                stdout, stderr = process.communicate()
            log.write_text(stdout + stderr)
            with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
                sink.write(json.dumps(dict(command=command, stage='infrastructure-unresolved',
                                           guard_seconds=300, log=str(log))) + '\n')
            raise RuntimeError(f'INFRASTRUCTURE_UNRESOLVED: 300-second guard: {log}') from error
        result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        log.write_text(result.stdout + result.stderr)
        with (cls.diagnostics / 'commands.jsonl').open('a') as sink:
            sink.write(json.dumps(dict(command=command, exit=result.returncode,
                                       log=str(log), full=full)) + '\n')
        if result.returncode != expected:
            raise AssertionError(f'expected exit {expected}; actual {result.returncode}; {log}\n'
                                 + result.stdout[-4000:] + result.stderr[-4000:])
        cls.counts = {}
        for line in activity.read_text().splitlines() if activity.exists() else []:
            row = json.loads(line)
            cls.counts[row['kind']] = cls.counts.get(row['kind'], 0) + row['count']
        return result

    @classmethod
    def build(cls, *, full=False):
        # Compile changed sources separately from artifact acquisition. Each
        # actual command retains the same infrastructure guard.
        cls.command([MODULE, SIBLING])
        sibling_before = ((hashlib.sha256(cls.artifacts[1].read_bytes()).hexdigest(),
                           cls.artifacts[1].stat().st_mtime_ns)
                          if cls.artifacts[1].exists() else None)
        if full:
            # These two fixture artifacts were created by this invocation.
            for artifact in cls.artifacts:
                for suffix in ('', '.trace', '.hash'):
                    Path(str(artifact) + suffix).unlink(missing_ok=True)
        counts = {}
        for name in (MODULE, SIBLING):
            cls.command([name + ':report'], full=full)
            for kind, count in cls.counts.items():
                counts[kind] = counts.get(kind, 0) + count
        cls.counts = counts
        if not full and sibling_before is not None:
            sibling_after = (hashlib.sha256(cls.artifacts[1].read_bytes()).hexdigest(),
                             cls.artifacts[1].stat().st_mtime_ns)
            if sibling_before != sibling_after:
                raise AssertionError('unaffected sibling module bytes or writing time changed')
        for name, artifact in zip((MODULE, SIBLING), cls.artifacts):
            shutil.copyfile(artifact, cls.diagnostics / f'{cls.sequence}-{name}.zip')
        report = cls.directory / 'raw-lean-report.json'
        with zipfile.ZipFile(cls.artifacts[0]) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                Path(str(report) + suffix).write_bytes(bundle.read('raw-lean-report.json' + suffix))
        rows = publication.validate_rows(report, Path(str(report) + '.materials.zip'))
        cls.report = report
        consumed = fib_analysis.consume(report)
        (cls.diagnostics / f'consumed-{cls.sequence}.json').write_bytes(
            publication.materials.canonical_json(consumed))
        # Exercise the production aggregator on these real module artifacts.
        # Its private fixture input manifest selects only this test's modules;
        # it does not touch the repository's aggregate or full-project custody.
        aggregate_root = cls.directory / 'aggregate-root'
        aggregate_state = aggregate_root / '.lake/build/lean-inspector'
        aggregate_state.mkdir(parents=True, exist_ok=True)
        (aggregate_state / 'inputs.json').write_bytes(publication.materials.canonical_json(dict(
            modules=[MODULE, SIBLING], coordinates=publication.coordinates(ROOT))))
        aggregate = cls.directory / 'aggregate.zip'
        native.aggregate(aggregate_root, aggregate, *cls.artifacts)
        shutil.copyfile(aggregate, cls.diagnostics / f'{cls.sequence}-aggregate.zip')
        destination = cls.directory / 'aggregate-consumer'
        destination.mkdir(exist_ok=True)
        combined = fib_analysis.consume(publication.unpack(aggregate, destination))
        if len(combined['applications']) != len(consumed['applications']) + 1:
            raise AssertionError('aggregate membership or provenance lost a compiled application')
        if len(rows) != 1 or rows[0]['module'] != MODULE:
            raise AssertionError('wrong canonical module artifact')
        return {row['application'].removeprefix(PREFIX): row for row in consumed['applications']
                if row['application'].startswith(PREFIX)}

    def check_program_rebuilding(self, expected):
        # This test owns its temporary edit to the production compiler it tests.
        # Report artifacts and mathematical source are not replaced or patched.
        program = ROOT / 'tools/lean-inspector/LeanInformationAudit/Contract/FibApplications.lean'
        original, metadata = program.read_bytes(), program.stat()
        valid = original + b'\nnamespace LeanInformationAudit.FibApplications\n' \
            b'private def programBuildProbe : Nat := 1\nend LeanInformationAudit.FibApplications\n'
        invalid = valid.replace(b'programBuildProbe : Nat := 1', b'programBuildProbe : Nat := true')
        stamps = [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                  for p in self.artifacts]
        program.write_bytes(valid)
        try:
            self.assertEqual(expected, self.build())
            self.assertEqual(self.counts.get('extract', 0), 0)
            self.assertEqual(stamps, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                     for p in self.artifacts])
            program_log = (self.diagnostics / f'command-{self.sequence - 1}.log').read_text()
            self.assertIn('Built LeanInformationAudit.Contract.FibApplications', program_log)
            program.write_bytes(invalid)
            failed = self.command([MODULE + ':report'], expected=1)
            self.assertIn('FibApplications.lean', failed.stdout + failed.stderr)
            self.assertIn('error:', (failed.stdout + failed.stderr).lower())
            self.assertEqual(stamps, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                     for p in self.artifacts])
        finally:
            if program.read_bytes() not in (valid, invalid):
                raise RuntimeError('program changed outside the fixture; refusing overwrite')
            program.write_bytes(original)
            os.chmod(program, metadata.st_mode)
            os.utime(program, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
            self.command(['leanInspector/reportInspector'])
        self.assertEqual(program.read_bytes(), original)

    def test_compiled_clients_boundaries_and_incremental(self):
        current = self.first
        for key in ('finite', 'constant', 'quotient', 'restricted', 'empty', 'singleton', 'delayed', 'decodedNat'):
            self.assertIsNotNone(current[key]['request'], (key, current[key]))
            self.assertEqual(current[key]['request']['acquisition']['kind'], 'finite',
                             (key, current[key]['request']['acquisition']))
        finite = current['finite']['reading']
        self.assertEqual(finite['arena']['cardinality'], 3)
        self.assertEqual(finite['escape_pairs'], [[0, 2], [2, 0]])
        self.assertEqual(finite['escape_rate'], {'numerator': 2, 'denominator': 6})
        self.assertEqual([row['count'] for row in finite['layered_spectrum']['layers']], [4, 0, 0])
        self.assertEqual([row['count'] for row in current['delayed']['reading']['layered_spectrum']['layers']],
                         [0, 0, 4, 0])
        self.assertEqual(current['constant']['reading']['unique_capture'][0]['count'], 0)
        decoded = current['decodedNat']['reading']['continuation_target']['outputs']
        self.assertTrue(all(row['value'] == {'kind': 'text', 'value': 'seven'} for row in decoded))
        self.assertTrue(all(row['decoded']['literal'] == {'kind': 'nat', 'value': 7}
                            for row in decoded))
        opaque = current['opaqueLayers']['reading']
        self.assertIsNotNone(opaque['source_contract']['binding'])
        self.assertIsNotNone(opaque['kernel']['structural'])
        self.assertIsNone(opaque['kernel']['structural']['additions'])
        self.assertFalse(opaque['kernel']['structural']['available'])
        self.assertIn('fib.plan_layers_unavailable',
                      opaque['disposition']['readings']['escape_rate']['reason'])
        definition = current['specializedDefinition']['reading']['source_contract']['binding']
        self.assertEqual(definition['level_count'], 1)
        self.assertEqual(definition['definition']['name'], PREFIX + 'definedStatement')
        self.assertEqual(definition['occurrence']['universe_arguments'], ['Lean.Level.zero'])
        joined = current['joinedDefinition']['reading']['source_contract']['binding']
        self.assertEqual(joined['level_count'], 2)
        self.assertEqual(joined['definition']['name'], PREFIX + 'definedStatement')
        self.assertEqual(joined['occurrence']['universe_arguments'], ['Lean.Level.zero'] * 2)
        self.assertEqual(current['quotient']['reading']['arena']['presentation']['scope'], 'quotient')
        self.assertEqual(current['restricted']['reading']['arena']['presentation']['scope'], 'restriction')
        for key, count in [('empty', 0), ('singleton', 1)]:
            reading = current[key]['reading']
            self.assertEqual(reading['arena']['cardinality'], count)
            self.assertEqual(reading['escape_pairs'], [])
            self.assertIsNone(reading['escape_rate'])
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'not-applicable')
        for key, levels, binders in [('dependentFamily', 1, 4), ('history', 2, 13)]:
            reading = current[key]['reading']
            binding = reading['source_contract']['binding']
            self.assertEqual((binding['level_count'], binding['telescope_size']), (levels, binders))
            self.assertIsNotNone(reading['kernel']['structural'])
            self.assertIsNone(reading['escape_rate'])
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'unavailable')
        self.assertEqual(current['infinite']['reading']['disposition']['readings']['escape_rate']['kind'],
                         'not-applicable')
        self.assertIsNotNone(current['undecoded']['reading']['source_contract'])
        self.assertIn('fib.acquisition_', current['undecoded']['request']['acquisition']['reason'])
        self.assertEqual(current['wrongOwner']['unavailable_reason'], 'unclassified_form:source.owner')
        self.assertEqual(current['nativeWrongTarget']['unavailable_reason'],
                         'unclassified_form:source.statement_reconstruction')
        native = current['nativeDeclared']['reading']
        self.assertEqual(native['arena']['cardinality'], 5)
        self.assertEqual(native['arena']['ordered_pair_denominator'], 20)
        self.assertEqual(native['atom_readout']['mode_order'], ['null', '2', '5', '25', '3'])
        self.assertEqual(native['layered_spectrum']['partition_count'], 20)
        self.assertEqual(current['nativeAbsent']['reading']['disposition']['readings']['association_coordinate']['kind'],
                         'unknown')
        self.assertEqual(current['nativeZeroCondition']['reading']['disposition']['readings']['conditional_reply_law']['kind'],
                         'not-applicable')
        self.assertEqual(current['nativeRejected']['reading']['disposition']['status'], 'refuted')
        self.assertEqual(current['nativeUnavailableLaw']['reading']['arena']['cardinality'], 5)
        self.assertEqual(current['nativeUnavailableLaw']['reading']['disposition']['readings']['association_coordinate']['kind'],
                         'unavailable')
        missing = fib_analysis.consume(self.report, [PREFIX + 'absentContract'])
        self.assertIn('no acquired FIB', missing['applications'][0]['reading']['disposition']['reason'])
        for row in current.values():
            self.assertFalse(row['reading']['disposition']['is_lean_proof'])
            if row['request'] is not None:
                self.assertLessEqual(set(row['request']['binding']['accepted_axioms']),
                                     {'propext', 'Classical.choice', 'Quot.sound'})
        snapshots = [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns) for p in self.artifacts]
        self.assertEqual(current, self.build())
        self.assertEqual(snapshots, [(hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                                    for p in self.artifacts])
        self.assertEqual(self.counts.get('extract', 0), 0)
        type(self).source = self.source.replace('acquired : Nat := 1', 'acquired : Nat := 2').replace(
            'denominator : Nat := 5', 'denominator : Nat := 6')
        self.sources[2].write_text(self.source)
        changed = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 1)
        self.assertGreaterEqual(self.counts.get('fib-reused', 0), len(current) - 1)
        self.assertNotEqual(current['changedLaw']['input_identity'], changed['changedLaw']['input_identity'])
        self.assertNotEqual(current['changedLaw']['reading']['association_coordinate'],
                            changed['changedLaw']['reading']['association_coordinate'])
        self.assertEqual({k: v for k, v in current.items() if k != 'changedLaw'},
                         {k: v for k, v in changed.items() if k != 'changedLaw'})
        self.assertEqual(snapshots[1], (hashlib.sha256(self.artifacts[1].read_bytes()).hexdigest(),
                                       self.artifacts[1].stat().st_mtime_ns))
        self.assertEqual(changed, self.build(full=True))
        # A source proof dependency changes the actual closure even when the
        # target's type, numerical law and source display strings remain equal.
        type(self).source = self.source.replace(
            'theorem source : type_of%',
            'private theorem sourceDependency : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution\n'
            'theorem source : type_of%').replace(
            'theorem source : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution\n',
            'theorem source : type_of% '
            'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution :=\n'
            '  sourceDependency\n')
        self.sources[2].write_text(self.source)
        source_changed = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 1)
        self.assertNotEqual(changed['changedLaw']['input_identity'], source_changed['changedLaw']['input_identity'])
        self.assertEqual(changed['changedLaw']['reading'], source_changed['changedLaw']['reading'])
        self.assertEqual(source_changed, self.build(full=True))
        # A semantically equal reader still changes its actual compiled input.
        type(self).application = self.application.replace(
            'fun a => rawTransition (rawMachine 0).start a',
            'fun a => rawTransition (rawMachine 0).start (id a)')
        self.sources[0].write_text(self.application)
        reader_changed = self.build()
        affected = {'nativeDeclared', 'nativeAbsent', 'nativeEmpirical', 'nativeApex',
                    'nativeZeroCondition', 'nativeRejected', 'nativeWrongTarget',
                    'nativeParameterized', 'nativeUnavailableLaw', 'changedLaw'}
        self.assertEqual({key for key in source_changed
                          if source_changed[key]['input_identity'] != reader_changed[key]['input_identity']},
                         affected)
        for key in source_changed:
            self.assertEqual(source_changed[key]['reading'], reader_changed[key]['reading'])
        self.assertEqual(reader_changed, self.build(full=True))
        # Real membership and qualification changes; no synthetic partition.
        type(self).application = self.application.replace('def finite := finiteAnalysis',
            'def finite := constantAnalysis').replace('def constant := constantAnalysis\n', '')
        type(self).application += '\nnamespace AuricFibUniversalProduction\n' \
            'def added := Reg.D5.S0.Diagonal.PigeonholeFiber.quotientAnalysis\n' \
            'end AuricFibUniversalProduction\n'
        self.sources[0].write_text(self.application)
        members = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 2)
        self.assertNotIn('constant', members)
        self.assertIn('added', members)
        self.assertEqual(members['finite']['reading']['arena']['cardinality'], 2)
        self.assertEqual(source_changed['history'], members['history'])
        self.assertEqual(members, self.build(full=True))
        type(self).application = self.application.replace('def finite := constantAnalysis\n', '') + '\nnamespace AuricFibUniversalProduction\n' \
            'def finite := wrongOwner\nend AuricFibUniversalProduction\n'
        self.sources[0].write_text(self.application)
        qualified = self.build()
        self.assertEqual(self.counts.get('fib-generated', 0), 0)
        self.assertIsNone(qualified['finite']['request'])
        self.assertEqual(qualified['finite']['unavailable_reason'], 'unclassified_form:source.owner')
        self.assertEqual(members['history'], qualified['history'])
        self.assertEqual(qualified, self.build(full=True))
        self.check_program_rebuilding(qualified)
        (self.diagnostics / 'verified.json').write_text(json.dumps(dict(
            applications=len(members), finite_rate=finite['escape_rate'],
            native_domain=native['atom_readout']['mode_order'],
            full_incremental_equivalence=True, unchanged_module_bytes_and_mtime=True,
            program_rebuilt_without_reading_invalidation=True, program_failure_propagated=True,
            accepted_axioms=sorted(set().union(*(set(row['request']['binding']['accepted_axioms'])
                for row in current.values() if row['request'] is not None))),
            protected_scope='only invocation-owned fixture module artifacts'), indent=2) + '\n')


if __name__ == '__main__':
    unittest.main()
