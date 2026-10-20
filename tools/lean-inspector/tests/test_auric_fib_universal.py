#!/usr/bin/env python3
"""One compiled optional-analysis fixture through the production consumer.

Lake builds the fixture once. Source, finite and non-finite boundaries share
that result; ordinary native reuse tests own incremental build behavior.
"""
import os
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis
import materials
import publication

MODULE = 'Reg.Support.AuricFibUniversalFixture'
PLAIN_MODULE = 'D5.S0.Diagonal.PigeonholeFiber'
PREFIX = 'AuricFibUniversalProduction.'
STATE = ROOT / '.lake/build/lean-inspector'


def cleanup_module(module):
    for folder in ('modules', 'inputs', 'judge-inputs'):
        for path in (STATE / folder).glob(module + '.*'):
            path.unlink()
    owner, _, basename = module.rpartition('.')
    for folder in ('lib/lean', 'ir'):
        directory = ROOT / '.lake/build/reg' / folder / owner.replace('.', '/')
        for path in directory.glob(basename + '.*'):
            path.unlink()


class UniversalProductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory(prefix='auric-fib-universal.')
        cls.directory = Path(cls.work.name)
        cls.source = ROOT / (MODULE.replace('.', '/') + '.lean')
        if cls.source.exists():
            cls.work.cleanup()
            raise RuntimeError('universal fixture is already owned; refusing takeover')
        cls.addClassCleanup(cls.cleanup)
        fixture_root = ROOT / 'tools/lean-inspector/LeanInformationAuditFibTests/AuricFib'
        native_fixture = (fixture_root / 'CompiledFixture.lean').read_text().replace(
            'LeanInformationAuditFibTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled')
        generic_fixture = (fixture_root / 'UniversalFixture.lean').read_text().replace(
            'import LeanInformationAuditFibTests.AuricFib.CompiledFixture\n', '')
        generic_fixture = generic_fixture.replace(
            'LeanInformationAuditFibTests.AuricFib.CompiledFixture', 'AuricFibUniversalCompiled').replace(
            'LeanInformationAuditFibTests.AuricFib.UniversalFixture', 'AuricFibUniversalProduction')
        generic_fixture = generic_fixture.replace('owner := `AuricFibUniversalProduction',
                                                  'owner := `' + MODULE)
        law_fixture = (fixture_root / 'LawFixture.lean').read_text().replace(
            'LeanInformationAuditFibTests.AuricFib.LawFixture', 'AuricFibUniversalProduction.Law').replace(
            'LawFixture.', 'AuricFibUniversalProduction.Law.')
        law_fixture = law_fixture.replace('owner := `AuricFibUniversalProduction.Law', 'owner := `' + MODULE)
        imports = [line for text in (native_fixture, generic_fixture, law_fixture) for line in text.splitlines()
                   if line.startswith('import ')]
        bodies = ['\n'.join(line for line in text.splitlines() if not line.startswith('import '))
                  for text in (native_fixture, generic_fixture, law_fixture)]
        cls.source.write_text('\n'.join(dict.fromkeys(imports)) + '\n' + '\n'.join(bodies) + '''
namespace AuricFibUniversalProduction
open LeanInformationAudit.Analysis LeanInformationAudit.AuricFib.Contract
universe u
def dataFree : Application absentContract where
  evidence := .typed dataFreeClient
def terminalCounts : Application absentContract where
  evidence := .typed {
    source := dataFreeSource, plan := dataFreeClient.plan,
    acquisition := .finite (Domain.fiber dataFreeSource ()) terminalPresentation }
def dataFreeBad : Application absentContract where
  evidence := .typed {
    source := unobservedMismatch
    plan := { task := (), initial := [], additions := [] }
    acquisition := .unavailable "no finite presentation requested" }
def unobservedFamily : Application (@D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber.{u}) where
  evidence := .typed {
    source := Source.unobserved _ `D5.S0.Diagonal.PigeonholeFiber
    plan := { task := (), initial := [], additions := [[], [()]] }
    acquisition := .unavailable "no finite presentation requested" }
end AuricFibUniversalProduction
''')
        subprocess.run(['bash', 'tools/scripts/worktree/lean-cache-run.sh', 'lake', '-d',
            'tools/lean-inspector-reg', 'build', 'leanInspector/reportInspector',
            MODULE + ':report', PLAIN_MODULE + ':report'],
            cwd=ROOT, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0'), check=True)
        cls.report = cls.directory / 'raw-lean-report.json'
        with zipfile.ZipFile(STATE / 'modules' / (MODULE + '.zip')) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                Path(str(cls.report) + suffix).write_bytes(bundle.read('raw-lean-report.json' + suffix))
        consumed = fib_analysis.consume(cls.report)
        if set(consumed) != {'applications', 'authority'}:
            raise AssertionError('FIB export must have no independent version field')
        with zipfile.ZipFile(STATE / 'modules' / (PLAIN_MODULE + '.zip')) as bundle:
            plain = json.loads(bundle.read('raw-lean-report.json'))
            if 'fib_analysis' in plain['modules'][0]:
                raise AssertionError('nonparticipants must not acquire a FIB partition')
        raw = json.loads(cls.report.read_text())
        if raw['schema'] != 'stratalint-raw-lean-report-v3':
            raise AssertionError('parent report schema must remain v3')
        if set(raw['modules'][0]['fib_analysis']) != {'applications'}:
            raise AssertionError('FIB partition must have no independent version field')
        cls.first = {row['application'].removeprefix(PREFIX): row for row in consumed['applications']
                     if row['application'].startswith(PREFIX)}

    @classmethod
    def cleanup(cls):
        cls.source.unlink(missing_ok=True)
        cleanup_module(MODULE)
        cls.work.cleanup()

    def test_compiled_clients_boundaries(self):
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
        missing = fib_analysis.consume(self.report, ['AuricFibUniversalCompiled.noise'])
        self.assertIn('no acquired FIB', missing['applications'][0]['reading']['disposition']['reason'])
        for row in current.values():
            self.assertFalse(row['reading']['disposition']['is_lean_proof'])
            if row['request'] is not None:
                self.assertLessEqual(set(row['request']['binding']['accepted_axioms']),
                                     {'propext', 'Classical.choice', 'Quot.sound'})

    def test_law_family_source_and_golden_point(self):
        from fractions import Fraction
        def q(value):
            return Fraction(int(value['numerator']), int(value['denominator']))
        row = self.first['Law.star']
        self.assertIsNotNone(row['request'], row)
        reading = row['reading']
        self.assertEqual(row['request']['arena'], 'law-family')
        self.assertEqual(reading['source_contract']['binding']['occurrence']['source_name'], PREFIX + 'Law.target')
        self.assertEqual([Fraction(x) for x in row['request']['point']['law']],
                         [Fraction(n, 8) for n in (4, 1, 1, 1, 1)])
        for name, value in dict(X=Fraction(1,4), Y=Fraction(1,4), Z=Fraction(1,8), r=Fraction(7,8)).items():
            self.assertEqual(q(reading['pyramid_coordinates'][name]), value)
        association = reading['association_coordinate']
        self.assertEqual(q(association['kappa']), Fraction(1,8))
        self.assertEqual(q(association['delta']), Fraction(3,64))
        self.assertEqual(q(association['product_completion'][3]), Fraction(1,14))
        self.assertEqual(q(reading['residuals']['fiber_width']), Fraction(1,4))
        self.assertEqual(association['family_capture']['status'], 'unknown')
        star = self.first['Law.Star.analysis']
        self.assertIsNotNone(star['request'], star)
        self.assertEqual(star['request']['point']['law'], row['request']['point']['law'])
        self.assertEqual(star['reading']['pyramid_coordinates'], reading['pyramid_coordinates'])
        self.assertEqual(star['reading']['association_coordinate']['delta'], association['delta'])
        self.assertEqual([p['atom'] for p in star['request']['law_family']['mode_pairing']],
                         [4, 0, 2, 3, 1])
        self.assertEqual(self.first['Law.collapsed']['reading']['association_coordinate']['family_capture']['status'], 'collapsed')
        self.assertFalse(self.first['Law.collapsed']['request']['facts'][0]['uses_target_results'])
        self.assertTrue(self.first['Law.usesTarget']['request']['facts'][0]['uses_target_results'])
        self.assertTrue(self.first['Law.usesOpaqueTarget']['request']['facts'][0]['uses_target_results'])
        for name in ('seam_readout', 'guard', 'reply', 'R_guard', 'native_continuation'):
            self.assertEqual(reading['disposition']['readings'][name]['kind'], 'not-applicable')
        self.assertIsNone(reading['seam_readout'])
        self.assertNotIn('R_guard', reading['residuals'])
        self.assertNotIn('J_f', reading['residuals'])
        signed = self.first['Law.taskSigned']
        self.assertIsNotNone(signed['request'], signed)
        self.assertEqual(signed['request']['task'], ['-1/2', '2/2', '-3/2', '4/2', '5/2'])
        self.assertEqual(q(signed['reading']['residuals']['J_f']), 2)
        zero = self.first['Law.taskZero']['reading']
        self.assertEqual(q(zero['residuals']['J_f']), 0)
        self.assertEqual(zero['continuation_target']['family_capture'], 'collapsed')
        infinite = self.first['Law.infinite']['reading']
        for name in ('escape_pairs', 'escape_rate', 'unique_capture'):
            self.assertEqual(infinite['disposition']['readings'][name]['kind'], 'not-applicable')
        self.assertEqual(infinite['disposition']['readings']['family_capture']['kind'], 'unknown')
        self.assertEqual(infinite['association_coordinate']['family_capture']['status'], 'unknown')
        strict = self.first['Law.Separation.strict']['reading']
        self.assertEqual(strict['association_coordinate']['family_capture']['status'], 'strict')
        self.assertEqual(strict['continuation_target']['family_capture'], 'strict')
        self.assertEqual(strict['association_coordinate']['family_capture']['inheritance'], 'unassessed')
        simplex = self.first['Law.Simplex.strict']['reading']
        self.assertEqual(simplex['association_coordinate']['family_capture']['inheritance'], 'simplex-inherited')
        self.assertEqual([f['kind'] for f in self.first['Law.signed']['request']['facts']],
                         ['deltaSign', 'positiveWidth'])
        for name in ('Law.signed', 'Law.Separation.strict', 'Law.Simplex.strict'):
            self.assertTrue(all(not fact['uses_target_results']
                                for fact in self.first[name]['request']['facts']), name)
        unavailable = self.first['Law.unavailablePoint']
        self.assertIsNotNone(unavailable['request'], unavailable)
        self.assertEqual(unavailable['reading']['disposition']['readings']['pyramid_coordinates']['kind'],
                         'unavailable')
        self.assertEqual(unavailable['reading']['association_coordinate']['family_capture']['status'],
                         'collapsed')
        self.assertEqual(unavailable['reading']['disposition']['readings']['source_contract']['kind'],
                         'available')
        missing = self.first['Law.noPoint']['reading']
        self.assertIsNone(missing['pyramid_coordinates'])
        self.assertEqual(missing['association_coordinate']['family_capture']['status'], 'unknown')

    def test_compiled_verdicts_are_lean_projections(self):
        laws = [row for row in self.first.values()
                if row['request'] is not None and row['request'].get('arena') == 'law-family']
        for row in laws:
            compiled = row['request']['compiled_capture']
            reading = row['reading']
            self.assertEqual(reading['association_coordinate']['family_capture'], compiled['family'])
            self.assertEqual(reading['layered_spectrum']['family_capture'], compiled['family'])
            if row['request']['task'] is not None:
                self.assertEqual(reading['continuation_target']['family_capture'], compiled['task'])
                self.assertEqual(reading['continuation_target']['uses_delta'], compiled['uses_delta'])
        # Replaying JSON at the public arithmetic entry acquires no theorem.
        strict = self.first['Law.Separation.strict']['request']
        result = subprocess.run([str(ROOT / '.lake/build/lean-inspector/reg/bin/auricFibAnalysis')],
                                input=json.dumps(strict), text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        public = json.loads(result.stdout)
        self.assertEqual(public['association_coordinate']['family_capture']['status'], 'unknown')
        self.assertEqual(public['disposition']['readings']['source_contract']['kind'], 'unavailable')

    def test_data_free_ingress(self):
        current = self.first
        for name, target, telescope, levels in (
                ('dataFree', PREFIX + 'absentContract', 0, 0),
                ('unobservedFamily', 'D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber', 4, 1)):
            row = current[name]
            self.assertIsNotNone(row['request'], row)
            reading = row['reading']
            binding = reading['source_contract']['binding']
            self.assertEqual(binding['occurrence']['source_name'], target)
            self.assertEqual(binding['occurrence']['original_type']['identity'], row['target_type_identity'])
            self.assertEqual(binding['telescope_size'], telescope)
            self.assertEqual(binding['level_count'], levels)
            self.assertEqual(binding['coordinates'], [])
            self.assertEqual(binding['readouts'], [])
            self.assertIn('terminal model', binding['source_correspondence'])
            self.assertEqual(reading['disposition']['readings']['source_contract']['kind'], 'available')
            self.assertEqual(reading['disposition']['readings']['escape_rate']['kind'], 'unavailable')
            self.assertIsNone(reading['escape_rate'])
            self.assertIsNone(reading['pyramid_coordinates'])
            self.assertLessEqual(set(binding['accepted_axioms']), {'propext', 'Classical.choice', 'Quot.sound'})
            selected = fib_analysis.consume(self.report, [target])
            self.assertIn(row, selected['applications'])
        terminal = current['terminalCounts']
        self.assertIsNotNone(terminal['request'])
        self.assertEqual(terminal['request']['acquisition']['kind'], 'unavailable')
        self.assertIn('fib.unobserved_source_domain_unacquired', terminal['request']['acquisition']['reason'])
        self.assertIsNone(terminal['reading']['escape_rate'])
        self.assertIsNone(terminal['reading']['arena']['cardinality'])
        self.assertEqual(terminal['reading']['disposition']['readings']['source_contract']['kind'], 'available')
        self.assertEqual(current['dataFree']['request']['plan']['additions'], [[], [0], []])
        self.assertEqual(current['dataFree']['request']['binding']['occurrence']['original_type']['head'], 'True')
        self.assertIsNone(current['dataFreeBad']['request'])
        self.assertEqual(current['dataFreeBad']['unavailable_reason'], 'fib.unobserved_model_mismatch')

    def test_production_leaf_reuse_and_fail_closed_boundaries(self):
        previous = STATE / 'modules' / (MODULE + '.zip')
        row = json.loads(self.report.read_text())['modules'][0]
        for leaf in row['fib_analysis']['applications']:
            leaf['reading'] = None
        reused = fib_analysis.produce(row, previous, '')
        self.assertEqual(reused['generated'], 0)
        self.assertEqual(reused['reused'], len(row['fib_analysis']['applications']))
        leaf = next(x for x in row['fib_analysis']['applications'] if x['request'] is not None)
        leaf['input_identity'] = 'f' * 64
        with self.assertRaisesRegex(ValueError, 'fib.analysis_program_missing'):
            fib_analysis.produce(copy.deepcopy(row), previous, '')
        stats = fib_analysis.produce(row, previous, ROOT / 'tools/scripts/auric-fib-analysis.sh')
        self.assertEqual(stats['generated'], 1)
        self.assertEqual(stats['analysis-invocations'], 1)
        self.assertGreater(stats['analysis-ns'], 0)
        malformed = self.directory / 'uncustodied.zip'
        with zipfile.ZipFile(malformed, 'w') as bundle:
            bundle.writestr('raw-lean-report.json', json.dumps(dict(schema='unknown', modules=[row])))
        with self.assertRaisesRegex(ValueError, 'fib.previous_module_binding'):
            fib_analysis.produce(row, malformed, '')

    def test_full_and_incremental_law_readings_agree(self):
        original = json.loads(self.report.read_text())['modules'][0]
        full = copy.deepcopy(original)
        stats = fib_analysis.produce(full, self.directory / 'no-prior-artifact.zip',
            ROOT / '.lake/build/lean-inspector/reg/bin/auricFibAnalysis')
        self.assertEqual(stats['reused'], 0)
        self.assertEqual(full['fib_analysis'], original['fib_analysis'])
        incremental = copy.deepcopy(original)
        previous = STATE / 'modules' / (MODULE + '.zip')
        stats = fib_analysis.produce(incremental, previous, '')
        self.assertEqual(stats['generated'], 0)
        self.assertEqual(incremental['fib_analysis'], full['fib_analysis'])

    def test_report_consumer_compares_complete_inputs_and_runs_once(self):
        original = json.loads(self.report.read_text())['modules'][0]
        origin = json.loads(Path(str(self.report) + '.provenance.json').read_text())
        def save(name, row):
            report = self.directory / (name + '.json')
            report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=[row])))
            current_origin = copy.deepcopy(origin)
            current_origin['report_sha256'] = hashlib.sha256(report.read_bytes()).hexdigest()
            Path(str(report) + '.provenance.json').write_text(json.dumps(current_origin))
            return report
        before = save('before', original)
        same = copy.deepcopy(original)
        same['source_sha256'] = 'f' * 64
        same = save('same-inputs', same)
        empty = copy.deepcopy(original)
        empty.pop('fib_analysis')
        empty_report = save('no-applications', empty)
        empty_origin_path = Path(str(empty_report) + '.provenance.json')
        empty_origin = json.loads(empty_origin_path.read_text())
        empty_origin['input_projection']['inputs'] = [x for x in empty_origin['input_projection']['inputs']
            if x['type'] != 'LeanInformationAudit.AuricFib.Contract.Application']
        empty_origin_path.write_text(json.dumps(empty_origin))
        with patch.object(fib_analysis.subprocess, 'run') as command:
            self.assertFalse(fib_analysis.run_regressions(ROOT, before, same))
            command.assert_not_called()
            # First Application, all complete supported states (including
            # unavailable inputs), removal, and explicit program coverage.
            for previous, current, selected in ((empty_report, before, False),
                    (before, empty_report, False), (before, same, True),
                    (empty_report, before, True)):
                command.reset_mock()
                self.assertTrue(fib_analysis.run_regressions(ROOT, previous, current, selected))
                command.assert_called_once()
                self.assertEqual(command.call_args.args[0], ['make', '-C', str(ROOT), 'compiled-fib-test'])
            # Every field of the complete detached input remains significant;
            # readings themselves never select a test or invalidate a report.
            for field, value in (('input_identity', 'a' * 64), ('unavailable_reason', 'changed boundary'),
                                 ('target_module', 'Other.Source')):
                changed = copy.deepcopy(original)
                changed['fib_analysis']['applications'][0][field] = value
                current = save('changed-' + field, changed)
                command.reset_mock()
                self.assertTrue(fib_analysis.run_regressions(ROOT, before, current))
                command.assert_called_once()
            # Failed selected work propagates and cannot replace its input data.
            before_bytes = before.read_bytes()
            command.side_effect = subprocess.CalledProcessError(23, 'make')
            with self.assertRaises(subprocess.CalledProcessError) as failure:
                fib_analysis.run_regressions(ROOT, before, same, True)
            self.assertEqual(failure.exception.returncode, 23)
            self.assertEqual(before.read_bytes(), before_bytes)
        with self.assertRaisesRegex(ValueError, 'fib.missing_required_inputs'):
            save('missing', empty)  # Its projection still declares Applications.
            fib_analysis.application_inputs(self.directory / 'missing.json')
        with self.assertRaises(FileNotFoundError):
            fib_analysis.run_regressions(ROOT, before, self.directory / 'absent.json')

    def test_z_native_incremental_work_uses_lake_traces(self):
        activity = self.directory / 'incremental-work.jsonl'
        phases = self.directory / 'incremental-phases.jsonl'
        original = self.source.read_bytes()
        unrelated_name = 'Reg.Support.AuricFibUnrelatedFixture'
        unrelated = ROOT / (unrelated_name.replace('.', '/') + '.lean')
        self.assertFalse(unrelated.exists(), 'unrelated fixture is already owned')
        extra_targets = []
        def build():
            activity.write_text('')
            phases.write_text('')
            result = subprocess.run(['bash', 'tools/scripts/worktree/lean-cache-run.sh', 'lake', '-d',
                'tools/lean-inspector-reg', 'build', MODULE + ':report', PLAIN_MODULE + ':report',
                *extra_targets],
                cwd=ROOT, env=dict(os.environ, STRATALINT_INSPECTOR_ACTIVITY=str(activity),
                    STRATALINT_INSPECTOR_PHASES=str(phases)), capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return [json.loads(line) for line in activity.read_text().splitlines()]
        self.assertEqual(build(), [])
        try:
            unrelated.write_text('def unrelatedFibWorkProbe : Nat := 1\n')
            extra_targets.append(unrelated_name + ':report')
            self.assertFalse(any(x['kind'].startswith('fib-') for x in build()))
            unrelated.write_text('def unrelatedFibWorkProbe : Nat := 2\n')
            self.assertFalse(any(x['kind'].startswith('fib-') for x in build()))
            # The compiler changes this module without changing any Application.
            # Its genuine closure invalidates extraction; unchanged leaves reuse
            # the custody-checked readings and invoke no arithmetic analyzer.
            self.source.write_bytes(original + b'\ndef fibIncrementalNoise : Nat := 13\n')
            changed = build()
            self.assertEqual(sum(x['count'] for x in changed if x['kind'] == 'extract'), 1)
            self.assertEqual(sum(x['count'] for x in changed if x['kind'] == 'fib-generated'), 0)
            self.assertEqual(sum(x['count'] for x in changed if x['kind'] == 'fib-analysis-invocations'), 0)
            self.assertGreater(sum(x['count'] for x in changed if x['kind'] == 'fib-reused'), 0)
            self.assertIn('fib-extract', phases.read_text())
            self.assertNotIn('lake-analyzer-await', phases.read_text())
            self.assertEqual(build(), [])
            # Keep the changed acquired law normalized and compiler-valid.
            changed_source = original
            for before, after in (
                    (b'private def acquiredNullMass : Nat := 1',
                     b'private def acquiredNullMass : Nat := 2'),
                    (b'  denominator := 5\n', b'  denominator := 6\n')):
                self.assertEqual(original.count(before), 1)
                changed_source = changed_source.replace(before, after)
            self.assertNotEqual(changed_source, original)
            self.source.write_bytes(changed_source)
            affected = build()
            self.assertGreater(sum(x['count'] for x in affected if x['kind'] == 'fib-generated'), 0)
            self.assertGreater(sum(x['count'] for x in affected if x['kind'] == 'fib-analysis-invocations'), 0)
            self.assertGreater(sum(x['count'] for x in affected if x['kind'] == 'fib-reused'), 0)
            affected_report = self.directory / 'affected-report.json'
            with zipfile.ZipFile(STATE / 'modules' / (MODULE + '.zip')) as bundle:
                for suffix in ('', '.materials.zip', '.provenance.json'):
                    Path(str(affected_report) + suffix).write_bytes(
                        bundle.read('raw-lean-report.json' + suffix))
            declared = next(row for row in fib_analysis.consume(affected_report)['applications']
                            if row['application'] == PREFIX + 'nativeDeclared')
            self.assertEqual(declared['request']['law'], ['2/6'] + ['1/6'] * 4)
            self.assertEqual(declared['reading']['source_contract']['pushforward_law'],
                             [{'numerator': '1', 'denominator': '3'}] +
                             [{'numerator': '1', 'denominator': '6'}] * 4)
            self.assertEqual(build(), [])
        finally:
            self.source.write_bytes(original)
            unrelated.unlink(missing_ok=True)
            cleanup_module(unrelated_name)


if __name__ == '__main__':
    unittest.main()
