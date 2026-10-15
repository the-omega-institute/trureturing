#!/usr/bin/env python3
"""One compiled optional-analysis fixture through the production consumer.

Lake builds the fixture once. Source, finite and non-finite boundaries share
that result; ordinary native reuse tests own incremental build behavior.
"""
import os
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis

MODULE = 'Reg.Support.AuricFibUniversalFixture'
PLAIN_MODULE = 'D5.S0.Diagonal.PigeonholeFiber'
PREFIX = 'AuricFibUniversalProduction.'
STATE = ROOT / '.lake/build/lean-inspector'


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
        fixture_root = ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/AuricFib'
        native_fixture = (fixture_root / 'CompiledFixture.lean').read_text().replace(
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
        for folder, suffixes in [('modules', ['.zip', '.zip.trace', '.zip.hash',
                                              '.zip.pending', '.zip.fib-previous']),
                                 ('inputs', ['.json', '.json.sources.json']),
                                 ('judge-inputs', ['.json', '.json.trace', '.json.hash'])]:
            for suffix in suffixes:
                (STATE / folder / (MODULE + suffix)).unlink(missing_ok=True)
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


if __name__ == '__main__':
    unittest.main()
