#!/usr/bin/env python3
"""One real compiled audit/report fixture for the optional FIB consumer.

Typed source and mathematical boundaries also run in compiledJudgeTests; the
universal production cases retain generic, non-finite and failed-program checks.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
import zipfile
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis
import publication
from test_auric_fib_analysis import assert_layer_partition

MODULE = 'Reg.Support.AuricFibCompiledFixture'
SOURCE_MODULE = 'Reg.Support.AuricFibCompiledSource'
PREFIX = 'LeanInformationAuditRegTests.AuricFib.CompiledFixture.'
TEMPLATE = ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/AuricFib/CompiledFixture.lean'
STATE = ROOT / '.lake/build/lean-inspector'


def q(value):
    return Fraction(int(value['numerator']), int(value['denominator']))


def assert_native_replay(test, request, raw, produced):
    if produced['disposition']['status'] == 'refuted':
        test.assertEqual(raw, produced)
        return
    test.assertEqual(set(raw), set(produced))
    for field in set(produced) - {'source_contract', 'disposition'}:
        test.assertEqual(raw[field], produced[field], field)
    source, acquired = raw['source_contract'], produced['source_contract']
    test.assertIsNone(source['binding'])
    test.assertEqual(source['supplied_binding'], request['binding'])
    test.assertEqual(acquired['binding'], request['binding'])
    test.assertIsNone(source['law_acquisition'])
    test.assertEqual(source['supplied_law_acquisition'], request.get('law_acquisition'))
    test.assertEqual(acquired['law_acquisition'], request.get('law_acquisition'))
    test.assertNotIn('supplied_binding', acquired)
    test.assertNotIn('supplied_law_acquisition', acquired)
    provenance = {'binding', 'supplied_binding', 'law_acquisition', 'supplied_law_acquisition'}
    test.assertEqual({k: v for k, v in source.items() if k not in provenance},
                     {k: v for k, v in acquired.items() if k not in provenance})
    raw_disposition, compiled_disposition = raw['disposition'], produced['disposition']
    test.assertIn('unverified', raw_disposition['reason'])
    test.assertNotEqual(raw_disposition['reason'], compiled_disposition['reason'])
    test.assertEqual({k: v for k, v in raw_disposition.items() if k not in {'reason', 'readings'}},
                     {k: v for k, v in compiled_disposition.items() if k not in {'reason', 'readings'}})
    explanations, compiled_explanations = raw_disposition['readings'], compiled_disposition['readings']
    test.assertEqual(set(explanations), set(compiled_explanations))
    test.assertEqual(explanations['source_contract']['kind'], 'unavailable')
    test.assertIn('unverified', explanations['source_contract']['reason'])
    test.assertEqual(compiled_explanations['source_contract'], dict(kind='available',
        reason='compiled native adapter with explicit initialized specialization'))
    law_fields = {'pyramid_coordinates', 'association_coordinate', 'residuals', 'conditional_reply_law'}
    for field in set(explanations) - law_fields - {'source_contract'}:
        test.assertEqual(explanations[field], compiled_explanations[field], field)
    for field in law_fields:
        if source['pushforward_law'] is None:
            test.assertEqual(explanations[field]['kind'], 'unknown')
            test.assertEqual(compiled_explanations[field], request.get('law_acquisition', explanations[field]))
        else:
            test.assertEqual(explanations[field]['kind'], compiled_explanations[field]['kind'])
            if explanations[field]['kind'] == 'available':
                test.assertIn('supplied', explanations[field]['reason'])
                test.assertNotEqual(explanations[field]['reason'], compiled_explanations[field]['reason'])
            else:
                test.assertEqual(explanations[field], compiled_explanations[field])
    test.assertFalse(raw_disposition['is_lean_proof'])
    test.assertFalse(compiled_disposition['is_lean_proof'])
    test.assertNotEqual(raw, produced)


class CompiledFibIntegration(unittest.TestCase):
    def setUp(self):
        self.paths = [ROOT / (x.replace('.', '/') + '.lean') for x in (MODULE, SOURCE_MODULE)]
        if any(p.exists() for p in self.paths):
            raise RuntimeError('compiler fixture source is already owned by another invocation')
        self.temporary = tempfile.TemporaryDirectory(prefix='compiled-audit-consume.')
        self.root = Path(self.temporary.name)
        self.addCleanup(self.cleanup)
        self.config = ROOT / 'tools/lean-inspector-reg/lakefile.toml'
        self.configuration = self.config.read_bytes()
        self.config_metadata = self.config.stat()
        self.assertEqual(self.configuration.count(b'name = "auricFibAnalysis"'), 1)
        self.native_bin = self.root / 'bin'
        self.config.write_bytes(('binDir = ' + json.dumps(str(self.native_bin)) + '\n').encode()
            + self.configuration.replace(b'name = "auricFibAnalysis"',
                                         b'name = "unrequestedNativeFibAnalysis"'))
        template = TEMPLATE.read_text()
        first, rest = template.split('def declared :', 1)
        # This private transitive input is independent of the native theorem.
        self.source = ('module\npublic section\nnamespace ' + PREFIX[:-1] + '\n'
            'private def acquiredNullMass : Nat := 1\n'
            'def acquiredSourceNullMass : Nat := acquiredNullMass\n'
            'def acquiredSourceDenominator : Nat := 5\n'
            'end ' + PREFIX[:-1] + '\n')
        first = first.replace('private def acquiredNullMass : Nat := 1\n', '')
        first = first.replace('nullMass := acquiredNullMass', 'nullMass := acquiredSourceNullMass')
        first = first.replace('denominator := 5', 'denominator := acquiredSourceDenominator', 1)
        self.application = 'import ' + SOURCE_MODULE + '\n' + first + 'def declared :' + rest
        start, end = self.application.index('def empirical :'), self.application.index('def apex :')
        empirical = self.application[start:end].replace(' bridge (', ' empiricalBridge (')
        self.application = (self.application[:start] +
            'def empiricalBridge : NativeBridge := bridge\n\n' + empirical + self.application[end:])
        self.write_sources()
        self.env = dict(os.environ, GIT_OPTIONAL_LOCKS='0',
            STRATALINT_LEAN_PRODUCER_DLL=str(ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'))
        self.activity = self.root / 'activity.jsonl'
        self.env['STRATALINT_INSPECTOR_ACTIVITY'] = str(self.activity)
        self.env['STRATALINT_INSPECTOR_PROFILE'] = '1'
        self.commands = 0
        # Both facets share Lake's ordinary preparation in one invocation.
        self.first = self.build(initial=True)
        self.assertGreater(self.work_counts.get('fib-generated', 0), 0)
        self.assertEqual(self.work_counts.get('fib-reused', 0), 0)
        ordinary = STATE / 'modules' / (SOURCE_MODULE + '.zip')
        ordinary_report = self.root / 'ordinary.json'
        with zipfile.ZipFile(ordinary) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                Path(str(ordinary_report) + suffix).write_bytes(
                    bundle.read('raw-lean-report.json' + suffix))
        self.assertEqual(fib_analysis.consume(ordinary_report)['applications'], [])
        missing = fib_analysis.consume(ordinary_report, [PREFIX + 'acquiredSourceNullMass'])
        self.assertIn('no acquired FIB', missing['applications'][0]['reading']['disposition']['reason'])

    def cleanup(self):
        for path in self.paths:
            path.unlink(missing_ok=True)
        self.temporary.cleanup()
        self.config.write_bytes(self.configuration)
        os.chmod(self.config, self.config_metadata.st_mode)
        os.utime(self.config, ns=(self.config_metadata.st_atime_ns, self.config_metadata.st_mtime_ns))

    def write_sources(self):
        for path, text in zip(self.paths, (self.application, self.source)):
            data = text.encode('utf-8')
            if not path.exists() or path.read_bytes() != data:
                path.write_bytes(data)

    def command(self, args, expected=0, *, full=False):
        started = time.monotonic()
        self.activity.unlink(missing_ok=True)
        # The initial scoped fixture acquisition may start with no project
        # oleans. Use the existing one-command cold-build consent; ensure,
        # cache ownership and the Native runner's cumulative guard still apply.
        # Incremental and rejection commands keep the ordinary environment.
        env = dict(self.env, LAKE_ARTIFACT_CACHE="false",
                   STRATALINT_ACCEPT_COLD_BUILD="1") if full else self.env
        # The shared .NET native runner owns the cumulative 300s child-tree
        # guard, streams and cleanup; this command adds no FIB timeout layer.
        result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                                capture_output=True, check=False)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        self.commands += 1
        self.work_counts = {}
        for event in (self.activity.read_text().splitlines() if self.activity.exists() else []):
            value = json.loads(event)
            self.work_counts[value['kind']] = self.work_counts.get(value['kind'], 0) + value['count']
        print('COMPILED_ANALYSIS_WORK ' + json.dumps(dict(sequence=self.commands,
            exit=result.returncode, elapsed_seconds=time.monotonic()-started,
            full=full, actual_work=self.work_counts)), flush=True)
        return result

    def build(self, *, initial=False):
        artifact = STATE / 'modules' / (MODULE + '.zip')
        targets = [MODULE + ':report']
        if initial:
            targets.append(SOURCE_MODULE + ':report')
            # Only these fixture artifacts are cold; compiler dependencies stay
            # under the normal Lake/cache ownership.
            for name in (MODULE, SOURCE_MODULE):
                path = STATE / 'modules' / (name + '.zip')
                for suffix in ('', '.trace', '.hash'):
                    Path(str(path) + suffix).unlink(missing_ok=True)
        self.command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'lake', '-d', 'tools/lean-inspector-reg', 'build', *targets], full=initial)
        self.artifact = artifact
        self.assertFalse(Path(str(artifact) + '.fib-previous').exists())
        with zipfile.ZipFile(artifact) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                (self.root / ('raw-lean-report.json' + suffix)).write_bytes(
                    bundle.read('raw-lean-report.json' + suffix))
        self.report = self.root / 'raw-lean-report.json'
        consumed = fib_analysis.consume(self.report)
        records = {x['application'].removeprefix(PREFIX): x for x in consumed['applications']}
        self.assertEqual(set(records), {x['application'].removeprefix(PREFIX) for x in
            publication.validate_rows(self.report, Path(str(self.report) + '.materials.zip'))[0]
                ['fib_analysis']['applications']})
        return records

    def check_positive_source_native_macro_and_boundaries(self):
        report = self.first['declared']['reading']
        missing = fib_analysis.consume(self.report, [PREFIX + 'noise'])
        self.assertIsNone(missing['applications'][0]['reading']['escape_rate'])
        self.assertIn('no acquired FIB', missing['applications'][0]['reading']['disposition']['reason'])
        self.assertEqual(report['arena']['cardinality'], 5)
        self.assertEqual(report['arena']['ordered_pair_denominator'], 20)
        self.assertEqual(len(report['atom_readout']['states']), 5)
        replies = {x['mode']: x['suffix_reply'] for x in report['atom_readout']['states']}
        self.assertIsNone(replies['25'])
        self.assertIsNone(replies['2'])
        self.assertEqual(replies['3'], '18')
        self.assertEqual(q(report['escape_rate']), 0)
        layers = report['layered_spectrum']['layers']
        self.assertTrue(any(x['collapsed'] and x['count'] == 0 for x in layers[1:]))
        self.assertEqual(report['layered_spectrum']['partition_count'], 20)
        self.assertIsNone(self.first['absent']['reading']['pyramid_coordinates'])
        self.assertEqual(self.first['absent']['reading']['arena']['cardinality'], 5)
        absent = self.first['absent']
        self.assertEqual(absent['request']['initial_readouts'], [])
        self.assertEqual(absent['request']['layers'], ['seam', 'guard'])
        self.assertEqual(absent['request']['binding']['occurrence']['source_name'],
                         'D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution')
        self.assertEqual(absent['reading']['source_contract']['binding'], absent['request']['binding'])
        self.assertEqual(absent['reading']['disposition']['readings']['source_contract']['kind'], 'available')
        partial = assert_layer_partition(self, absent['reading'], [], ['seam', 'guard'])
        self.assertEqual([layer['count'] for layer in partial['layers']], [0, 12, 0])
        self.assertEqual(partial['unresolved']['count'], 8)
        self.assertEqual(q(partial['unresolved']['rate']), Fraction(2, 5))
        self.assertEqual(self.first['empirical']['reading']['source_contract']['kind'], 'empirical-archive')
        self.assertFalse(report['source_contract']['physical_law_certified'])
        self.assertFalse(report['disposition']['is_lean_proof'])
        self.assertEqual(report['source_contract']['window_length'], 1)
        self.assertEqual(report['source_contract']['pushforward_law'],
            report['association_coordinate']['reconstructed_law'])
        self.assertEqual(q(report['residuals']['R_guard']['value']),
            q(report['association_coordinate']['delta']) /
            (q(report['pyramid_coordinates']['r']) *
             q(report['continuation_target']['conditioning_event_mass'])))
        self.assertIsNone(self.first['unsupported']['reading']['arena'])
        self.assertIsNone(self.first['wrongTarget']['reading']['escape_rate'])
        self.assertIsNone(self.first['parameterized']['reading']['escape_rate'])
        self.assertEqual(self.first['parameterized']['unavailable_reason'], 'fib.unsupported_application_type')
        self.assertEqual(self.first['rejected']['reading']['disposition']['status'], 'refuted')
        for name in ('apex', 'zeroCondition', 'empirical'):
            self.assertEqual(self.first[name]['reading']['arena']['cardinality'], 5)
            self.assertEqual(self.first[name]['reading']['arena']['ordered_pair_denominator'], 20)
        self.assertEqual(q(self.first['apex']['reading']['pyramid_coordinates']['r']), 0)
        self.assertEqual(q(self.first['apex']['reading']['residuals']['R_guard']['value']), 0)
        zero = self.first['zeroCondition']['reading']['continuation_target']
        self.assertIsNone(zero['conditional_reply_law'])
        records = [x for x in self.first.values() if x['request'] is not None]
        replay = subprocess.run(['bash', 'tools/scripts/auric-fib-analysis.sh', '--batch'],
            cwd=ROOT, env=self.env, input=json.dumps([x['request'] for x in records]),
            text=True, capture_output=True, check=False)
        self.assertEqual(replay.returncode, 2, replay.stdout + replay.stderr)
        raw = json.loads(replay.stdout)
        self.assertEqual(len(raw), len(records))
        for record, reading in zip(records, raw):
            with self.subTest(application=record['application']):
                assert_native_replay(self, record['request'], reading, record['reading'])

    def test_compiled_audit_consumer(self):
        self.check_positive_source_native_macro_and_boundaries()
        for name in ('auricFibAnalysis', 'unrequestedNativeFibAnalysis'):
            self.assertFalse((self.native_bin / name).exists())

        # One initial fixture serves all transitions; Lake decides the work.
        before = self.artifact.read_bytes(), self.artifact.stat().st_mtime_ns
        self.assertEqual(self.first, self.build())
        self.assertEqual(before, (self.artifact.read_bytes(), self.artifact.stat().st_mtime_ns))
        self.assertEqual(self.work_counts.get('extract', 0), 0)
        self.assertEqual(self.work_counts.get('fib-generated', 0), 0)

        self.application = self.application.replace('theorem noise : True := trivial',
            'theorem noise : True := by exact (And.intro True.intro True.intro).1')
        self.write_sources()
        unrelated = self.build()
        self.assertEqual(self.first, unrelated)
        self.assertEqual(self.work_counts.get('fib-generated'), 0)
        self.assertEqual(self.work_counts.get('fib-reused'), len(self.first))

        # Isolate the private source edge: another changed dependency must not
        # accidentally force the refresh this assertion is meant to require.
        self.source = self.source.replace('acquiredNullMass : Nat := 1', 'acquiredNullMass : Nat := 2')
        self.source = self.source.replace('acquiredSourceDenominator : Nat := 5',
                                         'acquiredSourceDenominator : Nat := 6')
        self.write_sources()
        source = self.build()
        self.assertNotEqual(self.first['declared']['input_identity'], source['declared']['input_identity'])
        self.assertNotEqual(self.first['declared']['reading']['association_coordinate'],
                            source['declared']['reading']['association_coordinate'])
        self.assertEqual(source['declared']['reading']['arena']['cardinality'], 5)
        self.assertEqual(self.work_counts.get('fib-generated'), 1)
        self.assertEqual(self.work_counts.get('fib-reused'), len(self.first) - 1)
        self.assertEqual({k: v for k, v in self.first.items() if k != 'declared'},
                         {k: v for k, v in source.items() if k != 'declared'})

        # Distinct live closures let one real compilation exercise each edge:
        # reader -> empirical; layer -> declared; target -> wrongTarget;
        # removal/addition -> zeroCondition/added; qualification -> apex.
        self.application = self.application.replace('def empiricalBridge : NativeBridge := bridge',
            'def empiricalBridge : NativeBridge where\n'
            '  reader := fun a => rawTransition (rawMachine 0).start (id a)\n'
            '  reply := reply\n  reader_eq := rfl\n  reply_eq := rfl')
        self.application = self.application.replace('[] [.seam, .guard, .reply, .atom]',
            '[.reply] [.guard, .seam, .atom]', 1)
        self.application = self.application.replace('theorem unrelated : True := trivial',
            'theorem unrelated : True := by exact (And.intro True.intro True.intro).1')
        start, end = self.application.index('def zeroCondition :'), self.application.index('def unsupported :')
        removed = self.application[start:end]
        self.application = self.application[:start] + removed.replace('def zeroCondition :',
            'def added :', 1) + self.application[end:]
        start, end = self.application.index('def apex :'), self.application.index('def added :')
        apex = self.application[start:end]
        self.application = self.application.replace(apex, apex[:apex.index('  evidence :=')] +
            '  evidence := .unsupported "continuation contract unavailable"\n\n')
        self.write_sources()
        changed = self.build()
        self.assertNotEqual(source['empirical']['input_identity'], changed['empirical']['input_identity'])
        self.assertEqual(source['empirical']['reading'], changed['empirical']['reading'])
        self.assertNotEqual(source['declared']['reading']['layered_spectrum'],
                            changed['declared']['reading']['layered_spectrum'])
        self.assertNotEqual(source['wrongTarget']['input_identity'], changed['wrongTarget']['input_identity'])
        self.assertEqual(source['wrongTarget']['reading'], changed['wrongTarget']['reading'])
        self.assertNotIn('zeroCondition', changed)
        self.assertIn('added', changed)
        self.assertEqual(source['zeroCondition']['reading'], changed['added']['reading'])
        self.assertIsNone(changed['apex']['reading']['escape_rate'])
        self.assertIsNone(changed['apex']['request'])
        affected = {'empirical', 'declared', 'wrongTarget', 'zeroCondition', 'apex', 'added'}
        self.assertEqual({k: v for k, v in source.items() if k not in affected},
                         {k: v for k, v in changed.items() if k not in affected})
        self.assertEqual(self.work_counts.get('fib-generated'), 3)
        self.assertEqual(self.work_counts.get('fib-reused'), 4)

        # Complete numerical generation uses the same current compiler-bound
        # input and production function, with no prior artifact. Extraction and
        # custody were already checked by the real report and consumer above.
        # UniversalProductionTests retains complete extraction equivalence.
        row = publication.validate_rows(self.report, Path(str(self.report) + '.materials.zip'))[0]
        stats = fib_analysis.produce(row, self.root / 'no-prior.zip',
                                     ROOT / 'tools/scripts/auric-fib-analysis.sh')
        self.assertEqual(stats['reused'], 0)
        complete = {x['application'].removeprefix(PREFIX): x for x in row['fib_analysis']['applications']}
        self.assertEqual(changed, complete)
        print('COMPILED_ANALYSIS_COMPLETE ' + json.dumps(stats), flush=True)

        before = self.artifact.read_bytes()
        self.application = self.application.replace('reader_eq := rfl', 'reader_eq := by cases True.intro')
        self.application = self.application.replace('fun a => rawTransition (rawMachine 0).start a',
            'fun _ => none')
        self.write_sources()
        failed = self.command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'lake', '-d', 'tools/lean-inspector-reg', 'build', MODULE + ':report'], expected=1)
        bridge_line = self.application[:self.application.index('reader_eq :=')].count('\n') + 1
        self.assertIn(f'AuricFibCompiledFixture.lean:{bridge_line}:', failed.stdout + failed.stderr)
        self.assertIn('unsolved goals', failed.stdout + failed.stderr)
        self.assertEqual(before, self.artifact.read_bytes())
        missing = self.command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'lake', '-d', 'tools/lean-inspector-reg', 'build', 'auricFibAnalysis'], expected=1)
        self.assertIn('unknown target', missing.stdout + missing.stderr)
        for name in ('auricFibAnalysis', 'unrequestedNativeFibAnalysis'):
            self.assertFalse((self.native_bin / name).exists())


if __name__ == '__main__':
    unittest.main()
