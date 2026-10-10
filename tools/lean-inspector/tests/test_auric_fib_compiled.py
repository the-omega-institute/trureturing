#!/usr/bin/env python3
"""Real pinned compiler -> native module artifact -> FIB downstream consumer."""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import fib_analysis
import materials
import publication

MODULE = 'Reg.Support.AuricFibCompiledFixture'
SOURCE_MODULE = 'Reg.Support.AuricFibCompiledSource'
PREFIX = 'LeanInformationAuditRegTests.AuricFib.CompiledFixture.'
TEMPLATE = ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/AuricFib/CompiledFixture.lean'
STATE = ROOT / '.lake/build/lean-inspector'
DIAGNOSTICS = None


def q(value):
    return Fraction(int(value['numerator']), int(value['denominator']))


def observe_fib(label, payload):
    try:
        if DIAGNOSTICS:
            with (DIAGNOSTICS / 'phases').open('a', encoding='utf-8') as target:
                target.write(json.dumps(dict(observation=label, **payload)) + '\n')
        else:
            print(label + ' ' + json.dumps(payload), flush=True)
    except (OSError, ValueError):
        pass


class CompiledFibIntegration(unittest.TestCase):
    def setUp(self):
        self.paths = [ROOT / (x.replace('.', '/') + '.lean') for x in (MODULE, SOURCE_MODULE)]
        if any(p.exists() for p in self.paths):
            raise RuntimeError('FIB compiler fixture source is already owned by another invocation')
        self.addCleanup(self.cleanup)
        template = TEMPLATE.read_text()
        first, rest = template.split('def declared :', 1)
        # The acquired numeric data has no native-theory dependency. Keep its
        # private source edge real without importing the full theorem twice.
        self.source = ('module\npublic section\nnamespace ' + PREFIX[:-1] + '\n'
            'private def acquiredNullMass : Nat := 1\n'
            'def acquiredSourceNullMass : Nat := acquiredNullMass\n'
            'def acquiredSourceDenominator : Nat := 5\n'
            'end ' + PREFIX[:-1] + '\n')
        first = first.replace('private def acquiredNullMass : Nat := 1\n', '')
        first = first.replace('nullMass := acquiredNullMass', 'nullMass := acquiredSourceNullMass')
        first = first.replace('denominator := 5', 'denominator := acquiredSourceDenominator', 1)
        self.application = 'import ' + SOURCE_MODULE + '\n' + first + 'def declared :' + rest
        self.write_sources()
        self.env = dict(os.environ, GIT_OPTIONAL_LOCKS='0',
            STRATALINT_LEAN_PRODUCER_DLL=str(ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'))
        self.work = tempfile.TemporaryDirectory(prefix='fib-compiled-consume.')
        self.addCleanup(self.work.cleanup)
        self.activity = Path(self.work.name) / 'activity.jsonl'
        self.env['STRATALINT_INSPECTOR_ACTIVITY'] = str(self.activity)
        self.env['STRATALINT_INSPECTOR_PROFILE'] = '1'
        for name, variable in [('phases', 'STRATALINT_INSPECTOR_PHASES'),
                ('stdout', 'STRATALINT_INSPECTOR_CHILD_STDOUT'), ('stderr', 'STRATALINT_INSPECTOR_CHILD_STDERR')]:
            self.env[variable] = str((DIAGNOSTICS or Path(self.work.name)) / name)
        self.first = self.build()

    def cleanup(self):
        for path in self.paths:
            path.unlink(missing_ok=True)

    def write_sources(self):
        for path, text in zip(self.paths, (self.application, self.source)):
            path.write_text(text)

    def command(self, args, expected=0, *, full=False):
        started = time.monotonic()
        self.activity.unlink(missing_ok=True)
        env = dict(self.env, LAKE_ARTIFACT_CACHE="false") if full else self.env
        paths = {name: Path(env[variable]) for name, variable in
            [('phases', 'STRATALINT_INSPECTOR_PHASES'), ('stdout', 'STRATALINT_INSPECTOR_CHILD_STDOUT'),
             ('stderr', 'STRATALINT_INSPECTOR_CHILD_STDERR')] if env.get(variable)}
        paths.update({name + '-cache': Path(str(path) + '.cache')
                      for name, path in list(paths.items()) if name in ('stdout', 'stderr')})
        for path in paths.values():
            try:
                path.write_bytes(b'')
            except OSError as error:
                observe_fib('FIB_COMPILED_DIAGNOSTIC_UNAVAILABLE', dict(path=str(path), error=str(error)))
        self.command_sequence = getattr(self, 'command_sequence', 0) + 1
        sequence = self.command_sequence
        observe_fib('FIB_COMPILED_STAGE', dict(stage='command', boundary='start', sequence=sequence,
            command=args, full=full))
        result = None
        try:
            result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                                    capture_output=True, check=False)
        finally:
            observe_fib('FIB_COMPILED_STAGE', dict(stage='command', boundary='finish', sequence=sequence,
                raw_exit=result.returncode if result is not None else None,
                elapsed_seconds=time.monotonic()-started))
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        self.work_counts = {}
        for event in (self.activity.read_text().splitlines() if self.activity.exists() else []):
            value = json.loads(event)
            self.work_counts[value['kind']] = self.work_counts.get(value['kind'], 0) + value['count']
        print('FIB_COMPILED_COMMAND ' + json.dumps({'command': args,
            'exit': result.returncode, 'elapsed_seconds': time.monotonic()-started,
            'actual_work': self.work_counts}), flush=True)
        return result

    def build(self, full=False):
        artifact = STATE / 'modules' / (MODULE + '.zip')
        if full:
            artifact.unlink(missing_ok=True)
            Path(str(artifact) + ".trace").unlink(missing_ok=True)
        result = self.command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'lake', '-d', 'tools/lean-inspector-reg', 'build', MODULE + ':report'], full=full)
        observe_fib('FIB_COMPILED_STAGE', dict(stage='artifact-consumer', boundary='start',
            sequence=self.command_sequence, artifact=str(artifact)))
        self.artifact = artifact
        self.assertFalse(Path(str(artifact) + '.fib-previous').exists())
        with zipfile.ZipFile(artifact) as bundle:
            for suffix in ('', '.materials.zip', '.provenance.json'):
                (Path(self.work.name) / ('raw-lean-report.json' + suffix)).write_bytes(
                    bundle.read('raw-lean-report.json' + suffix))
        consumed = fib_analysis.consume(Path(self.work.name) / 'raw-lean-report.json')
        records = {x['application'].removeprefix(PREFIX): x for x in consumed['applications']}
        self.assertEqual(set(records), {x['application'].removeprefix(PREFIX) for x in
            publication.validate_rows(Path(self.work.name) / 'raw-lean-report.json',
                Path(self.work.name) / 'raw-lean-report.json.materials.zip')[0]['fib_analysis']['applications']})
        if full:
            self.assertGreater(self.work_counts.get('fib-generated', 0), 0)
            self.assertEqual(self.work_counts.get('fib-reused', 0), 0)
        self.output = result.stdout
        observe_fib('FIB_COMPILED_STAGE', dict(stage='artifact-consumer', boundary='finish',
            sequence=self.command_sequence, applications=len(records)))
        return records

    def test_positive_source_native_macro_and_boundaries(self):
        report = self.first['declared']['reading']
        missing = fib_analysis.consume(Path(self.work.name) / 'raw-lean-report.json', [PREFIX + 'noise'])
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
        self.source = self.source.replace('acquiredNullMass : Nat := 1', 'acquiredNullMass : Nat := 2')
        self.source = self.source.replace('acquiredSourceDenominator : Nat := 5',
                                         'acquiredSourceDenominator : Nat := 6')
        self.write_sources()
        changed = self.build()
        self.assertNotEqual(report['association_coordinate'], changed['declared']['reading']['association_coordinate'])
        self.assertEqual(changed['declared']['reading']['arena']['cardinality'], 5)
        self.assertEqual(self.first['absent'], changed['absent'])
        self.assertEqual(changed, self.build(full=True))

    def test_noop_and_unrelated_preserve_artifact_and_leaves(self):
        before = (self.artifact.read_bytes(), self.artifact.stat().st_mtime_ns)
        self.assertEqual(self.first, self.build())
        self.assertEqual(before, (self.artifact.read_bytes(), self.artifact.stat().st_mtime_ns))
        self.assertEqual(self.work_counts.get('extract', 0), 0)
        self.assertEqual(self.work_counts.get('fib-generated', 0), 0)
        self.application = self.application.replace('theorem noise : True := trivial',
            'theorem noise : True := by exact (And.intro True.intro True.intro).1')
        self.write_sources()
        changed = self.build()
        self.assertEqual(self.first, changed)
        self.assertEqual(self.work_counts.get('fib-generated'), 0)
        self.assertEqual(self.work_counts.get('fib-reused'), len(self.first))
        self.assertEqual(changed, self.build(full=True))

    def test_private_transitive_source_and_layer_dependency_updates(self):
        self.source = self.source.replace('acquiredNullMass : Nat := 1', 'acquiredNullMass : Nat := 2')
        self.source = self.source.replace('acquiredSourceDenominator : Nat := 5',
                                         'acquiredSourceDenominator : Nat := 6')
        self.write_sources()
        source = self.build()
        self.assertNotEqual(self.first['declared']['input_identity'], source['declared']['input_identity'])
        self.assertEqual(self.first['absent'], source['absent'])
        self.assertEqual(self.work_counts.get('fib-generated'), 1)
        self.assertEqual(self.work_counts.get('fib-reused'), len(self.first) - 1)
        self.application = self.application.replace('[] [.seam, .guard, .reply, .atom]',
            '[.reply] [.guard, .seam, .atom]', 1)
        self.write_sources()
        schedule = self.build()
        self.assertNotEqual(source['declared']['reading']['layered_spectrum'],
                            schedule['declared']['reading']['layered_spectrum'])
        self.assertEqual(source['absent'], schedule['absent'])
        self.assertEqual(schedule, self.build(full=True))

    def test_membership_removal_addition_and_eligibility(self):
        start = self.application.index('def declared :')
        end = self.application.index('def absent :')
        saved = self.application[start:end]
        self.application = self.application[:start] + self.application[end:]
        self.write_sources()
        removed = self.build()
        self.assertNotIn('declared', removed)
        self.assertEqual(self.first['absent'], removed['absent'])
        index = self.application.index('def absent :')
        self.application = self.application[:index] + saved + self.application[index:]
        self.write_sources()
        self.assertEqual(self.first, self.build())
        self.application = self.application.replace('evidence := .native bridge (.declared "compiled source fixture" acquiredMasses)\n    [] [.seam, .guard, .reply, .atom]',
            'evidence := .unsupported "continuation contract unavailable"', 1)
        self.write_sources()
        unavailable = self.build()
        self.assertIsNone(unavailable['declared']['reading']['escape_rate'])
        self.assertEqual(unavailable, self.build(full=True))

    def test_invalid_native_bridge_fails_compilation(self):
        self.application = self.application.replace('reader_eq := rfl', 'reader_eq := by cases True.intro')
        # An ordinary mistyped contract cannot produce new artifact evidence.
        self.application = self.application.replace('fun a => rawTransition (rawMachine 0).start a',
            'fun _ => none')
        self.write_sources()
        before = self.artifact.read_bytes()
        result = self.command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'lake', '-d', 'tools/lean-inspector-reg', 'build', MODULE + ':report'], expected=1)
        diagnostic = result.stdout + result.stderr
        bridge_line = self.application[:self.application.index('reader_eq :=')].count('\n') + 1
        self.assertIn(f'AuricFibCompiledFixture.lean:{bridge_line}:', diagnostic)
        self.assertIn('unsolved goals', diagnostic)
        self.assertEqual(before, self.artifact.read_bytes())

    def test_native_reader_and_target_dependency_updates(self):
        self.application = self.application.replace('fun a => rawTransition (rawMachine 0).start a',
            'fun a => rawTransition (rawMachine 0).start (id a)')
        self.write_sources()
        changed = self.build()
        self.assertNotEqual(self.first['declared']['input_identity'], changed['declared']['input_identity'])
        self.assertEqual(self.first['declared']['reading'], changed['declared']['reading'])
        self.assertEqual(self.first['unsupported'], changed['unsupported'])
        self.application = self.application.replace('theorem unrelated : True := trivial',
            'theorem unrelated : True := by exact (And.intro True.intro True.intro).1')
        self.write_sources()
        target = self.build()
        self.assertNotEqual(changed['wrongTarget']['input_identity'], target['wrongTarget']['input_identity'])
        self.assertEqual(changed['wrongTarget']['reading'], target['wrongTarget']['reading'])
        self.assertEqual(changed['declared'], target['declared'])
        self.assertEqual(target, self.build(full=True))


class CompiledFibProgramTests(unittest.TestCase):
    def test_report_uses_compiled_module_without_native_executable(self):
        config = ROOT / 'tools/lean-inspector-reg/lakefile.toml'
        before = config.read_bytes()
        metadata = config.stat()
        self.assertEqual(before.count(b'name = "auricFibAnalysis"'), 1)
        fixture = CompiledFibIntegration()
        try:
            # Remove the executable target, retaining the actual analyzer module
            # and every source/contract dependency in the production workspace.
            config.write_bytes(before.replace(b'name = "auricFibAnalysis"',
                b'name = "unrequestedNativeFibAnalysis"'))
            fixture.setUp()
            report = fixture.first['declared']['reading']
            self.assertEqual(report['arena']['cardinality'], 5)
            self.assertEqual(report['arena']['ordered_pair_denominator'], 20)
            requests = [x['request'] for x in publication.validate_rows(
                Path(fixture.work.name) / 'raw-lean-report.json',
                Path(fixture.work.name) / 'raw-lean-report.json.materials.zip')[0]
                ['fib_analysis']['applications'] if x['request'] is not None]
            standalone = subprocess.run(['bash', 'tools/scripts/auric-fib-analysis.sh', '--batch'],
                cwd=ROOT, env=fixture.env, input=json.dumps(requests),
                text=True, capture_output=True, check=False)
            self.assertEqual(standalone.returncode, 2, standalone.stdout + standalone.stderr)
            self.assertEqual(json.loads(standalone.stdout), [x['reading'] for x in
                publication.validate_rows(Path(fixture.work.name) / 'raw-lean-report.json',
                    Path(fixture.work.name) / 'raw-lean-report.json.materials.zip')[0]
                ['fib_analysis']['applications'] if x['request'] is not None])
        finally:
            fixture.doCleanups()
            config.write_bytes(before)
            os.chmod(config, metadata.st_mode)
            os.utime(config, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
        self.assertEqual(config.read_bytes(), before)


class CompiledFibObservationTests(unittest.TestCase):
    def test_live_native_output_precedes_exit_and_preserves_raw_failure(self):
        import native
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = {name: root / name for name in ('phases', 'stdout', 'stderr')}
            env = dict(os.environ, STRATALINT_INSPECTOR_PHASES=str(paths['phases']),
                STRATALINT_INSPECTOR_CHILD_STDOUT=str(paths['stdout']),
                STRATALINT_INSPECTOR_CHILD_STDERR=str(paths['stderr']))
            child = root / 'child'
            child.write_text(f'#!{sys.executable}\n' + '''import os, sys
from pathlib import Path
print('native stdout before exit', flush=True)
print('native stderr before exit', file=sys.stderr, flush=True)
assert Path(os.environ['STRATALINT_INSPECTOR_CHILD_STDOUT']).read_text() == 'native stdout before exit\\n'
assert Path(os.environ['STRATALINT_INSPECTOR_CHILD_STDERR']).read_text() == 'native stderr before exit\\n'
raise SystemExit(37)
''')
            child.chmod(0o755)
            out, err = io.StringIO(), io.StringIO()
            with patch.dict(os.environ, env), patch('sys.stdout', out), patch('sys.stderr', err):
                with self.assertRaisesRegex(ValueError, 'raw.reader_failed:exit=37') as raised:
                    native.run_inspector(root, child, [])
            self.assertEqual(raised.exception.__cause__.returncode, 37)
            self.assertEqual(out.getvalue(), 'native stdout before exit\n')
            self.assertEqual(err.getvalue(), 'native stderr before exit\n')
            self.assertEqual(paths['stdout'].read_text(), out.getvalue())
            self.assertEqual(paths['stderr'].read_text(), err.getvalue())

    def test_diagnostic_sink_failure_preserves_command_result_and_exception(self):
        fixture = CompiledFibIntegration()
        with tempfile.TemporaryDirectory() as directory:
            fixture.work = type('Work', (), {'name': directory})()
            fixture.activity = Path(directory) / 'activity'
            fixture.env = dict(os.environ)
            blocked = Path(directory) / 'blocked'
            blocked.write_text('regular file')
            # Diagnostic output is optional; captured assertion input is not.
            with patch.object(sys.modules[__name__], 'DIAGNOSTICS', blocked):
                result = fixture.command([sys.executable, '-c',
                    "import sys; print('out'); print('err', file=sys.stderr); sys.exit(19)"], expected=19)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (19, 'out\n', 'err\n'))
                failure = subprocess.TimeoutExpired(['original'], 300, output='raw', stderr='error')
                with patch.object(subprocess, 'run', side_effect=failure):
                    with self.assertRaises(subprocess.TimeoutExpired) as raised:
                        fixture.command(['original'])
                self.assertIs(raised.exception, failure)

if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == '--diagnostics':
        DIAGNOSTICS = Path(sys.argv[2])
        if not DIAGNOSTICS.is_absolute() or not DIAGNOSTICS.is_dir():
            raise SystemExit('FIB diagnostics require an existing absolute directory')
        del sys.argv[1:3]
    unittest.main()
