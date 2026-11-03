"""Execute native Lake facets in private pinned-toolchain fixture packages."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch
import zipfile

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
ROOT = Path(os.environ.get('STRATALINT_NATIVE_SOURCE_ROOT', ROOT)).resolve()
sys.path.insert(0, str(HERE))
import publication
import materials
import native



from test_native_support import *


class NativeBatchPartitionTests:
    def test_runtime_capacity_bounds_each_raw_and_judged_group(self):
        requests = [['/root', f'Module.{index:03}', '', '', '/inspector', '']
                    for index in range(11, -1, -1)]
        for size in ('1', '2', '7', '100'):
            chunks = []
            with self.subTest(size=size), patch.dict(os.environ, STRATALINT_NATIVE_BATCH_MODULES=size), \
                    patch.object(native, 'input_projection', side_effect=lambda root, name:
                        {'inputs': ['registration'] if int(name.rsplit('.', 1)[1]) % 2 else []}), \
                    patch.object(native, 'produce_batch_chunk', side_effect=chunks.append):
                native.produce_batch(requests)
            self.assertTrue(all(0 < len(chunk) <= int(size) for chunk in chunks))
            self.assertEqual(sorted(row[1] for chunk in chunks for row in chunk),
                             sorted(row[1] for row in requests))

    def test_partition_preserves_membership_and_order(self):
        requests = [['/root', f'Module.{index:03}', '', '', '/inspector', '']
                    for index in range(201, -1, -1)]
        chunks = []
        with patch.object(native, 'input_projection', return_value={'inputs': []}), \
                patch.object(native, 'produce_batch_chunk', side_effect=chunks.append):
            native.produce_batch(requests)
        self.assertEqual([len(chunk) for chunk in chunks], [100, 100, 2])
        self.assertEqual([row[1] for chunk in chunks for row in chunk],
                         [f'Module.{index:03}' for index in range(202)])

    def test_partition_binds_reg_sized_inventory(self):
        requests = [['/root', f'Reg.Module.{index:03}', '', '', '/inspector', '']
                    for index in range(97)]
        chunks = []
        with patch.object(native, 'input_projection', return_value={'inputs': ['registration']}), \
                patch.object(native, 'produce_batch_chunk', side_effect=chunks.append):
            native.produce_batch(requests)
        self.assertEqual([len(chunk) for chunk in chunks], [97])

    def test_partition_rejects_cross_chunk_duplicate_and_mixed_owner(self):
        requests = [['/root', f'Module.{index:03}', '', '', '/inspector', '']
                    for index in range(101)]
        for replacement, diagnostic in [
            (['/root', 'Module.099', '', '', '/inspector', ''], 'duplicate native batch module'),
            (['/other', 'Module.101', '', '', '/inspector', ''], 'mixed native batch owners'),
        ]:
            with self.subTest(diagnostic=diagnostic), \
                    patch.object(native, 'produce_batch_chunk') as chunk:
                with self.assertRaisesRegex(ValueError, diagnostic):
                    native.produce_batch(requests + [replacement])
                chunk.assert_not_called()


class NativeBatchCapacityConsumerTests:
    def test_runtime_capacity_through_report_entry(self):
        # Real pinned compiler/extractor, using the existing statement-only fixture.
        # No mathematical registration-assessment or Linux memory claim is made.
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = json.loads((ROOT / 'lean-report-inputs.json').read_text())['report_execution']
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.ensure()
        self.restore_compiler()
        self.copy('tools/scripts/report/runner-diagnostics.py')
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        logs = Path(str(output) + '.logs')
        work = self.root / 'module-work.jsonl'
        self.env['STRATALINT_INSPECTOR_MODULE_WORK'] = str(work)
        self.env['LEAN_NUM_THREADS'] = '1'
        self.env['STRATALINT_ACCEPT_COLD_BUILD'] = '1'
        runtime = ['python3', str(self.root / 'tools/scripts/report/runner-diagnostics.py'), '--',
            'bash', str(self.root / 'tools/scripts/report/report-supervisor.sh'),
            '--role', 'lean-cache-slice', '--', 'make', 'lean-report',
            'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build']
        # Same pre-Make validation as the action; values are environment data,
        # never interpolated shell text or Make command-line expressions.
        command = ['bash', '-euc', 'python3 tools/lean-inspector/native.py batch-size\nexec "$@"',
                   'native-cache-producer', *runtime]

        def entry(label, size, *, regenerate=False, success=True):
            work.write_text('')
            args = command + (['REGENERATE_REPORT_ARTIFACTS=1'] if regenerate else [])
            env = dict(self.env, STRATALINT_NATIVE_BATCH_MODULES=size)
            started = time.monotonic()
            result = self.guarded_command(args, env=env)
            self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
            self.record_result(label, dict(command=args, batch_modules=size, exit=result.returncode,
                elapsed_seconds=time.monotonic() - started,
                work=[json.loads(line) for line in work.read_text().splitlines()]))
            return result

        def captures(label, size):
            phases = [json.loads(line) for line in (logs / 'native-phases.jsonl').read_text().splitlines()]
            calls = [phase for phase in phases if phase['phase'] == 'native-inspect'
                     and phase['boundary'] == 'finish']
            names, evidence, paths = [], [], [logs / 'native-phases.jsonl']
            for call in calls:
                self.assertTrue(call['success'])
                path = Path(call['request_capture'])
                request = json.loads(path.read_text())
                # This is the captured argument vector used by the actual executable.
                modules = request['arguments'][6::3]
                self.assertTrue(0 < len(modules) <= size)
                names.extend(modules)
                evidence.append(dict(modules=modules, executable_sha256=request['inspector_executable_sha256']))
                paths.append(path)
            self.assertEqual(sorted(names), ['D5.A', 'D5.Alone', 'D5.B', 'Fixture'])
            self.record_result(label, dict(selected_modules=sorted(names), native_calls=evidence), paths)
            return [len(row['modules']) for row in evidence]

        entry('default', '100')
        self.assertEqual(captures('default-captures', 100), [4])
        baseline = self.report()
        before = self.stamps()
        receipt = json.loads(Path(str(output) + '.reuse.json').read_bytes())
        warm = entry('warm-smaller', '2')
        self.assertEqual(self.stamps(), before)
        self.assertEqual(self.report(), baseline)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', warm.stdout)
        self.assertEqual(json.loads(Path(str(output) + '.reuse.json').read_bytes())['inputs'], receipt['inputs'])
        self.assertEqual(work.read_text(), '')
        # Direct report entry also rejects invalid capacity before a warm hit.
        invalid = self.guarded_command(runtime, env=dict(self.env, STRATALINT_NATIVE_BATCH_MODULES='0'))
        self.assertNotEqual(invalid.returncode, 0)
        self.assertIn('STRATALINT_NATIVE_BATCH_MODULES requires', invalid.stdout + invalid.stderr)
        self.record_result('direct-warm-invalid', dict(command=runtime, batch_modules='0', exit=invalid.returncode))

        entry('small', '2', regenerate=True)
        self.assertEqual(captures('small-captures', 2), [2, 2])
        self.assertEqual(self.report(), baseline)
        self.assertEqual(sorted(row['module'] for row in baseline[0]), ['D5.A', 'D5.Alone', 'D5.B', 'Fixture'])
        self.record_result('equivalent', dict(report_sha256=hashlib.sha256(baseline[1]).hexdigest(),
            materials_sha256=hashlib.sha256(baseline[2]).hexdigest(), module_count=len(baseline[0]),
            report_bytes=len(baseline[1]), materials_bytes=len(baseline[2]),
            whole_report_and_material_bytes_identical=True, warm_receipt_inputs_and_module_artifacts_unchanged=True),
            [output, Path(str(output) + '.materials.zip'), Path(str(output) + '.reuse.json')])

        before = self.stamps()
        marker = self.root / 'injected'
        for value in ('', '0', '101', '-1', '+2', '01', '2.0', ' 2', '2\n', '\u0662',
                      f'2; touch {marker}', f'$(touch {marker})', f'$(shell touch {marker})', f'`touch {marker}`'):
            result = entry('invalid-' + hashlib.sha256(value.encode()).hexdigest()[:8], value, success=False)
            self.assertIn('STRATALINT_NATIVE_BATCH_MODULES requires an integer from 1 to 100',
                          result.stdout + result.stderr)
            self.assertEqual(self.stamps(), before)
            self.assertEqual(self.report(), baseline)
            self.assertFalse(marker.exists())

        # The bounded runtime setting still propagates real kernel/audit failures.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        result = self.guarded_command(['make', 'lean', 'LEAN_TARGETS=:report Audit'],
            env=dict(self.env, STRATALINT_NATIVE_BATCH_MODULES='2'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Audit.lean', result.stdout + result.stderr)
        self.record_result('required-audit-failure', dict(exit=result.returncode))
        self.write('D5/A.lean', 'def invalid : False := True.intro\n')
        result = entry('kernel-failure', '2', success=False)
        self.assertIn('D5/A.lean', result.stdout + result.stderr)


class NativeRecoveryConsumerTests:
    def _exercise_chunk_durability(self, interruption):
        # More than one real native chunk, with the existing four fixture roots.
        for index in range(100):
            self.write(f'D5/Durable{index:03}.lean', f'def durable{index:03} : Nat := {index}\n')
        fixture = self.root / 'Fixture.lean'
        fixture.write_text(fixture.read_text() + '\nnamespace LeanInformationAudit.Contract\n'
            'structure Registration where\n  value : Nat\nend LeanInformationAudit.Contract\n'
            'def durabilityInput : LeanInformationAudit.Contract.Registration := { value := 1 }\n')
        control = self.root / 'chunk-interruption'
        control.write_text(interruption)
        producer = self.root / 'tools/lean-inspector/native.py'
        source = producer.read_text()
        source = source.replace('def produce_batch_chunk(requests):',
            'def produce_batch_chunk(requests):\n'
            '    control = Path(requests[0][0]) / "chunk-interruption"\n'
            '    if control.exists() and any(row[1] == "Fixture" for row in requests):\n'
            '        mode = control.read_text()\n'
            '        (control.parent / "interrupted-chunk.json").write_text(json.dumps([row[1] for row in requests]))\n'
            '        if mode == "failure": raise ValueError("fixture later chunk failure")\n'
            '        if mode == "cancel": os.kill(os.getpid(), 15)')
        call = '            run_inspector(root, executable, arguments, argument_file)'
        source = source.replace(call, call + '\n'
            '            control = root / "chunk-interruption"\n'
            '            if control.exists() and control.read_text() == "truncated" and "Fixture" in triples:\n'
            '                output = directory / "spool.json"\n'
            '                output.write_bytes(output.read_bytes()[:-7])')
        producer.write_text(source)
        result = self.build(success=False)
        state = self.root / '.lake/build/lean-inspector'
        names = json.loads((state / 'module-inputs.json').read_text())['modules']
        self.assertEqual(len(names), 104)
        first = sorted(name for name in names if name != 'Fixture')
        remaining = ['Fixture']
        projection = json.loads((state / 'judge-inputs/Fixture.json').read_text())
        self.assertEqual([row['name'] for row in projection['inputs']], ['durabilityInput'])
        self.assertIn('Fixture', json.loads((self.root / 'interrupted-chunk.json').read_text()))
        self.assertFalse((state / 'report.zip').exists())
        before = self.stamps()
        self.record_result('interrupted', dict(mode=interruption, exit=result.returncode,
            registered_modules=names, completed_modules=sorted(before), expected_completed=first,
            pending=sorted(p.name for p in (state / 'modules').glob('*.pending'))))
        self.assertEqual(sorted(before), first)
        traces = {name: [(state / 'modules' / (name + suffix)).read_bytes()
                        for suffix in ('.zip.trace', '.zip.hash')] for name in first}
        for name in remaining:
            self.assertFalse((state / 'modules' / (name + '.zip.trace')).exists())
        self.write('activity.jsonl', '')
        accepted = self.run_lake('--no-build', 'build', *(name + ':report' for name in first))
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.assertEqual(self.stamps(), before)
        self.assertEqual(traces, {name: [(state / 'modules' / (name + suffix)).read_bytes()
                        for suffix in ('.zip.trace', '.zip.hash')] for name in first})
        refused = self.run_lake('--no-build', 'build', ':report', success=False)
        self.assertFalse((state / 'report.zip').exists())
        self.record_result('fresh-native-reuse', dict(mode=interruption, accepted_exit=accepted.returncode,
            aggregate_refusal_exit=refused.returncode, reused_modules=first,
            extraction=0, artifacts_and_traces_unchanged=True))
        control.unlink()
        # A changed source must miss even though its completed chunk was committed.
        changed = self.root / 'D5/Alone.lean'
        changed.write_text(changed.read_text() + '-- changed committed input\n')
        self.run_lake('--no-build', 'build', 'D5.Alone:report', success=False)
        self.write('activity.jsonl', '')
        self.run_lake('build', 'D5.Alone:report')
        activity = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in activity if row['kind'] == 'extract'), 1)
        refreshed = self.stamps()
        self.assertEqual([name for name in first if refreshed[name] != before[name]], ['D5.Alone'])
        resumed = self.build()
        activity = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in activity if row['kind'] == 'extract'), len(remaining))
        self.assertEqual(sorted(row['module'] for row in self.report()[0]), sorted(names))
        self.assertEqual({name: self.stamps()[name] for name in first}, refreshed)
        self.record_result('complete-resume', dict(mode=interruption, exit=resumed.returncode,
            changed_source_extractions=1, resumed_extractions=len(remaining),
            registered_modules=len(names), aggregate_modules=len(self.report()[0])))

    def test_completed_chunk_survives_later_failure(self):
        self._exercise_chunk_durability('failure')

    def test_completed_chunk_survives_later_cancellation(self):
        self._exercise_chunk_durability('cancel')

    def test_completed_chunk_survives_later_truncation(self):
        self._exercise_chunk_durability('truncated')

    def test_release_stage_and_verify_preserve_absent_lake(self):
        self.build()
        self.publish()
        incoming = self.root / 'public.json'
        with tempfile.TemporaryDirectory(prefix='inspector-release.') as directory:
            directory = Path(directory)
            temporary = directory / 'tmp'
            temporary.mkdir()
            for damage in ['none', 'missing', 'stale', 'changed-dependency']:
                with self.subTest(damage=damage):
                    root = directory / damage
                    shutil.copytree(self.root, root, ignore=shutil.ignore_patterns('.lake', '.git'))
                    subprocess.run(['git', 'init', '--quiet', str(root)], check=True,
                        capture_output=True, timeout=120)
                    bundle = incoming if damage != 'missing' else directory / 'absent.json'
                    if damage == 'stale':
                        source = root / 'D5/Alone.lean'
                        source.write_text(source.read_text() + '-- changed input\n')
                    elif damage == 'changed-dependency':
                        (root / 'ClaimSupport.lean').write_text('def claimSupport : Prop := True\n')
                    environment = dict(self.env, TMPDIR=str(temporary),
                        STRATALINT_LEAN_INPUT_MEMO_ROOT=str(directory / 'verify-memo'))
                    staged = directory / ('staged-' + damage) / publication.RAW
                    stage = subprocess.run([sys.executable, '-B', str(root / 'tools/lean-inspector/publication.py'),
                        'stage', '--bundle', str(bundle), '--staging-directory', str(staged.parent),
                        '--repository', str(root)], cwd=directory, env=environment,
                        text=True, capture_output=True, timeout=120)
                    accepted = damage in ['none', 'changed-dependency']
                    self.assertEqual(stage.returncode, 0 if accepted else 1, stage.stdout + stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'stage must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [], 'stage must clean its input memo')
                    verify = subprocess.run(['bash', str(root / 'tools/scripts/report/lean-report-input.sh'),
                        'verify', '--repository', str(root), '--report', str(staged if accepted else bundle)],
                        cwd=directory, env=environment, text=True, capture_output=True, timeout=120)
                    self.assertEqual(verify.returncode,
                        {'none': 0, 'missing': 2, 'stale': 2, 'changed-dependency': 0}[damage], verify.stdout + verify.stderr)
                    if accepted:
                        self.assertEqual(staged.read_bytes(), incoming.read_bytes())
                        self.assertEqual(publication.member(staged, '.materials.zip').read_bytes(),
                            publication.member(incoming, '.materials.zip').read_bytes())
                    else:
                        self.assertFalse(staged.exists())
                        diagnostic = {'missing': 'missing bundle member', 'stale': 'stale input/provenance'}[damage]
                        self.assertIn(diagnostic, stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'verify must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [])
                    self.record_result('release-' + damage, dict(stage_exit=stage.returncode,
                        verify_exit=verify.returncode, lake_absent=True, temporary_clean=True))




    def test_native_imports_without_lzma_and_batch_failures_propagate(self):
        self.build()
        request = self.root / 'requests.json'
        artifact = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        # A fresh interpreter without lzma must still import the real producer.
        control = subprocess.run([sys.executable, '-B', '-c',
            'import sys; sys.modules["lzma"] = None; sys.path.insert(0, sys.argv[1]); import native',
            str(self.root / 'tools/lean-inspector')],
            cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
        errors = [ValueError('required producer failure')]
        if zipfile.lzma is not None:
            errors.append(zipfile.lzma.LZMAError('required producer decoder failure'))
        for kind, owner in [('produce', 'produce_batch'), ('aggregate', 'aggregate')]:
            request.write_text(json.dumps([[kind, [str(self.root), str(artifact)]]]))
            for error in errors:
                with self.subTest(kind=kind, exception=type(error).__name__):
                    with patch.object(native, owner, side_effect=error):
                        with self.assertRaises(type(error)):
                            native.batch(request)
    def test_native_required_failures(self):
        self.build()
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        self.build(success=False, targets=['Audit'])
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        self.write('D5/A.lean', 'def invalid : False := True.intro\n')
        self.build(success=False)
        self.write('D5/A.lean', 'import D5.B\ndef value : Nat := D5.hidden\n')
        self.write('utility.json', '{invalid')
        self.build(success=False)
        self.utility()
        original_policy = (self.root / 'lean-report-inputs.json').read_text()
        for invalid in ['{invalid', original_policy.replace('"schema_version": 1', '"schema_version": 9'),
                        original_policy.replace('"pattern": "tools/scripts/report/lean-report-selection.py"',
                                                '"pattern": "absent-required-producer.py"')]:
            self.write('lean-report-inputs.json', invalid)
            self.build(success=False)
        (self.root / 'lean-report-inputs.json').unlink()
        self.build(success=False)
        self.write('lean-report-inputs.json', original_policy)
        (self.root / 'External.lean').unlink()
        self.build(success=False)
        self.write('External.lean', 'import ClaimSupport\ndef claim : Prop := claimSupport\n')
        self.utility()
        inspector = self.root / 'tools/lean-inspector/Inspector.lean'
        inspector.write_text(inspector.read_text() + '\ndef invalidProducer : False := True.intro\n')
        self.build(success=False)
        self.copy('tools/lean-inspector/Inspector.lean')
        (self.root / 'tools/lean-inspector/materials.py').unlink()
        self.build(success=False)


class NativeModuleFacetTests:
    def test_public_module_report_and_private_job_is_not_a_target(self):
        self.build()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        source = self.root / 'D5/Alone.lean'
        before = self.stamps()
        source.write_text(source.read_text() + '-- public module facet miss\n')
        self.write('activity.jsonl', '')
        self.run_lake('build', 'D5.Alone:report')
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        self.assertEqual([json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()],
                         [dict(kind='extract', count=1)])
        result = self.run_lake('build', 'D5.Alone:inspectorModuleReport', success=False)
        self.assertIn('unknown module facet', result.stdout + result.stderr)
        for index, targets in enumerate([(':report', 'D5.Alone:report'), ('D5.Alone:report', ':report')]):
            with self.subTest(targets=targets):
                source.write_text(source.read_text() + f'-- shared miss {index}\n')
                self.write('activity.jsonl', '')
                self.run_lake('build', *targets)
                records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
                self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertTrue(path.is_file())

        # A required producer failure must fail both public module and package entrypoints.
        producer = self.root / 'tools/lean-inspector/native.py'
        producer.write_text(producer.read_text().replace(
            'def module(root, name, source, utility_path, executable, output, analyzer="", previous=""):',
            'def module(root, name, source, utility_path, executable, output, analyzer="", previous=""):\n'
            '    raise ValueError("required fixture producer failure")').replace(
            'def produce_batch(requests):',
            'def produce_batch(requests):\n    raise ValueError("required fixture producer failure")'))
        source.write_text(source.read_text() + '-- require module production\n')
        result = self.run_lake('build', 'D5.Alone:report', success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
        source.write_text(source.read_text() + '-- require a new native artifact\n')
        result = self.build(success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
