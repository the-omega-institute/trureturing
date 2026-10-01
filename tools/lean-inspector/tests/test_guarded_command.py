"""Lifecycle checks for the native fixture process boundary."""
from test_native_support import *


class GuardedCommandTests(unittest.TestCase):
    """Lifecycle tests need no Lean build, network, or host timing verdict."""
    def setUp(self):
        self.fixture = NativeTestSupport()
        self.fixture.temporary = tempfile.TemporaryDirectory(prefix='inspector-lifecycle.')
        self.fixture.root = Path(self.fixture.temporary.name)
        self.fixture.env = dict(os.environ)
        self.addCleanup(self.fixture.cleanup_fixture)

    def test_artifact_donor_cleanup_failure_fails_owning_suite(self):
        class Consumer(NativeArtifactTestSupport, unittest.TestCase):
            def setUp(self):
                pass

            def test_consumer(self):
                pass

        def prepare(donor):
            donor.temporary = object()
            donor.root = Path('unused-donor')
            donor.addCleanup(donor.cleanup_fixture)

        result = unittest.TestResult()
        with patch.object(NativeTestSupport, 'setUpClass'), \
                patch.object(NativeTestSupport, 'setUp', prepare), \
                patch.object(NativeTestSupport, 'build'), \
                patch.object(NativeArtifactTestSupport, 'inventory', return_value={}), \
                patch.object(NativeTestSupport, 'cleanup_fixture',
                             side_effect=RuntimeError('owned donor cleanup failed')):
            unittest.defaultTestLoader.loadTestsFromTestCase(Consumer).run(result)
        self.assertEqual(result.testsRun, 1)
        self.assertEqual(len(result.errors), 1)
        self.assertIn('owned donor cleanup failed', result.errors[0][1])
        self.assertFalse(result.wasSuccessful())

    def test_dependency_consumers_start_private_and_cold_with_unconsumed_compiler_seed(self):
        class Consumers(NativeDependencyTestSupport, unittest.TestCase):
            def test_first(self):
                self.assertEqual(self.compiler_seed, '/immutable/compiler-stage')
                self.assertEqual((self.root / 'Fixture.lean').read_text(), 'original')
                self.write('Fixture.lean', 'first consumer mutation')
                self.compiler_seed = None

            def test_second(self):
                self.assertEqual(self.compiler_seed, '/immutable/compiler-stage')
                self.assertEqual((self.root / 'Fixture.lean').read_text(), 'original')
                self.assertEqual(self.env['FIXTURE_ROOT'], str(self.root))

        def prepare(donor):
            donor.temporary = tempfile.TemporaryDirectory(prefix='dependency-fixture.')
            donor.addCleanup(donor.cleanup_fixture)
            donor.root = Path(donor.temporary.name)
            donor.env = dict(FIXTURE_ROOT=str(donor.root))
            donor.compiler_seed = '/immutable/compiler-stage'
            donor.write('Fixture.lean', 'original')

        def ensure(donor):
            donor.write('.lake/packages/mathlib/.lake/build/lib/lean/Cache.olean', 'dependency')
            return dict(mathlib_olean_state='warm', project_olean_state='cold')

        result = unittest.TestResult()
        with patch.object(NativeTestSupport, 'setUpClass'), \
                patch.object(NativeTestSupport, 'setUp', prepare), \
                patch.object(NativeTestSupport, 'ensure', autospec=True, side_effect=ensure) as ensured, \
                patch.object(NativeTestSupport, 'build', side_effect=AssertionError('project must stay cold')):
            unittest.defaultTestLoader.loadTestsFromTestCase(Consumers).run(result)
        self.assertEqual(ensured.call_count, 1)
        self.assertEqual(result.testsRun, 2)
        self.assertTrue(result.wasSuccessful(), result.errors + result.failures)
        self.assertFalse(Consumers.donor.root.exists())

    def test_dependency_preparation_rejects_project_outputs_despite_cold_receipt(self):
        class Consumer(NativeDependencyTestSupport, unittest.TestCase):
            def test_consumer(self):
                self.fail('invalid preparation must fail before any consumer')

        def prepare(donor):
            donor.temporary = tempfile.TemporaryDirectory(prefix='dependency-fixture.')
            donor.addCleanup(donor.cleanup_fixture)
            donor.root = Path(donor.temporary.name)
            donor.write('.lake/build/lib/lean/Fixture.olean', 'premature project output')

        result = unittest.TestResult()
        with patch.object(NativeTestSupport, 'setUpClass'), \
                patch.object(NativeTestSupport, 'setUp', prepare), \
                patch.object(NativeTestSupport, 'ensure', return_value=dict(
                    mathlib_olean_state='warm', project_olean_state='cold')):
            unittest.defaultTestLoader.loadTestsFromTestCase(Consumer).run(result)
        self.assertEqual(result.testsRun, 0)
        self.assertEqual(len(result.errors), 1)
        self.assertIn('must not build project/report outputs', result.errors[0][1])
        self.assertFalse(Consumer.donor.root.exists())

    def test_command_preserves_output_and_nonzero_exit(self):
        for enabled, status in [(False, 0), (False, 7), (True, 0), (True, 7)]:
            with self.subTest(enabled=enabled, status=status):
                output = io.StringIO()
                with patch.dict(os.environ, STRATALINT_NATIVE_COMMAND_OBSERVATION='1' if enabled else ''), \
                        patch.object(sys, 'stderr', output):
                    result = self.fixture.guarded_command([sys.executable, '-c',
                        f'import sys; print("out"); print("err", file=sys.stderr); sys.exit({status})'])
                self.assertEqual((result.returncode, result.stdout, result.stderr), (status, 'out\n', 'err\n'))
                if not enabled:
                    self.assertEqual(output.getvalue(), '')
                    continue
                observation = json.loads(output.getvalue().removeprefix('\nNATIVE_COMMAND_OBSERVATION '))
                self.assertEqual(observation['raw_exit'], status)
                self.assertEqual(observation['outcome'], 'returned')
                self.assertGreater(observation['process_scan_count'], 0)
                self.assertIsInstance(observation['process_scan_seconds'], float)
                self.assertIsInstance(observation['elapsed_seconds'], float)

    def test_unavailable_observation_does_not_replace_command_results_or_errors(self):
        output = io.StringIO()
        with patch.dict(os.environ, STRATALINT_NATIVE_COMMAND_OBSERVATION='1'), \
                patch.object(time, 'perf_counter', side_effect=OSError('clock unavailable')), \
                patch('test_native_support.reaped_children_cpu', side_effect=OSError('counter unavailable')), \
                patch.object(sys, 'stderr', output):
            result = self.fixture.guarded_command([sys.executable, '-c', 'raise SystemExit(7)'])
        self.assertEqual(result.returncode, 7)
        observation = json.loads(output.getvalue().removeprefix('\nNATIVE_COMMAND_OBSERVATION '))
        self.assertIsNone(observation['elapsed_seconds'])
        self.assertIsNone(observation['reaped_children_cpu_seconds'])
        self.assertIsNone(observation['process_scan_seconds'])
        self.assertGreater(observation['process_scan_count'], 0)
        launch_error = OSError('original command launch failure')
        with patch.dict(os.environ, STRATALINT_NATIVE_COMMAND_OBSERVATION='1'), \
                patch.object(subprocess, 'Popen', side_effect=launch_error), \
                patch('builtins.print', side_effect=BrokenPipeError('observation output unavailable')):
            with self.assertRaises(OSError) as raised:
                self.fixture.guarded_command(['unused-command'])
        self.assertIs(raised.exception, launch_error)

    def test_sampling_and_cleanup_errors_stop_and_join_observer(self):
        started = threading.Event()
        observers = []
        original_thread = threading.Thread
        class ObservedThread(original_thread):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.join_calls = 0
                observers.append(self)
            def run(self):
                started.set()
                super().run()
            def join(self, timeout=None):
                self.join_calls += 1
                # Infrastructure guard for a broken cancellation path. The
                # verdict below checks settled state, never elapsed time.
                super().join(timeout=5)
        ps = ['ps', '-axo', 'pid=,ppid=,pgid=,lstart=,stat=,command=']
        sampling_error, cleanup_error, fixture_error = (
            subprocess.TimeoutExpired(ps, 5) for _ in range(3))
        failures = iter([sampling_error, cleanup_error, fixture_error])
        def failed_scan(*args, **kwargs):
            if not started.wait(5):
                raise RuntimeError('infrastructure-hang-guard expired: observer never started')
            raise next(failures)
        guard_error = fixture_cleanup_error = None
        try:
            # A live child and frozen command clock prevent deadline expiry
            # from concealing a missing observer cancellation.
            with patch.object(threading, 'Thread', ObservedThread), \
                    patch.object(self.fixture, 'command_clock', return_value=0.0), \
                    patch.object(subprocess, 'check_output', side_effect=failed_scan) as scans:
                try:
                    self.fixture.guarded_command([sys.executable, '-c', 'import signal; signal.pause()'])
                except BaseException as error:
                    guard_error = error
                try:
                    self.fixture.cleanup_fixture()
                except BaseException as error:
                    fixture_cleanup_error = error
                observed = [(thread.is_alive(), thread.daemon, thread.join_calls) for thread in observers]
                commands = list(self.fixture._commands)
                child_alive = commands[0][0].poll() is None if commands else False
                fixture_retained = self.fixture.root.exists()
                finalizer_detached = not self.fixture.temporary._finalizer.alive
        finally:
            # Restore sampling and reclaim the real child/thread before any
            # verdict, including on the prior broken lifecycle or a mutant.
            try:
                self.fixture.cleanup_fixture()
            finally:
                for thread in observers:
                    original_thread.join(thread, timeout=5)
            # Python 3.9's TemporaryDirectory.cleanup is a no-op after detach.
            shutil.rmtree(self.fixture.root, ignore_errors=True)
        self.assertIs(guard_error, cleanup_error)
        self.assertIs(guard_error.__context__, sampling_error)
        self.assertIs(fixture_cleanup_error, fixture_error)
        self.assertEqual(len(commands), 1)
        self.assertTrue(child_alive)
        self.assertTrue(fixture_retained)
        self.assertTrue(finalizer_detached)
        self.assertEqual([call.args[0] for call in scans.call_args_list], [ps] * 3)
        self.assertTrue(all(call.kwargs['timeout'] == 5 for call in scans.call_args_list))
        self.assertFalse(any(thread.is_alive() for thread in observers))
        self.assertIsNotNone(commands[0][0].poll())
        self.assertEqual(observed, [(False, False, 1)], 'failed cleanup must stop and join its observer')

    def test_completion_boundary_survives_delayed_process_sample(self):
        # The child exits during a process-table scan. Advance an injected
        # clock only after the independent completion observation, so scheduler
        # speed cannot decide the before/exact/after-deadline outcomes.
        for completion_time in [119.999, 120.0, 120.001]:
            with self.subTest(completion_time=completion_time):
                release = self.fixture.root / 'release'
                release.unlink(missing_ok=True)
                clock = [0.0]
                sampled = threading.Event()
                owner = threading.get_ident()
                child = []
                original = self.fixture.owned_processes
                original_wait = subprocess.Popen.wait
                def wait(process, timeout=None):
                    result = original_wait(process, timeout)
                    if threading.get_ident() != owner:
                        clock[0] = completion_time
                    return result
                def command_clock():
                    value = clock[0]
                    if threading.get_ident() != owner and value == completion_time:
                        sampled.set()
                    return value
                def delayed_sample(command, *, sessions=False):
                    rows = original(command, sessions=sessions)
                    if not sessions and not child:
                        child.append(command[0])
                        release.touch()
                        command[0].wait(timeout=5)
                        self.assertTrue(sampled.wait(5), 'completion observer did not run')
                        clock[0] = 121.0
                    return rows
                script = ('import sys, time\nfrom pathlib import Path\n'
                          'while not Path(sys.argv[1]).exists(): time.sleep(0.001)\n'
                          'print("finished")\n')
                with patch.object(self.fixture, 'command_clock', side_effect=command_clock), \
                        patch.object(self.fixture, 'owned_processes', side_effect=delayed_sample), \
                        patch.object(subprocess.Popen, 'wait', wait):
                    if completion_time < 120:
                        result = self.fixture.guarded_command([sys.executable, '-c', script, str(release)])
                        self.assertEqual((result.returncode, result.stdout), (0, 'finished\n'))
                    else:
                        with self.assertRaises(subprocess.TimeoutExpired):
                            self.fixture.guarded_command([sys.executable, '-c', script, str(release)])
                self.assertEqual(child[0].returncode, 0)
                self.assertEqual(self.fixture._commands, [])

    def test_timeout_cannot_be_reversed_by_successful_cleanup(self):
        release = self.fixture.root / 'release'
        clock = [0.0]
        child = []
        original_sample = self.fixture.owned_processes
        original_join = self.fixture.join_command
        def sample(command, *, sessions=False):
            rows = original_sample(command, sessions=sessions)
            if not sessions:
                child.append(command[0])
                clock[0] = 120.0
            return rows
        def join(command):
            release.touch()
            command[0].wait(timeout=5)
            original_join(command)
        script = ('import sys, time\nfrom pathlib import Path\n'
                  'while not Path(sys.argv[1]).exists(): time.sleep(0.001)\n')
        with patch.object(self.fixture, 'command_clock', side_effect=lambda: clock[0]), \
                patch.object(self.fixture, 'owned_processes', side_effect=sample), \
                patch.object(self.fixture, 'join_command', side_effect=join):
            with self.assertRaises(subprocess.TimeoutExpired):
                self.fixture.guarded_command([sys.executable, '-c', script, str(release)])
        self.assertEqual(child[0].returncode, 0)
        self.assertEqual(self.fixture._commands, [])

    def test_timeout_joins_writers_across_groups_before_removal(self):
        root = self.fixture.root
        writer = '''import os, signal, sys, time
from pathlib import Path
root, name = Path(sys.argv[1]), sys.argv[2]
signal.signal(signal.SIGTERM, signal.SIG_IGN)
with (root / (name + '.ticks')).open('a') as out:
    out.write('writing\\n'); out.flush()
    (root / (name + '.ready')).write_text(str(os.getpid()))
    while True:
        out.write('writing\\n'); out.flush(); time.sleep(0.01)
'''
        (root / 'writer.py').write_text(writer)
        parent = '''import os, subprocess, sys
from pathlib import Path
root = Path(sys.argv[1])
(root / 'parent.ready').write_text(str(os.getpid()))
children = [subprocess.Popen([sys.executable, str(root / 'writer.py'), str(root), name],
    start_new_session=separate) for name, separate in [('same', False), ('separate', True)]]
for child in children: child.wait()
'''
        self.fixture.write('.lake/build/stratalint/raw-lean-report.json.logs/report.stdout.log', 'report active\n')
        self.fixture.write('.lake/build/stratalint/raw-lean-report.json.logs/native-work.jsonl', '{"kind":"extract"}\n')
        self.fixture.write('tmp/stratalint-inspector-startup.fixture/ensure.stdout.log', 'ensure active\n')
        control = subprocess.Popen([sys.executable, '-c', 'import signal; signal.pause()'])
        self.addCleanup(lambda: (control.kill(), control.wait()) if control.poll() is None else None)
        def safety_cleanup():
            # Also keep a broken/mutated cleanup implementation safe to test.
            for name in ['same', 'separate', 'parent']:
                marker = root / (name + '.ready')
                if marker.exists():
                    pid = int(marker.read_text())
                    row = self.fixture.command_processes().get(pid)
                    if row and str(root) in row['command']:
                        try:
                            os.kill(pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    if name == 'parent':
                        try:
                            os.waitpid(pid, 0)
                        except ChildProcessError:
                            pass
        self.addCleanup(safety_cleanup)
        started = time.monotonic()
        def deadline_after_ready():
            if time.monotonic() - started > 120:
                raise RuntimeError('infrastructure-hang-guard expired: writers never ready')
            return 121 if all((root / (name + '.ready')).exists() for name in ['same', 'separate']) else 0
        with patch.object(self.fixture, 'command_clock', side_effect=deadline_after_ready):
            with self.assertRaises(subprocess.TimeoutExpired) as expired:
                self.fixture.guarded_command([sys.executable, '-c', parent, str(root)])
        self.assertEqual(expired.exception.timeout, 120)
        pids = [int((root / (name + '.ready')).read_text()) for name in ['same', 'separate']]
        for pid in pids:
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)
        self.assertIsNone(control.poll(), 'cleanup must not signal an unrelated process')
        diagnostic = self.fixture.last_command_diagnostic
        self.assertTrue(set(pids).issubset({row['pid'] for row in diagnostic['processes']}))
        groups = {row['pid']: row['group'] for row in diagnostic['processes']}
        self.assertNotEqual(groups[pids[0]], groups[pids[1]])
        self.assertIn('report active', json.dumps(diagnostic))
        self.assertIn('ensure active', json.dumps(diagnostic))
        self.assertIn('extract', json.dumps(diagnostic))
        self.fixture.cleanup_fixture()
        self.assertFalse(root.exists())
        self.assertIsNone(control.poll())
