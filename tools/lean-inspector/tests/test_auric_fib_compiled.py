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
import threading
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
        return True
    except (OSError, ValueError):
        return False


def analyzer_await_interval(path):
    # Require the callback and Inspector join in this fresh command's channel.
    # The byte offset distinguishes two starts even within one clock tick.
    with path.open('rb') as source:
        identity = os.fstat(source.fileno())
        offset = max(0, source.seek(0, 2) - 32768)
        source.seek(offset)
        lines = source.read(32768).splitlines(keepends=True)
    state, interval = None, None
    for line in lines:
        start = offset
        offset += len(line)
        try:
            event = json.loads(line)
        except (ValueError, UnicodeError):
            state, interval = None, None
            continue
        if not isinstance(event, dict) or not line.endswith(b'\n'):
            state, interval = None, None
            continue
        if 'observation' in event:
            if event['observation'] == 'FIB_COMPILED_DIAGNOSTIC_UNAVAILABLE':
                state, interval = None, None
            continue
        phase, boundary = event.get('phase'), event.get('boundary')
        if phase == 'lake-report-programs':
            state, interval = ('programs' if boundary == 'start' else None), None
        elif phase == 'lake-report-programs-callback':
            state = 'callback' if state == 'programs' and boundary == 'start' else None
            interval = None
        elif phase == 'lake-report-inspector':
            state = 'ready' if state == 'callback' and boundary == 'ready' else None
            interval = None
        elif phase == 'lake-analyzer-await':
            if state == 'ready' and boundary == 'start':
                state = 'await'
                interval = (identity.st_dev, identity.st_ino, start, event.get('monotonic_ms'))
            else:
                state, interval = None, None
        elif phase in ('lake-module-report', 'cache-reader') and boundary == 'finish':
            state, interval = None, None
    return interval


def linux_process_identity(pid):
    # starttime disambiguates PID reuse; comm may itself contain parentheses.
    fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
    return int(fields[1]), fields[19]


def linux_report_processes(pid, lake_args):
    identities, lakes = {}, []
    pending = [(pid, None)]
    while pending:
        current, parent = pending.pop()
        identity = linux_process_identity(current)
        if parent is not None and identity[0] != parent:
            raise ValueError('process ancestry changed')
        identities[current] = identity
        if current != pid:
            command = Path(f'/proc/{current}/cmdline').read_bytes().rstrip(b'\0').split(b'\0')
            if (Path(os.fsdecode(command[0])).name == 'lake'
                    and command[1:] == [os.fsencode(arg) for arg in lake_args]):
                lakes.append(current)
        # A .NET worker thread may have spawned Lake, so include every task's children.
        for task in Path(f'/proc/{current}/task').iterdir():
            children = (task / 'children').read_text().split()
            pending.extend((int(child), current) for child in children if int(child) not in identities)
    if len(lakes) != 1:
        raise ValueError('unique invocation Lake PID unavailable')
    return identities, lakes[0]


def observe_report_process(process, phases, lake_args, sequence, stopped):
    payload = dict(sequence=sequence, invocation_pid=process.pid, lake_pid=None,
        status='inconclusive', reason='analyzer-await interval absent, missed or command finished',
        limitation='One instantaneous process view; not a critical path, deadlock or speedup proof. '
                   'Phase and process reads are not atomic; exited or reparented children may be missed. '
                   'Markers are best-effort; a missing finish does not prove the await remained active.')
    try:
        if sys.platform != 'linux':
            payload.update(status='unavailable', reason='Linux process snapshot only')
            return
        if phases is None:
            payload.update(status='unavailable', reason='fresh invocation phase channel unavailable')
            return
        while not stopped.is_set():
            try:
                interval = analyzer_await_interval(phases)
            except FileNotFoundError:
                interval = None
            if interval is not None:
                break
            stopped.wait(0.05)
        else:
            return
        identities, lake_pid = linux_report_processes(process.pid, lake_args)
        payload['lake_pid'] = lake_pid
        if stopped.is_set() or process.poll() is not None or analyzer_await_interval(phases) != interval:
            payload['reason'] = 'command or analyzer-await interval ended before snapshot'
            return
        # Enumerate only this spawned invocation via /proc. ps is read once,
        # with explicit descendant PIDs; unrelated session arguments are never requested.
        selected = set(identities) - {process.pid}
        payload.update(reason='ps pending; no completed snapshot yet', monotonic_ns=time.monotonic_ns(),
            phase='lake-analyzer-await', phase_start_offset=interval[2], phase_start_ms=interval[3])
        if not observe_fib('FIB_COMPILED_PROCESS_SNAPSHOT_PENDING', payload):
            payload.update(status='unavailable', reason='diagnostic sink unwritable')
            return
        snapshot = subprocess.run(['ps', '-p', ','.join(map(str, sorted(selected))), '-o',
            'pid=,ppid=,etimes=,time=,stat=,wchan:32=,args='],
            text=True, capture_output=True, check=False, timeout=1)
        if snapshot.returncode:
            payload.update(status='unavailable', reason='ps failed', ps_exit=snapshot.returncode)
            return
        if (stopped.is_set() or process.poll() is not None or analyzer_await_interval(phases) != interval
                or any(linux_process_identity(pid) != identity for pid, identity in identities.items())):
            payload['reason'] = 'process identity or analyzer-await interval raced snapshot'
            return
        rows, omitted = [], 0
        for line in snapshot.stdout.splitlines():
            fields = line.split(None, 6)
            if len(fields) != 7:
                continue
            pid, parent = int(fields[0]), int(fields[1])
            if pid not in selected or parent != identities[pid][0]:
                continue
            row = dict(pid=pid, ppid=parent, elapsed_seconds=fields[2], cpu_time=fields[3],
                state=fields[4], wait_channel=fields[5], command=fields[6][:512],
                command_truncated=len(fields[6]) > 512)
            if len(json.dumps(rows + [row]).encode()) <= 8192:
                rows.append(row)
            else:
                omitted += 1
        payload.update(status='observed' if any(row['pid'] == lake_pid for row in rows) else 'inconclusive',
            reason='recorded analyzer-await interval bracketed the single ps read', rows=rows, omitted_rows=omitted)
    except Exception as error:
        # Observation failures must not replace the real command outcome.
        payload.update(status='unavailable' if isinstance(error, OSError) else 'inconclusive',
            reason=type(error).__name__)
    finally:
        if not observe_fib('FIB_COMPILED_PROCESS_SNAPSHOT', payload):
            try:
                print('FIB_COMPILED_PROCESS_SNAPSHOT ' + json.dumps(dict(sequence=sequence,
                    invocation_pid=process.pid, status='unavailable', reason='diagnostic sink unwritable')),
                    file=sys.stderr, flush=True)
            except (OSError, ValueError):
                pass


def run_with_report_snapshot(args, env, phases, sequence):
    with subprocess.Popen(args, cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
        stopped = threading.Event()
        observer = None
        try:
            observer = threading.Thread(target=observe_report_process,
                args=(process, phases, args[3:], sequence, stopped), daemon=True)
            observer.start()
        except Exception:
            observe_fib('FIB_COMPILED_PROCESS_SNAPSHOT', dict(status='unavailable', reason='observer start failed'))
        try:
            stdout, stderr = process.communicate()
        finally:
            stopped.set()
            if observer is not None and observer.ident is not None:
                # A stuck ps cannot delay the original result or send signals.
                observer.join(timeout=0.1)
        return subprocess.CompletedProcess(args, process.returncode, stdout, stderr)


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
        snapshot_phases = paths.get('phases')
        for path in paths.values():
            try:
                path.write_bytes(b'')
            except OSError as error:
                if path == snapshot_phases:
                    snapshot_phases = None
                observe_fib('FIB_COMPILED_DIAGNOSTIC_UNAVAILABLE', dict(path=str(path), error=str(error)))
        self.command_sequence = getattr(self, 'command_sequence', 0) + 1
        sequence = self.command_sequence
        observe_fib('FIB_COMPILED_STAGE', dict(stage='command', boundary='start', sequence=sequence,
            command=args, full=full))
        result = None
        try:
            if getattr(self, 'observe_processes', False) and sequence == 1:
                result = run_with_report_snapshot(args, env, snapshot_phases, sequence)
            else:
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
        fixture.observe_processes = True
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
    await_start = ''.join(json.dumps(dict(phase=phase, boundary=boundary, monotonic_ms=index)) + '\n'
        for index, (phase, boundary) in enumerate([
            ('lake-report-programs', 'start'), ('lake-report-programs-callback', 'start'),
            ('lake-report-inspector', 'ready'), ('lake-analyzer-await', 'start')]))

    def test_only_complete_callback_and_inspector_sequence_opens_interval(self):
        events = self.await_start.splitlines(keepends=True)
        finish = '{"phase":"lake-analyzer-await","boundary":"finish"}\n'
        cases = {
            'absent': '', 'outer-boundary': events[0], 'callback-only': ''.join(events[:2]),
            'inspector-only': ''.join(events[:3]), 'await-without-join': events[-1],
            'missing-callback': events[0] + ''.join(events[2:]),
            'missing-inspector': ''.join(events[:2]) + events[-1],
            'observation-is-not-producer-marker': ''.join(events[:3]) +
                '{"observation":"FIB_COMPILED_PROCESS_SNAPSHOT",'
                '"phase":"lake-analyzer-await","boundary":"start"}\n',
            'finished': self.await_start + finish,
            'no-fib': ''.join(events[:3]) + '{"phase":"lake-report-programs","boundary":"finish"}\n',
            'finish-missing-but-report-continued': self.await_start +
                '{"phase":"lake-report-programs","boundary":"finish"}\n',
            'finish-missing-but-command-ended': self.await_start +
                '{"phase":"cache-reader","boundary":"finish","raw_exit":19}\n',
            'broken-json': self.await_start + '{broken\n',
            'wrong-json-type': self.await_start + '[]\n',
            'partial-record': self.await_start + finish.rstrip('\n'),
            'unavailable': self.await_start +
                '{"observation":"FIB_COMPILED_DIAGNOSTIC_UNAVAILABLE"}\n',
            'prefix-outside-tail': self.await_start + ('{}\n' * 12000),
        }
        process = type('Process', (), {'pid': 100, 'poll': lambda self: None})()
        with tempfile.TemporaryDirectory() as directory:
            phases = Path(directory) / 'phases'
            phases.write_text(self.await_start)
            self.assertIsNotNone(analyzer_await_interval(phases))
            for name, contents in cases.items():
                with self.subTest(case=name):
                    phases.write_text(contents)
                    self.assertIsNone(analyzer_await_interval(phases))
                    stopped = threading.Event()
                    with (patch(__name__ + '.observe_fib', return_value=True) as sink,
                          patch.object(sys, 'platform', 'linux'),
                          patch.object(stopped, 'wait', side_effect=lambda _: stopped.set()),
                          patch.object(subprocess, 'run') as ps):
                        observe_report_process(process, phases, [], 1, stopped)
                    ps.assert_not_called()
                    sink.assert_called_once()
                    snapshot = sink.call_args.args[1]
                    self.assertEqual(snapshot['status'], 'inconclusive')
                    self.assertNotIn('rows', snapshot)

    def test_interval_ending_before_ps_spends_no_sample(self):
        process = type('Process', (), {'pid': 100, 'poll': lambda self: None})()
        with tempfile.TemporaryDirectory() as directory:
            phases = Path(directory) / 'phases'
            phases.write_text(self.await_start)
            def ended(*args):
                with phases.open('a') as target:
                    target.write('{"phase":"lake-analyzer-await","boundary":"finish"}\n')
                return {100: (1, '10'), 101: (100, '11')}, 101
            with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', Path(directory)),
                  patch.object(sys, 'platform', 'linux'),
                  patch(__name__ + '.linux_report_processes', side_effect=ended),
                  patch.object(subprocess, 'run') as ps):
                observe_report_process(process, phases, [], 1, threading.Event())
            ps.assert_not_called()
            snapshot = json.loads(phases.read_text().splitlines()[-1])
            self.assertEqual(snapshot['status'], 'inconclusive')
            self.assertIn('before snapshot', snapshot['reason'])

    def test_failed_pending_sink_or_unsupported_platform_cannot_claim_sample(self):
        process = type('Process', (), {'pid': 100, 'poll': lambda self: None})()
        for case in ('failed-sink', 'non-linux'):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                phases = Path(directory) / 'phases'
                phases.write_text(self.await_start)
                error = io.StringIO()
                with (patch.object(sys, 'platform', 'linux' if case == 'failed-sink' else 'darwin'),
                      patch(__name__ + '.linux_report_processes',
                          return_value=({100: (1, '10'), 101: (100, '11')}, 101)),
                      patch(__name__ + '.observe_fib', return_value=False),
                      patch.object(sys, 'stderr', error), patch.object(subprocess, 'run') as ps):
                    observe_report_process(process, phases, [], 1, threading.Event())
                ps.assert_not_called()
                snapshot = json.loads(error.getvalue().split(' ', 1)[1])
                self.assertEqual(snapshot['status'], 'unavailable')
                self.assertNotIn('rows', snapshot)

    def test_missed_interval_does_not_hold_command_open_for_sampling(self):
        for exit_code in (0, 19):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as directory:
                phases = Path(directory) / 'phases'
                phases.write_text(self.await_start +
                    '{"phase":"lake-analyzer-await","boundary":"finish"}\n')
                script = "import sys; print('out'); print('err', file=sys.stderr); sys.exit(int(sys.argv[1]))"
                with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', Path(directory)),
                      patch.object(sys, 'platform', 'linux'), patch.object(subprocess, 'run') as ps):
                    result = run_with_report_snapshot([sys.executable, '-c', script, str(exit_code)],
                        dict(os.environ), phases, 1)
                ps.assert_not_called()
                self.assertEqual((result.returncode, result.stdout, result.stderr),
                    (exit_code, 'out\n', 'err\n'))
                self.assertEqual(json.loads(phases.read_text().splitlines()[-1])['status'], 'inconclusive')

    def test_unreset_phase_channel_cannot_bind_stale_boundary(self):
        fixture = CompiledFibIntegration()
        fixture.observe_processes = True
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            phases = root / 'phases'
            phases.write_text(self.await_start)
            fixture.activity = root / 'activity'
            fixture.env = dict(os.environ, STRATALINT_INSPECTOR_PHASES=str(phases))
            with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', root),
                  patch.object(sys, 'platform', 'linux'),
                  patch.object(Path, 'write_bytes', side_effect=PermissionError('phase reset refused')),
                  patch.object(subprocess, 'run') as ps):
                result = fixture.command([sys.executable, '-c',
                    "import sys; print('out'); print('err', file=sys.stderr); sys.exit(19)"], expected=19)
            ps.assert_not_called()
            self.assertEqual((result.returncode, result.stdout, result.stderr), (19, 'out\n', 'err\n'))
            snapshots = [json.loads(line) for line in phases.read_text().splitlines()
                if '"observation": "FIB_COMPILED_PROCESS_SNAPSHOT"' in line]
            self.assertEqual(len(snapshots), 1)
            self.assertEqual(snapshots[0]['status'], 'unavailable')
            self.assertEqual(snapshots[0]['reason'], 'fresh invocation phase channel unavailable')

    def test_linux_tree_binds_exact_lake_child_in_worker_thread(self):
        args = ['-d', 'project', 'build', 'fixture:report']
        parents = {100: 1, 101: 100, 102: 101}
        children = {'/proc/100/task/100/children': '', '/proc/100/task/107/children': '101',
                    '/proc/101/task/101/children': '102', '/proc/102/task/102/children': ''}
        def read_text(path):
            if path.name == 'stat':
                pid = int(path.parent.name)
                return f'{pid} (process ) name) S {parents[pid]} ' + '0 ' * 17 + str(pid * 10)
            return children[str(path)]
        def tasks(path):
            pid = int(path.parent.name)
            return [path / str(task) for task in ([100, 107] if pid == 100 else [pid])]
        def command(path):
            pid = int(path.parent.name)
            return b'\0'.join(os.fsencode(arg) for arg in
                (['/toolchain/bin/lake'] + args if pid == 102 else ['dotnet', 'producer.dll'])) + b'\0'
        with (patch.object(Path, 'read_text', autospec=True, side_effect=read_text),
              patch.object(Path, 'read_bytes', autospec=True, side_effect=command) as reads,
              patch.object(Path, 'iterdir', autospec=True, side_effect=tasks)):
            identities, lake = linux_report_processes(100, args)
            self.assertEqual(lake, 102)
            self.assertEqual(identities, {pid: (parent, str(pid * 10)) for pid, parent in parents.items()})
            self.assertEqual([call.args[0] for call in reads.call_args_list],
                [Path('/proc/101/cmdline'), Path('/proc/102/cmdline')])
            with self.assertRaisesRegex(ValueError, 'unique invocation Lake PID'):
                linux_report_processes(100, ['wrong', 'report'])

    def test_snapshot_filters_descendants_and_bounds_commands_with_one_ps(self):
        process = type('Process', (), {'pid': 100, 'poll': lambda self: None})()
        identities = {100: (1, '10'), 101: (100, '11'), 102: (101, '12')}
        with tempfile.TemporaryDirectory() as directory:
            phases = Path(directory) / 'phases'
            phases.write_text(self.await_start)
            output = '101 100 5 00:00:01 Sl futex lake -d project build fixture:report\n'
            output += '102 101 4 00:00:02 R - lean ' + 'x' * 20000 + '\n'
            output += '999 1 9 00:00:09 S wait PRIVATE_OTHER_SESSION\n'
            with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', Path(directory)),
                  patch.object(sys, 'platform', 'linux'),
                  patch(__name__ + '.linux_report_processes', return_value=(identities, 101)),
                  patch(__name__ + '.linux_process_identity', side_effect=identities.__getitem__),
                  patch.object(subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, output, '')) as ps):
                observe_report_process(process, phases, ['-d', 'project'], 1, threading.Event())
            ps.assert_called_once()
            self.assertEqual(ps.call_args.args[0][0:3], ['ps', '-p', '101,102'])
            self.assertEqual(ps.call_args.kwargs['timeout'], 1)
            events = [json.loads(line) for line in phases.read_text().splitlines()]
            snapshot = events[-1]
            self.assertEqual(snapshot['status'], 'observed')
            self.assertEqual(snapshot['phase'], 'lake-analyzer-await')
            self.assertEqual(snapshot['phase_start_ms'], 3)
            self.assertEqual((snapshot['invocation_pid'], snapshot['lake_pid']), (100, 101))
            self.assertEqual([row['pid'] for row in snapshot['rows']], [101, 102])
            self.assertTrue(snapshot['rows'][1]['command_truncated'])
            self.assertLessEqual(len(json.dumps(snapshot['rows']).encode()), 8192)
            self.assertNotIn('PRIVATE_OTHER_SESSION', phases.read_text())

    def test_snapshot_unavailable_and_races_do_not_retry_or_claim_observation(self):
        process = type('Process', (), {'pid': 100, 'poll': lambda self: None})()
        identities = {100: (1, '10'), 101: (100, '11')}
        for case in ('missing-ps', 'failed-ps', 'ps-timeout', 'missing-child', 'pid-reused',
                     'phase-finished', 'phase-restarted', 'phase-replaced', 'command-ended', 'no-phase'):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                phases = Path(directory) / 'phases'
                phases.write_text(self.await_start)
                stop = threading.Event()
                if case == 'no-phase':
                    phases.write_text('')
                    stop.set()
                def ps_result(*args, **kwargs):
                    if case == 'missing-ps':
                        raise FileNotFoundError('ps')
                    if case == 'ps-timeout':
                        raise subprocess.TimeoutExpired('ps', 1)
                    if case == 'phase-finished':
                        with phases.open('a') as target:
                            target.write('{"phase":"lake-analyzer-await","boundary":"finish"}\n')
                    if case == 'phase-restarted':
                        with phases.open('a') as target:
                            target.write(self.await_start)
                    if case == 'phase-replaced':
                        replacement = phases.with_suffix('.replacement')
                        replacement.write_text(self.await_start)
                        replacement.replace(phases)
                    if case == 'command-ended':
                        stop.set()
                    return subprocess.CompletedProcess([], 1 if case == 'failed-ps' else 0,
                        '101 100 5 00:00:01 S wait lake\n', '')
                with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', Path(directory)),
                      patch.object(sys, 'platform', 'linux'),
                      patch(__name__ + '.linux_report_processes',
                          side_effect=ValueError('no Lake') if case == 'missing-child' else None,
                          return_value=(identities, 101)),
                      patch(__name__ + '.linux_process_identity',
                          side_effect=lambda pid: (1, 'reused') if case == 'pid-reused' else identities[pid]),
                      patch.object(subprocess, 'run', side_effect=ps_result) as ps):
                    observe_report_process(process, phases, [], 1, stop)
                self.assertEqual(ps.call_count, 0 if case in ('missing-child', 'no-phase') else 1)
                snapshot = json.loads(phases.read_text().splitlines()[-1])
                self.assertIn(snapshot['status'], ('unavailable', 'inconclusive'))
                self.assertNotIn('rows', snapshot)

    def test_observed_small_child_preserves_streams_and_exit_with_failed_diagnostics(self):
        for exit_code, blocked in ((0, False), (19, False), (37, True)):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                phases = root / 'phases'
                if blocked:
                    phases.mkdir()
                script = '''import sys, time
from pathlib import Path
path = Path(sys.argv[1])
if not path.is_dir():
    path.write_text(sys.argv[3])
    deadline = time.monotonic() + 2
    while '"observation": "FIB_COMPILED_PROCESS_SNAPSHOT"' not in path.read_text():
        assert time.monotonic() < deadline, 'observer did not settle'
        time.sleep(0.01)
print('original out')
print('original err', file=sys.stderr)
sys.exit(int(sys.argv[2]))
'''
                identities = {}
                def process_tree(pid, args):
                    identities.update({pid: (1, 'a'), pid + 1: (pid, 'b')})
                    return identities, pid + 1
                def ps_result(*args, **kwargs):
                    if exit_code != 0:
                        raise FileNotFoundError('ps')
                    pid = max(identities)
                    return subprocess.CompletedProcess([], 0,
                        f'{pid} {pid-1} 1 00:00:00 S wait lake\n', '')
                with (patch.object(sys.modules[__name__], 'DIAGNOSTICS', root),
                      patch.object(sys, 'platform', 'linux'),
                      patch(__name__ + '.linux_report_processes', side_effect=process_tree),
                      patch(__name__ + '.linux_process_identity', side_effect=identities.__getitem__),
                      patch.object(subprocess, 'run', side_effect=ps_result) as ps):
                    result = run_with_report_snapshot([sys.executable, '-c', script, str(phases), str(exit_code), self.await_start],
                        dict(os.environ), phases, 1)
                self.assertEqual((result.returncode, result.stdout, result.stderr),
                    (exit_code, 'original out\n', 'original err\n'))
                self.assertEqual(ps.call_count, 0 if blocked else 1)

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
