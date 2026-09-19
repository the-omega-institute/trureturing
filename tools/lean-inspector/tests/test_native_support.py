"""Execute native Lake facets in private pinned-toolchain fixture packages."""
import hashlib
import io
import json
import os
import signal
from pathlib import Path
import shutil
import shlex
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile
import zlib

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
ROOT = Path(os.environ.get('STRATALINT_NATIVE_SOURCE_ROOT', ROOT)).resolve()
sys.path.insert(0, str(HERE))
import publication
import materials
import native



class NativeTestSupport:
    @classmethod
    def setUpClass(cls):
        cls.lake = os.environ.get('STRATALINT_NATIVE_LAKE_BIN') or subprocess.check_output(
            ['elan', 'which', 'lake'], cwd=ROOT, text=True).strip()
        cls.dotnet = shutil.which('dotnet')
        cls.cli = Path(os.environ.get('STRATALINT_NATIVE_DOTNET_CLI',
            ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'))
        if not cls.dotnet or not cls.cli.is_file():
            raise RuntimeError('native fixtures require make -C tools dotnet first')
    def setUp(self):
        self._fixture_started = time.monotonic()
        self._fixture_setup_seconds = 0
        self.temporary = tempfile.TemporaryDirectory(prefix='inspector-native.',
            dir=os.environ.get('STRATALINT_NATIVE_TMPDIR'))
        self.addCleanup(self.cleanup_fixture)
        self.root = Path(self.temporary.name)
        self.write('lakefile.toml', '''name = "fixture"
defaultTargets = ["Fixture", "Audit"]
moreLeanArgs = ["-Dweak.compilerOrigin=true"]
[[require]]
name = "leanInspector"
path = "tools/lean-inspector"
[[require]]
name = "mathlib"
path = "fixture-mathlib"
[[lean_lib]]
name = "Fixture"
needs = ["leanInspector/compilerInput"]
roots = ["Fixture", "D5"]
globs = ["Fixture", "D5.+"]
[[lean_lib]]
name = "Audit"
needs = ["leanInspector/compilerInput"]
globs = ["Audit"]
defaultFacets = ["static"]
[[lean_exe]]
name = "cache"
root = "Cache"
''')
        # No external dependencies need downloading. Let the actual ensure
        # owner invoke this fixture cache provider before the first raw Lake
        # build; only that owner creates the stamp and admits donor seeding.
        self.write('fixture-mathlib/lakefile.toml', 'name = "mathlib"\n')
        self.write('fixture-mathlib/lake-manifest.json', '{"version":"1.2.0","packages":[]}\n')
        self.write('Cache.lean', 'def main : IO Unit := pure ()\n')
        self.write('lake-manifest.json', json.dumps(dict(version='1.2.0',
            packagesDir='.lake/packages', packages=[dict(type='path', scope='',
                name='leanInspector', manifestFile='lake-manifest.json', inherited=False,
                dir='tools/lean-inspector', configFile='lakefile.lean'),
                dict(type='path', scope='', name='mathlib', manifestFile='lake-manifest.json', inherited=False,
                    dir='fixture-mathlib', configFile='lakefile.toml', rev='0123456789abcdef0123456789abcdef01234567')],
            name='fixture', lakeDir='.lake', fixedToolchain=False)))
        self.write('Fixture.lean', 'import D5.A\ntheorem result : ¬ False := fun h => h\n')
        self.write('D5/A.lean', 'import D5.B\ndef value : Nat := D5.hidden\n')
        self.write('D5/B.lean', 'module\npublic section\nnamespace D5\nprivate def secret : Nat := 1\ndef hidden : Nat := secret\n')
        self.write('D5/Alone.lean', 'def alone : String := "λ😀𐀀"\nopaque concealed : Nat := 7\n')
        self.write('External.lean', 'import ClaimSupport\ndef claim : Prop := claimSupport\n')
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := False\n')
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        self.write('LeanInformationAudit/Registry.lean', 'def fixtureDriver : Nat := 1\n')
        with (self.root / 'lakefile.toml').open('a') as target:
            target.write('[[lean_lib]]\nname = "External"\nneeds = ["leanInspector/compilerInput"]\n'
                '[[lean_lib]]\nname = "ClaimSupport"\nneeds = ["leanInspector/compilerInput"]\n')
            target.write('[[lean_lib]]\nname = "LeanInformationAudit"\nneeds = ["leanInspector/compilerInput"]\n'
                'globs = ["LeanInformationAudit.+"]\n')
        for name in ['Inspector.lean', 'lakefile.lean', 'lake-manifest.json', 'template-plan-inputs.json', 'native.py', 'native_image.c', 'publication.py', 'materials.py', 'reuse.py', 'inspect.sh']:
            self.copy('tools/lean-inspector/' + name)
        shutil.copytree(HERE / 'compiler', self.root / 'tools/lean-inspector/compiler', ignore=shutil.ignore_patterns('__pycache__'))
        # These native-facet fixtures test statement extraction and publication,
        # with no D5 registration library. Use the explicit statement-only API;
        # their reports cannot satisfy the declared-template admission reader.
        inspector = self.root / 'tools/lean-inspector/Inspector.lean'
        source = inspector.read_text()
        entry = '  let statementOnly := args.head? == some "--statements-only"'
        if source.count(entry) != 1:
            raise RuntimeError('statement fixture inspector entry is missing')
        inspector.write_text(source.replace(entry,
            '  let args := "--statements-only" :: args\n' + entry))
        for name in ['tools/scripts/report/lean-report-selection.py', 'tools/scripts/report/lean-report-input.sh',
                     'tools/scripts/worktree/lean-cache-input.sh', 'tools/scripts/worktree/lean_cache.py',
                     'tools/scripts/worktree/cache_material.py', 'tools/scripts/worktree/cache_deadline.py',
                     'lean-toolchain', 'Makefile',
                     'tools/scripts/worktree/lean-cache-ensure.sh', 'tools/scripts/worktree/lean-cache-run.sh',
                     'tools/scripts/report/lean-report.sh', 'tools/scripts/report/report-supervisor.sh',
                     'tools/scripts/lib/resource-observation-lib.sh',
                     'tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs']:
            self.copy(name)
        self.write('bin/dotnet', '#!/usr/bin/env python3\nimport os, sys\nfrom pathlib import Path\n'
            + f'dotnet, cli = {self.dotnet!r}, {str(self.cli)!r}\n'
            + 'operation = next((word for word in sys.argv if word in ("ensure-cache", "with-cache-writer", "with-cache-reader")), None)\n'
            + 'if operation: os.execv(dotnet, [dotnet, cli, *sys.argv[sys.argv.index(operation):]])\n'
            + 'if sys.argv[1] == "build": raise SystemExit(0)  # utility input is fixture data\n'
            + 'if sys.argv[-1] != "lean-utility-input": raise SystemExit("unexpected fixture dotnet command")\n'
            + 'with Path("utility-calls").open("a") as out: out.write("call\\n")\n'
            + 'print(Path("utility.json").read_text())\n')
        (self.root / 'bin/dotnet').chmod(0o755)
        self.utility()
        paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
        policy = dict(schema_version=1, report_semantic_version=1, report_modules=paths('Fixture.lean', 'D5/**/*.lean'),
            inspector_sources=paths('tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean'),
            dependency_sources=paths('External.lean', 'ClaimSupport.lean', 'LeanInformationAudit/Registry.lean'),
            config_inputs=paths('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'),
            producer_scopes={'lean-report': paths('lean-report-inputs.json', 'tools/scripts/report/lean-report-selection.py',
                'tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean',
                'tools/lean-inspector/template-plan-inputs.json',
                'tools/lean-inspector/native.py', 'tools/lean-inspector/native_image.c', 'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                'tools/lean-inspector/compiler/*.py', 'tools/lean-inspector/compiler/*.lean',
                'tools/lean-inspector/compiler/*.patch', 'tools/lean-inspector/compiler/LICENSE*',
                'tools/scripts/report/lean-report-input.sh', 'tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs'),
                'scribe-content': dict(include=[], exclude=[])})
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'], LAKE_BIN=self.lake,
            LAKE_CACHE_DIR=str(self.root / '.lake/artifact-cache'), LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true',
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(self.root / '.lake/input-memo'),
            STRATALINT_INSPECTOR_ACTIVITY=str(self.root / 'activity.jsonl'))
        self.compiler_seed = self.env.pop('STRATALINT_NATIVE_COMPILER_SEED', None)
        self.compiler_distribution_seed = self.compiler_seed
        # A fresh synthetic Git repository bounds ensure donor discovery to
        # this fixture. The compiler stage is restored separately after ensure.
        subprocess.run(['git', 'init', '--quiet', str(self.root)], check=True, capture_output=True)
        self._fixture_setup_seconds = time.monotonic() - self._fixture_started
    command_clock = staticmethod(time.monotonic)

    @staticmethod
    def command_processes():
        # Same PID/start identity discipline as report-supervisor; ancestry and
        # sessions, rather than process groups, include its nested worker group.
        output = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid=,lstart=,stat=,command='],
            text=True, env=dict(os.environ, LC_ALL='C'), timeout=5)
        rows = {}
        for line in output.splitlines():
            fields = line.split(None, 9)
            if len(fields) == 10:
                pid, parent, group = map(int, fields[:3])
                rows[pid] = dict(pid=pid, parent=parent, group=group,
                    identity=' '.join(fields[3:8]), state=fields[8], command=fields[9])
        return rows

    def owned_processes(self, command, *, sessions=False):
        process, identities = command
        rows = self.command_processes()
        owned = {pid for pid, identity in identities.items()
                 if pid in rows and rows[pid]['identity'] == identity}
        if process.poll() is None and process.pid in rows:
            owned.add(process.pid)
        if sessions:
            # A short-lived parent may exit between samples. Its reparented
            # children still belong to this command's private session, even
            # after a supervisor calls setpgid. Never signal by name or cwd.
            for pid in rows:
                try:
                    if os.getsid(pid) == process.pid:
                        owned.add(pid)
                except ProcessLookupError:
                    pass
        while True:
            children = {pid for pid, row in rows.items() if row['parent'] in owned}
            if children <= owned:
                break
            owned.update(children)
        for pid in owned:
            identities[pid] = rows[pid]['identity']
        return [rows[pid] for pid in owned if not rows[pid]['state'].startswith('Z')]

    def command_diagnostics(self, command, args, stdout, stderr, timeout=120):
        roots = [self.root / '.lake/build/stratalint', self.root / 'tmp']
        supervisor = Path(self.env.get('STRATALINT_SUPERVISOR_ROOT', self.root / 'tmp/supervisor'))
        if supervisor.is_relative_to(self.root):
            roots.append(supervisor)
        logs = {}
        for directory in roots:
            for path in directory.rglob('*'):
                if path.is_file() and (path.suffix in {'.log', '.jsonl'} or path.name == 'process-candidates'):
                    try:
                        logs[str(path.relative_to(self.root))] = path.read_bytes()[-16384:].decode('utf-8', 'replace')
                    except FileNotFoundError:
                        pass  # A live phase may be moving startup logs to final.
        diagnostic = dict(command=list(args), timeout_seconds=timeout, fixture=str(self.root),
            processes=self.owned_processes(command, sessions=True), logs=logs,
            stdout=stdout, stderr=stderr)
        self.last_command_diagnostic = diagnostic
        print('NATIVE_COMMAND_TIMEOUT ' + json.dumps(diagnostic), file=sys.stderr, flush=True)
        if hasattr(self, '_testMethodName'):
            self.record_result('timeout', diagnostic)

    def join_command(self, command):
        process, _ = command
        deadline = time.monotonic() + 10  # Cleanup grace, never command success.
        terminate_until = time.monotonic() + 1
        while True:
            rows = self.owned_processes(command, sessions=True)
            if not rows:
                process.wait(timeout=max(0.01, deadline - time.monotonic()))
                return
            if time.monotonic() >= deadline:
                raise RuntimeError('owned native processes survived cleanup; fixture retained: ' + repr(rows))
            # Leaves first lets make/dotnet/supervisors reap their own children.
            parents = {row['parent'] for row in rows}
            for row in rows:
                if row['pid'] in parents:
                    continue
                try:
                    current = self.command_processes().get(row['pid'])
                    if current and current['identity'] == row['identity']:
                        os.kill(row['pid'], signal.SIGTERM if time.monotonic() < terminate_until else signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(0.05)

    def cleanup_fixture(self):
        started = time.monotonic()
        try:
            for command in getattr(self, '_commands', []):
                self.join_command(command)
        except BaseException:
            # TemporaryDirectory's finalizer must not delete under live writers.
            self.temporary._finalizer.detach()
            raise
        self.temporary.cleanup()
        if hasattr(self, '_fixture_started'):
            self.record_result('lifecycle', dict(
                setup_seconds=round(self._fixture_setup_seconds, 3),
                body_seconds=round(started - self._fixture_started - self._fixture_setup_seconds, 3),
                cleanup_seconds=round(time.monotonic() - started, 3),
                fixture_removed=not self.root.exists(), owned_live_processes=0))

    def guarded_command(self, args, *, cwd=None, env=None, text=True, capture_output=True, timeout=120):
        if not 0 < timeout < float('inf') or not text or not capture_output:
            raise ValueError('native fixture commands require a finite positive guard and text capture')
        temporary = self.root / 'tmp'
        temporary.mkdir(exist_ok=True)
        environment = dict(self.env if env is None else env, TMPDIR=str(temporary))
        environment.setdefault('STRATALINT_SUPERVISOR_ROOT', str(temporary / 'supervisor'))
        started = self.command_clock()
        # Files keep output draining independent of descendant pipe lifetimes.
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            process = subprocess.Popen(args, cwd=cwd or self.root, env=environment,
                stdout=stdout, stderr=stderr, start_new_session=True)
            command = (process, {})
            if not hasattr(self, '_commands'):
                self._commands = []
            self._commands.append(command)
            try:
                while True:
                    self.owned_processes(command)
                    if self.command_clock() - started >= timeout:
                        stdout.seek(0); stderr.seek(0)
                        out, err = stdout.read().decode('utf-8', 'replace'), stderr.read().decode('utf-8', 'replace')
                        self.command_diagnostics(command, args, out, err, timeout)
                        raise subprocess.TimeoutExpired(args, timeout, output=out, stderr=err)
                    if process.poll() is not None:
                        break
                    time.sleep(0.1)
            finally:
                self.join_command(command)
                self._commands.remove(command)
                if getattr(self, 'last_command_diagnostic', {}).get('command') == list(args):
                    print('NATIVE_COMMAND_CLEANUP ' + json.dumps(dict(
                        pid=process.pid, owned_live_processes=0, direct_child_exit=process.returncode)),
                        file=sys.stderr, flush=True)
            stdout.seek(0); stderr.seek(0)
            return subprocess.CompletedProcess(args, process.returncode,
                stdout.read().decode('utf-8', 'replace'), stderr.read().decode('utf-8', 'replace'))

    def ensure(self):
        result = self.guarded_command(['make', 'lean-cache-ensure'], cwd=self.root, env=self.env,
            text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return json.loads(next(line.removeprefix('LEAN_CACHE ') for line in result.stdout.splitlines()
                               if line.startswith('LEAN_CACHE ')))
    def copy(self, name):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
        target.chmod(0o755 if name.endswith('.sh') else 0o644)
    def write(self, name, value):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)
    def utility(self, claim='claim'):
        self.write('utility.json', json.dumps([dict(modulePath='Fixture.lean', claimGid='claim-gid', claimModule='External',
            claimSelector=claim, claimSourcePath='External.lean', claimSourceSha256='sha256:' + publication.digest(self.root / 'External.lean'),
            resultGid='result-gid', resultModule='Fixture', resultSelector='result')]))
    def run_lake(self, *args, success=True):
        self.ensure()
        if self.compiler_distribution_seed is not None:
            # The collection owns this read-only stage. Restore the producer's
            # descriptor-checked compiler distribution privately before Lake
            # evaluates the staged producer artifacts. Lake then copies only
            # its registered outputs into this fixture's private cache; current
            # input traces still decide whether any artifact is usable.
            restored = self.guarded_command([sys.executable, '-B',
                str(self.root / 'tools/lean-inspector/compiler/build.py'), 'restore', self.compiler_distribution_seed],
                cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
            self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
            self.compiler_distribution_seed = None
        if self.compiler_seed is not None:
            restored = self.guarded_command([self.lake, 'cache', 'unstage', self.compiler_seed, 'leanInspector'],
                cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
            self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
            self.compiler_seed = None
        started = time.monotonic()
        result = self.guarded_command(['python3', '-B', str(self.root / 'tools/lean-inspector/compiler/build.py'),
            'run', 'lake', *args], cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        checks = getattr(self, '_lake_checks', [])
        text = result.stdout + result.stderr
        checks.append(dict(command=list(args), exit=result.returncode,
            seconds=round(time.monotonic() - started, 3),
            compiler_patched_modules=text.count('patching file '),
            built=sum('Built ' in line for line in text.splitlines()),
            extract_lines=[line for line in text.splitlines() if 'LEAN_INSPECTOR_EXTRACT' in line]))
        self._lake_checks = checks
        self.record_result('lake-commands', dict(checks=checks))
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        elif success is False:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result
    def build(self, success=True):
        self.write('activity.jsonl', '')
        return self.run_lake('build', ':report', success=success)
    def stamps(self):
        return {p.stem: (p.stat().st_mtime_ns, publication.digest(p)) for p in (self.root / '.lake/build/lean-inspector/modules').glob('*.zip')}
    def report(self):
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            report = publication.unpack(self.root / '.lake/build/lean-inspector/report.zip', directory)
            rows = publication.validate_bundle(report, manifest=self.root / 'lean-report-inputs.json')
            return rows, report.read_bytes(), publication.member(report, '.materials.zip').read_bytes()
    def origins(self):
        with zipfile.ZipFile(self.root / '.lake/build/lean-inspector/report.zip') as archive:
            return json.loads(archive.read(publication.RAW + '.provenance.json'))['module_origins']
    def record_result(self, phase, result, paths=()):
        """Optional external, reviewable fixture data; never a test oracle."""
        if output := os.environ.get('STRATALINT_NATIVE_RESULT_DIR'):
            output = Path(output) / self._testMethodName / phase
            output.mkdir(parents=True, exist_ok=True)
            for path in paths:
                destination = output / path.relative_to(self.root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, destination)
            (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    def publish(self):
        result = self.guarded_command([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
            'publish', str(self.root), str(self.root / 'public.json')], env=self.env,
            text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        publication.validate_bundle(self.root / 'public.json', publication.coordinates(self.root), self.root)
        result = self.guarded_command(['bash', str(self.root / 'tools/scripts/report/lean-report-input.sh'),
            'verify', '--repository', str(self.root), '--report', str(self.root / 'public.json')],
            env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    def check_row_decoder_recovery(self, damage, exception, *, no_build=False):
        self.build()
        before = self.stamps()
        expected_report = self.report()
        origins = self.origins()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        expected = path.read_bytes()
        self.record_result('valid', dict(artifact_sha256=publication.digest(path),
            rows=expected_report[0], origins=origins), [path])
        damaged = damage(expected)
        # Establish the real decoder failure before testing Lake's optional-row
        # recovery. Replace the private path, never a native-cache hard link.
        path.unlink()
        path.write_bytes(damaged)
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            with self.assertRaises(exception):
                report = publication.unpack(path, directory, ('', '.materials.zip', '.provenance.json'))
                publication.validate_rows(report, publication.member(report, '.materials.zip'),
                    manifest=self.root / 'lean-report-inputs.json')
        self.record_result('damaged', dict(artifact_sha256=publication.digest(path),
            exception=exception.__name__), [path])
        if no_build:
            self.write('activity.jsonl', '')
            stamp = (path.stat().st_ino, path.stat().st_mtime_ns)
            rejected = self.run_lake('--no-build', 'build', ':report', success=False)
            result = dict(exit_code=rejected.returncode,
                needs_rebuild='needs to be rebuilt' in rejected.stdout + rejected.stderr,
                no_activity=(self.root / 'activity.jsonl').read_text() == '',
                artifact_unchanged=path.read_bytes() == damaged and
                    stamp == (path.stat().st_ino, path.stat().st_mtime_ns))
            self.record_result('no-build', result)
            self.assertTrue(result['no_activity'])
            self.assertTrue(result['artifact_unchanged'])
        recovered = self.build(success=None)
        self.record_result('recovery', dict(exit_code=recovered.returncode,
            private_rebuilds=(recovered.stdout + recovered.stderr).count(
                'inspector artifact rejected; rebuilding privately'),
            decoder_escaped='LZMAError:' in recovered.stdout + recovered.stderr))
        self.assertEqual(recovered.returncode, 0, recovered.stdout + recovered.stderr)
        if no_build:
            self.assertTrue(result['needs_rebuild'], rejected.stdout + rejected.stderr)
        self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1, 'reconstruction must be private')
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), origins)
        self.record_result('recovered', dict(artifact_sha256=publication.digest(path),
            extraction_count=sum(row['count'] for row in records if row['kind'] == 'extract'),
            private_links=path.stat().st_nlink, report_matches_valid=True, origins_preserved=True), [path])
    def encrypted_member(self, data):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            offset = archive.start_dir + 8
        damaged = bytearray(data)
        self.assertEqual(damaged[offset] & 1, 0)
        damaged[offset] ^= 1
        return bytes(damaged)
    def check_census_modes(self, rows):
        module = next(row for row in rows if row['module'] == 'D5.B')
        hidden = next(decl for decl in module['declarations'] if decl['name'] == 'D5.hidden')
        secret = next(decl for decl in module['declarations'] if decl['name'].endswith('.secret'))
        olean = self.root / '.lake/build/lib/lean/D5/B.olean'
        parts = [str(olean) + suffix for suffix in ['', '.server', '.private']]
        self.write('dependencies.json', json.dumps([['D5.B', parts]]))
        self.write('identity.json', json.dumps({'keys': [['D5.B', hidden['name_key']]]}))
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        def inspect(*args):
            output = subprocess.check_output([str(executable), *args], cwd=self.root, env=self.env, text=True, timeout=120)
            return [json.loads(line) for line in output.splitlines()]
        bodies = inspect('--dependencies', 'dependencies.json', '-', 'bodies')
        hidden_body = next(row for row in bodies if row.get('name') == hidden['name_key'] and row['value'] is not None)
        self.assertIn(secret['name_key'], hidden_body['value'])
        names = inspect('--dependencies', 'dependencies.json', '-', 'names')
        self.assertEqual({r['name'] for r in bodies if 'name' in r}, {r['name'] for r in names if 'name' in r})
        identities = inspect('--statement-identities', 'dependencies.json', 'identity.json')
        self.assertTrue(identities)
        self.assertIn(hidden['statement_id'],
            {materials.declaration_statement_id(module['source_path'], hidden['kind'], hidden['name_key'], r['statement_material'])
             for r in identities if r['part'] == 'private'})


def stage_compiler(output):
    """Build the declared compiler target once; Lake owns its staged materials."""
    registration = json.loads((ROOT / 'tools/tests/StrataLint.Lean.Tests/Fixtures/native-compiler.json').read_text())
    if set(registration) != {'package_directory', 'target'}:
        raise ValueError('invalid native compiler fixture registration')

    class CompilerFixture(NativeTestSupport, unittest.TestCase):
        pass

    fixture = CompilerFixture()
    fixture.setUpClass()
    try:
        fixture.setUp()
        fixture.compiler_seed = None
        fixture.compiler_distribution_seed = None
        mappings = fixture.root / 'compiler-outputs.jsonl'
        checks = []
        # Keep compiler-origin construction as its own bounded phase.  The
        # Lake command still consumes the freshly built producer below, but a
        # busy host cannot make the origin build and native package build share
        # one 120-second guard.
        started = time.monotonic()
        prepared = fixture.guarded_command([
            sys.executable, str(fixture.root / 'tools/lean-inspector/compiler/build.py'), 'ensure'],
            cwd=fixture.root, env=fixture.env, text=True, capture_output=True, timeout=120)
        checks.append(dict(command=['compiler-origin', 'ensure'], exit=prepared.returncode,
            seconds=round(time.monotonic() - started, 3),
            built=sum('Built ' in line for line in (prepared.stdout + prepared.stderr).splitlines())))
        if prepared.returncode != 0:
            raise AssertionError(prepared.stdout + prepared.stderr)
        for args in [('-d', registration['package_directory'], 'build',
                      '-o', str(mappings), registration['target']),
                     ('cache', 'stage', str(mappings), str(output))]:
            started = time.monotonic()
            result = fixture.run_lake(*args)
            checks.append(dict(command=list(args), exit=result.returncode,
                seconds=round(time.monotonic() - started, 3),
                built=sum('Built ' in line for line in (result.stdout + result.stderr).splitlines())))
        # Access permissions apply to the directory produced by Lake stage;
        # they do not select or discover build inputs or reusable materials.
        for path in output.iterdir():
            path.chmod(path.stat().st_mode & ~0o222)
        started = time.monotonic()
        staged = fixture.guarded_command([
            sys.executable, str(fixture.root / 'tools/lean-inspector/compiler/build.py'),
            'stage', str(output)], cwd=fixture.root, env=fixture.env,
            text=True, capture_output=True, timeout=120)
        checks.append(dict(command=['compiler-origin', 'stage'], exit=staged.returncode,
            seconds=round(time.monotonic() - started, 3),
            built=sum('Built ' in line for line in (staged.stdout + staged.stderr).splitlines())))
        if staged.returncode != 0:
            raise AssertionError(staged.stdout + staged.stderr)
        fixture.record_result('compiler-stage', dict(checks=checks))
    finally:
        if not fixture.doCleanups():
            raise RuntimeError('native compiler stage fixture cleanup failed')



class GuardedCommandTests(unittest.TestCase):
    """Lifecycle tests need no Lean build, network, or host timing verdict."""
    def setUp(self):
        class Fixture(NativeTestSupport, unittest.TestCase):
            pass
        self.fixture = Fixture()
        self.fixture.temporary = tempfile.TemporaryDirectory(prefix='inspector-lifecycle.')
        self.fixture.root = Path(self.fixture.temporary.name)
        self.fixture.env = dict(os.environ)
        self.addCleanup(self.fixture.cleanup_fixture)

    def test_command_preserves_output_and_nonzero_exit(self):
        for status in [0, 7]:
            with self.subTest(status=status):
                result = self.fixture.guarded_command([sys.executable, '-c',
                    f'import sys; print("out"); print("err", file=sys.stderr); sys.exit({status})'])
                self.assertEqual((result.returncode, result.stdout, result.stderr), (status, 'out\n', 'err\n'))

    def test_native_compiler_images_keep_private_loader_paths(self):
        if sys.platform != 'darwin':
            return
        from compiler import build as compiler
        from concurrent.futures import ThreadPoolExecutor
        base = Path(subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT,
            text=True).strip()).resolve().parents[1]
        source = self.fixture.root / 'source'
        images = ['bin/llvm-ar', 'lib/libLLVM.dylib']
        for name in images:
            path = source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(base / name, path)
        expected = {name: publication.digest(source / name) for name in images}
        def invoke(index):
            stage = self.fixture.root / str(index)
            try:
                for name in images:
                    compiler.copy_material(source / name, stage / name)
                    self.assertFalse(os.path.samefile(source / name, stage / name))
                    self.assertEqual(publication.digest(stage / name), expected[name])
                result = subprocess.run([str(stage / 'bin/llvm-ar'), '--version'],
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stderr)
            finally:
                shutil.rmtree(stage)
        with ThreadPoolExecutor(max_workers=4) as workers:
            list(workers.map(invoke, range(16)))

    def test_scope_cleanup_failure_prevents_success_receipt(self):
        # Run the real CLI lifecycle in another process. Substitute only the
        # expensive Lean workload; doCleanups retains unittest's error capture.
        probe = '''import json, shutil, subprocess, sys
from pathlib import Path
import compiler_origin_scope as scope
root, fail = Path(sys.argv[1]), sys.argv[2] == 'failure'
root.mkdir()
(root / 'lake-manifest.json').write_text('{"packages": []}')
sources = root / 'sources'
sources.mkdir()
(sources / 'Input.lean').write_text('theorem input : True := True.intro\\n')
rows = [dict(module='Input', source_path='Input.lean', source_sha256='fixture', declarations=[])]
class Fixture(scope.ScopeFixture):
    @classmethod
    def setUpClass(cls): pass
    def setUp(self):
        self.root = root / 'fixture'
        self.root.mkdir()
        self.addCleanup(shutil.rmtree, self.root)
        if fail:
            def ordinary_failure(): raise RuntimeError('injected ordinary cleanup failure')
            self.addCleanup(ordinary_failure)
        self.lake, self.env = 'fixture-lake', {}
        self.write('lean-report-inputs.json', '{"report_modules": {}, "dependency_sources": {}}')
    def ensure(self): pass
    def guarded_command(self, argv, **kwargs):
        if '--output' in argv:
            Path(argv[argv.index('--output') + 1]).write_text(json.dumps(dict(modules=rows)))
            Path(argv[argv.index('--material-spool') + 1]).mkdir()
        return subprocess.CompletedProcess(argv, 0, '', '')
    def publish(self):
        for suffix in scope.publication.SUFFIXES:
            scope.publication.member(self.root / 'public.json', suffix).write_text('fixture')
    def report(self): return rows, b'', b''
    def origins(self): return {'Input': {'compiler_input_sha256': 'fixture'}}
scope.ROOT, scope.ScopeFixture = root, Fixture
scope.materials.compact = lambda source, spool, dest, policy: shutil.copyfile(source, dest)
output = root / 'output'
output.mkdir()
(output / 'result.json').write_text('{"exit": 0, "stale": true}')
sys.argv = ['compiler_origin_scope.py', '--sources', str(sources), '--output', str(output)]
scope.main()
'''
        for mode in ['success', 'failure']:
            with self.subTest(mode=mode):
                root = self.fixture.root / mode
                result = self.fixture.guarded_command([sys.executable, '-B', '-c', probe, str(root), mode],
                    cwd=HERE / 'tests')
                receipt = root / 'output/result.json'
                self.assertFalse((root / 'fixture').exists())
                if mode == 'success':
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(json.loads(receipt.read_text())['exit'], 0)
                    self.assertNotIn('stale', json.loads(receipt.read_text()))
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn('compiler origin scope fixture cleanup failed', result.stderr)
                    self.assertFalse(receipt.exists())
                    self.assertFalse(receipt.with_suffix('.json.tmp').exists())

    def test_timeout_joins_writers_across_groups_before_removal(self):
        self.check_timeout_joins_writers('command')

    def test_publication_timeout_joins_descendants(self):
        self.check_timeout_joins_writers('publish')

    def test_verification_timeout_joins_descendants(self):
        self.check_timeout_joins_writers('verify')

    def check_timeout_joins_writers(self, phase):
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
        if phase == 'publish':
            self.fixture.write('tools/lean-inspector/native.py', parent.replace('sys.argv[1]', 'sys.argv[2]'))
        elif phase == 'verify':
            self.fixture.write('tools/lean-inspector/native.py', 'pass\n')
            self.fixture.write('parent.py', parent)
            self.fixture.write('tools/scripts/report/lean-report-input.sh',
                'exec ' + ' '.join(shlex.quote(p) for p in
                    [sys.executable, str(root / 'parent.py'), str(root)]) + '\n')
        with patch.object(self.fixture, 'command_clock', side_effect=deadline_after_ready), \
                patch.object(publication, 'validate_bundle'), patch.object(publication, 'coordinates'):
            with self.assertRaises(subprocess.TimeoutExpired) as expired:
                if phase == 'command':
                    self.fixture.guarded_command([sys.executable, '-c', parent, str(root)])
                else:
                    self.fixture.publish()
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


if __name__ == '__main__':
    stage_compiler(Path(sys.argv[1]).resolve())
