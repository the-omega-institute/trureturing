"""Check warm publication, readonly restores and incremental misses through Make and Lake."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]


class SharedArtifactCacheTests(unittest.TestCase):
    def test_warm_and_scoped_readers(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            main, reader, cache = (base / name for name in ('main', 'reader', 'cache'))
            compile_log = base / 'compiles'
            env = dict(os.environ, LAKE_CACHE_DIR=str(cache), LAKE_ARTIFACT_CACHE='true',
                       STRATALINT_LEAN_PRODUCER_DLL=str(ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'),
                       COMPILE_LOG=str(compile_log), MATHLIB_NO_CACHE_ON_UPDATE='1', GIT_ALLOW_PROTOCOL='file')
            for var in ('MAKEFLAGS', 'MAKELEVEL', 'STRATALINT_WARM_DONOR', 'FULL_BUILD',
                        'STRATALINT_ACCEPT_COLD_BUILD', 'STRATALINT_LEAN_CACHE_DONOR_REPOSITORY'):
                env.pop(var, None)

            def call(directory, *args):
                proc = subprocess.run(args, cwd=directory, env=env, text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                self.assertEqual(0, proc.returncode, proc.stdout)
                return proc.stdout.strip()

            def write(directory, name, text):
                path = directory / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)

            def commit(directory):
                call(directory, 'git', 'add', '.')
                call(directory, 'git', '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                     'commit', '--no-gpg-sign', '-qm', 'fixture')

            def module(name, imports='', value=0):
                return (imports + '\nimport Lean\nrun_cmd do\n'
                        f'  IO.FS.withFile (← IO.getEnv "COMPILE_LOG").get! .append fun h => h.putStrLn "{name}"\n'
                        f'def {name.lower()} : Nat := {value}\n')

            mathlib = base / 'mathlib'
            write(mathlib, 'lakefile.toml', 'name = "mathlib"\n[[lean_exe]]\nname = "cache"\nroot = "Cache"\n')
            write(mathlib, 'Cache.lean', 'def main : IO Unit := pure ()\n')
            call(mathlib, 'git', 'init', '-q')
            commit(mathlib)
            rev = call(mathlib, 'git', 'rev-parse', 'HEAD')
            write(main, '.gitignore', '.lake/\n')
            for name in ('lean-toolchain', 'Makefile', 'tools/scripts/worktree/lean-cache-run.sh',
                         'tools/scripts/worktree/warm-donor.sh', 'tools/scripts/worktree/lean-git/git'):
                (main / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / name, main / name)
            write(main, 'lakefile.toml', f'name = "trureturing"\ndefaultTargets = ["Fixture"]\n'
                  f'[[require]]\nname = "mathlib"\ngit = "{mathlib}"\nrev = "{rev}"\n'
                  '[[lean_lib]]\nname = "Fixture"\n[[lean_lib]]\nname = "Support"\n')
            write(main, 'Support.lean', module('Support'))
            write(main, 'Fixture.lean', module('Fixture', 'import Support'))
            write(main, 'tools/lean-inspector-interface/lakefile.toml', 'name = "leanInspectorInterface"\n')
            write(main, 'tools/lean-inspector/lakefile.lean',
                  'import Lake\nopen Lake DSL\npackage leanInspector where\n'
                  '  packagesDir := "../../.lake/packages"\nrequire trureturing from "../.."\n'
                  'require leanInspectorInterface from "../lean-inspector-interface"\n@[default_target] lean_lib Impl\n')
            write(main, 'tools/lean-inspector/Impl.lean', module('Impl'))
            package_config = {'Reg': ('Reg', 'reg', '../.lake/packages', [
                ('trureturing', '..'), ('leanInspectorInterface', '../tools/lean-inspector-interface')]),
                'tools/lean-inspector-reg': ('Host', 'regInspector', '../../.lake/packages', [
                    ('reg', '../../Reg'), ('leanInspector', '../lean-inspector')])}
            for directory, (lib, name, packages_dir, deps) in package_config.items():
                requires = ''.join(f'[[require]]\nname = "{dep}"\npath = "{path}"\n' for dep, path in deps)
                write(main / directory, 'lakefile.toml', f'name = "{name}"\npackagesDir = "{packages_dir}"\n'
                      f'defaultTargets = ["{lib}"]\n{requires}[[lean_lib]]\nname = "{lib}"\n')
                write(main / directory, f'{lib}.lean', module(lib))
            for directory in (main, main / 'tools/lean-inspector-interface', main / 'tools/lean-inspector',
                              main / 'Reg', main / 'tools/lean-inspector-reg'):
                call(directory, 'lake', 'update')
            # Keep the repository's canonical relative paths for inherited packages.
            for package in ('Reg', 'tools/lean-inspector-reg'):
                path = Path(package) / 'lake-manifest.json'
                actual = json.loads((main / path).read_text())
                expected = json.loads((ROOT / path).read_text())
                actual['packages'] = ([p for p in expected['packages'] if p['type'] == 'path'] +
                                      [p for p in actual['packages'] if p['type'] == 'git'])
                (main / path).write_text(json.dumps(actual))
            call(main, 'git', 'init', '-qb', 'dev')
            commit(main)
            call(main, 'git', 'remote', 'add', 'origin', str(main))
            call(main, 'git', 'worktree', 'add', '--detach', str(reader), 'HEAD')

            def snapshot():
                return {file.relative_to(cache): (file.stat().st_mtime_ns, hashlib.sha256(file.read_bytes()).digest())
                        for file in cache.rglob('*') if file.is_file()}

            call(main, 'make', 'lean', 'LEAN_TARGETS=Fixture')
            self.assertEqual(['Support', 'Fixture'], compile_log.read_text().splitlines())
            self.assertFalse(snapshot())
            compile_log.write_text('')
            result = call(main, 'make', 'warm-donor', 'FULL_BUILD=1', 'LEAN_TARGETS=Fixture')
            self.assertIn('"status":"warmed"', result)
            self.assertEqual({'Impl', 'Reg', 'Host'}, set(compile_log.read_text().splitlines()))
            published = snapshot()
            scopes = {p.parts[1] for p in published if p.parts[0] == 'outputs'}
            self.assertTrue({'trureturing', 'leanInspector', 'reg', 'regInspector'} <= scopes, scopes)
            compile_log.write_text('')
            result = call(reader, 'make', 'lean', 'LEAN_TARGETS=Fixture', 'FULL_BUILD=1')
            receipts = [json.loads(line.removeprefix('LEAN_CACHE ')) for line in result.splitlines()
                        if line.startswith('LEAN_CACHE ')]
            self.assertTrue(receipts)
            self.assertTrue(all(row['clonefile_attempts'] == 0 for row in receipts), receipts)
            self.assertEqual('', compile_log.read_text())
            private_output = Path('.lake/build/lib/lean/Fixture.olean')
            self.assertEqual((main / private_output).read_bytes(), (reader / private_output).read_bytes())
            write(reader, 'Fixture.lean', module('Fixture', 'import Support', 2))
            call(reader, 'make', 'lean', 'LEAN_TARGETS=Fixture')
            self.assertEqual(['Fixture'], compile_log.read_text().splitlines())
            self.assertNotEqual((main / private_output).read_bytes(), (reader / private_output).read_bytes())
            self.assertEqual(published, snapshot())

            call(main, 'git', 'switch', '--detach')
            call(reader, 'git', 'restore', 'Fixture.lean')
            call(reader, 'git', 'switch', 'dev')
            skipped = call(reader, 'make', 'warm-donor', 'FULL_BUILD=1')
            self.assertIn('"reason":"worktree is not the main checkout"', skipped)
            self.assertEqual(published, snapshot())


if __name__ == '__main__':
    unittest.main()
