"""Real Lake package ownership, relocation and entrypoint admission controls."""
import json
import shutil
import subprocess

from test_native_support import ROOT, publication


class NativeRegTests:
    def reg_package(self):
        # A tiny local Git dependency exercises the same shared-manifest gate as
        # production, without downloading a second Mathlib or weakening admission.
        mathlib = self.root / 'fixture-mathlib'
        subprocess.run(['git', 'init', '--quiet', str(mathlib)], check=True)
        subprocess.run(['git', '-C', str(mathlib), 'add', 'lakefile.toml', 'lake-manifest.json'], check=True)
        subprocess.run(['git', '-C', str(mathlib), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'fixture'], check=True)
        rev = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
        config = self.root / 'lakefile.toml'
        config.write_text(config.read_text().replace('name = "fixture"', 'name = "trureturing"')
            .replace('path = "fixture-mathlib"', f'git = "{mathlib}"\nrev = "{rev}"'))
        manifest = json.loads((self.root / 'lake-manifest.json').read_text())
        manifest['name'] = 'trureturing'
        git = dict(type='git', name='mathlib', url=str(mathlib), rev=rev, inputRev=rev,
                   subDir=None, configFile='lakefile.toml', manifestFile='lake-manifest.json',
                   scope='', inherited=False)
        manifest['packages'][1] = git
        self.write('lake-manifest.json', json.dumps(manifest))
        self.copy('Reg/lakefile.toml')
        # Empty downstream libraries still have their declared source roots.
        # Lake's submodule glob requires directories, not dummy Lean modules.
        for library in ('LeanInformationAuditRegTests', 'LeanInformationAuditRegAnalysis'):
            (self.root / 'tools/lean-inspector' / library).mkdir()
        reg = json.loads((ROOT / 'Reg/lake-manifest.json').read_text())
        reg['packages'] = [p for p in reg['packages'] if p['type'] == 'path'] + [dict(git, inherited=True)]
        self.write('Reg/lake-manifest.json', json.dumps(reg))
        shutil.copytree(ROOT / 'tools/lean-inspector-interface',
                        self.root / 'tools/lean-inspector-interface', ignore=shutil.ignore_patterns('.lake'))
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_modules']['include'].append(dict(pattern='Reg/**/*.lean', optional=True))
        policy['dependency_sources']['include'].append(
            dict(pattern='tools/lean-inspector-interface/**/*.lean', optional=False))
        policy['config_inputs']['include'] += [dict(pattern=p, optional=False) for p in
            ('Reg/lakefile.toml', 'Reg/lake-manifest.json')]
        self.write('lean-report-inputs.json', json.dumps(policy))

    def make_lean(self, *targets, success=True):
        result = self.guarded_command(['make', 'lean', 'LEAN_TARGETS=' + ' '.join(targets)],
                                     cwd=self.root, env=self.env, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def test_reg_empty_and_nonempty_build_routing(self):
        self.run_lake('build', 'Fixture')
        self.make_lean()  # Ordinary root-only workspaces remain supported.
        self.reg_package()
        self.run_lake('build', 'Fixture')  # The new Git pin needs its own warm compiler baseline.
        self.make_lean()
        self.assertFalse((self.root / '.lake/build/reg/lib/lean/Reg').exists())
        self.write('Reg/Support/Entry.lean', 'import D5.A\nimport LeanInformationAuditInterface.Records\n'
                   'def registrationValue := value\n')
        self.make_lean('Reg.Support.Entry', 'D5.Alone')
        self.assertTrue((self.root / '.lake/build/reg/lib/lean/Reg/Support/Entry.olean').is_file())
        self.assertFalse((self.root / '.lake/build/lib/lean/Reg/Support/Entry.olean').exists())
        self.write('Audit.lean', 'this must fail\n')
        self.make_lean('Reg.Support.Entry')  # Selected targets remain selected.
        self.make_lean(success=False)  # The default root audit remains required.
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        downstream = 'tools/lean-inspector/LeanInformationAuditRegTests/Required.lean'
        self.write(downstream, 'invalid downstream default\n')
        self.make_lean('Reg.Support.Entry')
        self.make_lean(success=False)
        self.write(downstream, 'def requiredCheck : Bool := true\n')
        self.write('Reg/Support/Entry.lean', 'this must fail\n')
        self.make_lean(success=False)

    def test_reg_report_rows_relocation_and_defaults(self):
        self.reg_package()
        self.build_reg_report()
        self.assertFalse(any(r['module'].startswith('Reg.') for r in self.report()[0]))
        self.write('Reg/Support/Entry.lean', 'import D5.A\nimport LeanInformationAuditInterface.Records\n'
                   'def registrationValue := value\n')
        result = self.guarded_command(['make', 'lean-report'], cwd=self.root, env=self.env, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        published = json.loads((self.root / '.lake/build/stratalint/raw-lean-report.json').read_text())
        self.assertIn('Reg.Support.Entry', [r['module'] for r in published['modules']])
        rows = self.report()[0]
        row = next(r for r in rows if r['module'] == 'Reg.Support.Entry')
        self.assertEqual(row['source_path'], 'Reg/Support/Entry.lean')
        sources = json.loads((self.root / '.lake/build/lean-inspector/inputs/Reg.Support.Entry.json.sources.json').read_text())
        self.assertIn('tools/lean-inspector-interface/LeanInformationAuditInterface/Records.lean', sources)
        self.assertTrue(all(not p.startswith(('../', '/')) for p in sources))
        # Preserve the donor while using its copied config and module oleans in a
        # different root containing spaces. No absolute path is a source identity.
        donor = self.root
        destination = donor / 'relocated space'
        destination.mkdir()
        for child in list(donor.iterdir()):
            if child == destination:
                continue
            if child.is_dir():
                shutil.copytree(child, destination / child.name)
            else:
                shutil.copy2(child, destination / child.name)
        original_env = self.env
        self.root = destination
        self.env = {k: v.replace(str(donor), str(destination)) for k, v in original_env.items()}
        try:
            self.build_reg_report()
            moved = next(r for r in self.report()[0] if r['module'] == 'Reg.Support.Entry')
            self.assertEqual(moved, row)
            leaf = 'Reg/Support/Entry.lean'
            original = (donor / leaf).read_text()
            self.write(leaf, original + 'def relocatedOnly : Nat := 73\n')
            self.build_reg_report()
            changed = next(r for r in self.report()[0] if r['module'] == 'Reg.Support.Entry')
            self.assertEqual(changed['source_sha256'], 'sha256:' + publication.digest(self.root / leaf))
            self.assertNotEqual(changed['source_sha256'], row['source_sha256'])
            self.assertEqual((donor / leaf).read_text(), original)
            self.write('Audit.lean', 'invalid root audit\n')
            self.build_reg_report(success=False)
        finally:
            self.root, self.env = donor, original_env

    def build_reg_report(self, success=True):
        return self.run_lake('-d', str(self.root / 'Reg'), 'build', ':report', success=success)

    def test_reg_manifest_rejected_before_materialization(self):
        self.reg_package()
        reg = json.loads((self.root / 'Reg/lake-manifest.json').read_text())
        reg['packages'][-1]['rev'] = 'a' * 40
        self.write('Reg/lake-manifest.json', json.dumps(reg))
        result = self.make_lean('Reg', success=False)
        self.assertIn('REG-MANIFEST-GIT-AGREEMENT', result.stdout + result.stderr)
        self.assertFalse((self.root / 'Reg/.lake').exists())
        self.assertFalse((self.root / '.lake/packages/mathlib').exists())
        result = self.guarded_command(['make', 'lean-report'], cwd=self.root, env=self.env, timeout=120)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('REG-MANIFEST-GIT-AGREEMENT', result.stdout + result.stderr)
        self.assertFalse((self.root / 'Reg/.lake').exists())
