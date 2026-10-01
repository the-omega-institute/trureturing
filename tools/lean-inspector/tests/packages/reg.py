"""Real Lake package ownership, relocation and entrypoint admission controls."""
import json
import shutil

from test_native_support import publication


class NativeRegSupport:
    def reg_package(self):
        # Shared setup already supplies the admitted root/Reg dependency graph;
        # these cases additionally select registration sources for reporting.
        # Supply tiny sources for both libraries in the real copied package
        # configuration, including its required default test target.
        self.write('tools/lean-inspector/LeanInformationAuditRegTests/Required.lean',
                   'def requiredCheck : Bool := true\n')
        self.write('tools/lean-inspector/LeanInformationAuditRegAnalysis/Explicit.lean',
                   'def explicitAnalysis : Bool := true\n')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_modules']['include'].append(dict(pattern='Reg/**/*.lean', optional=True))
        policy['dependency_sources']['include'].append(
            dict(pattern='tools/lean-inspector-interface/**/*.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))

    def make_lean(self, *targets, success=True):
        result = self.guarded_command(['make', 'lean', 'LEAN_TARGETS=' + ' '.join(targets)],
                                     cwd=self.root, env=self.env, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def build_reg_report(self, success=True):
        return self.run_lake('-d', str(self.root / 'Reg'), 'build', ':report',
                             'trureturing/Audit', 'leanInspector/reportInspector',
                             'reg/LeanInformationAuditRegTests', success=success)


class NativeRegTests(NativeRegSupport):
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


class NativeRegConsumerTests(NativeRegSupport):
    def test_reg_empty_and_nonempty_build_routing(self):
        # Keep the dependency pin stable across the root-only and Reg cases.
        # A pin transition would discard the private compiler artifacts even
        # though this test changes package routing, not dependency versions.
        self.run_lake('build', 'Fixture')
        self.write('Reg/Unselected.lean', 'this must fail\n')
        self.make_lean('Fixture', 'Audit')  # Root-only selection with valid mandatory Reg metadata.
        self.assertFalse((self.root / '.lake/build/reg').exists())
        (self.root / 'Reg/Unselected.lean').unlink()
        self.reg_package()
        self.run_lake('build', 'Fixture')
        self.make_lean()
        self.assertFalse((self.root / '.lake/build/reg/lib/lean/Reg').exists())
        self.assertTrue((self.root / '.lake/build/reg/lib/lean/LeanInformationAuditRegTests/Required.olean').is_file())
        self.assertFalse((self.root / '.lake/build/reg/lib/lean/LeanInformationAuditRegAnalysis').exists())
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
        self.write(downstream, 'def requiredCheck : Bool := missingRequiredCheck\n')
        self.make_lean('Reg.Support.Entry')
        failed = self.make_lean(success=False)
        self.assertIn('missingRequiredCheck', failed.stdout + failed.stderr)
        self.write(downstream, 'def requiredCheck : Bool := true\n')
        self.make_lean()
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
            self.write('Audit.lean', 'def audit : Nat := 1\n')
            self.write('tools/lean-inspector/LeanInformationAuditRegTests/Required.lean',
                       'def requiredCheck : Bool := missingRequiredCheck\n')
            failed = self.build_reg_report(success=False)
            self.assertIn('missingRequiredCheck', failed.stdout + failed.stderr)
        finally:
            self.root, self.env = donor, original_env
