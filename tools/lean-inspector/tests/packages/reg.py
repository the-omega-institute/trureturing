"""Real Lake package ownership, relocation and entrypoint admission controls."""
import json
import shutil
import time

from test_native_support import publication


class NativeRegTests:
    def reg_package(self):
        # Shared setup already supplies the admitted root/Reg dependency graph;
        # these cases additionally select registration sources for reporting.
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

    def test_reg_empty_and_nonempty_build_routing(self):
        self.run_lake('build', 'Fixture')
        self.write('Reg/Unselected.lean', 'this must fail\n')
        self.make_lean('Fixture', 'Audit')  # Root-only selection with valid mandatory Reg metadata.
        self.assertFalse((self.root / '.lake/build/reg').exists())
        (self.root / 'Reg/Unselected.lean').unlink()
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
        return self.run_lake('-d', str(self.root / 'Reg'), 'build', ':report',
                             'trureturing/Audit', 'leanInspector/reportInspector', success=success)

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

    @staticmethod
    def sidecar_source_paths():
        import subprocess
        from test_native_support import ROOT
        paths = subprocess.check_output(['git', 'ls-files', '-z', '.gitignore', 'D5',
            'tools', 'Reg/lakefile.toml', 'Reg/lake-manifest.json', 'Trureturing.lean',
            'lakefile.toml', 'lake-manifest.json', 'lean-report-inputs.json',
            'Directory.*', 'global.json', '.editorconfig', 'Meta/engineering-projects.json', 'Meta/FILEMAP.toml', 'Meta/FILEMAP' ], cwd=ROOT).decode().split('\0')
        return paths

    def prepare_sidecar_enrollment(self, output):
        started = time.monotonic()
        paths = self.sidecar_source_paths()
        for name in filter(None, paths):
            self.copy(name)
        # The warm pinned provider supplies checkouts and the real cache
        # executable and resolves its source environment. Native cache-get
        # restores the complete upstream closure without configuring this cold
        # authored project first; all authored outputs still build privately.
        from test_native_support import ROOT
        command_started = time.monotonic()
        argv = ['python3', '-B', str(ROOT / 'tools/scripts/worktree/lean_actions.py'),
                'stage-dependency', '--repository', str(ROOT), '--destination', str(self.root)]
        staged = self.guarded_command(argv, cwd=self.root, env=self.env, timeout=120)
        (output / 'prerequisite-source-commands.json').write_text(json.dumps([dict(
            argv=argv, exit=staged.returncode, elapsed_seconds=time.monotonic() - command_started,
            stdout=staged.stdout, stderr=staged.stderr)], indent=2))
        self.assertEqual(staged.returncode, 0, staged.stdout + staged.stderr)
        self.assertFalse((self.root / '.lake/build').exists())
        self.assertEqual((self.root / '.lake/.stratalint-lean-cache-stamp.json').read_bytes(),
                         (ROOT / '.lake/.stratalint-lean-cache-stamp.json').read_bytes())
        # The private project owns this empty build root. Canonical ensure
        # preserves an owned root, so an optional Release archive cannot turn
        # the subsequent project compilation into reuse of authored outputs.
        (self.root / '.lake/build').mkdir()
        command_started = time.monotonic()
        prepared = self.ensure()
        (output / 'prerequisite.json').write_text(json.dumps(prepared, indent=2))
        self.assertEqual(prepared['method'], 'none')
        self.assertEqual(prepared['status'], 'present')
        self.assertIsNone(prepared['donor'])
        self.assertEqual(prepared['mathlib_missing_olean_files'], 0)
        self.assertEqual(prepared['project_olean_state'], 'cold')
        preparation = dict(source_seconds=command_started - started,
            ensure_seconds=time.monotonic() - command_started, builds=[])
        # D5 owns the mathematical prerequisites; Syntax owns enrollment and
        # assessment, and leanInspector owns the report executable. Building
        # these together charged the cold D5 closure to the compiler's 120s
        # command guard. Keep the same selected targets and private Lake
        # outputs, with both phases inside the class fixture's 300s supervisor.
        for phase, targets in [
                ('content', ['D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates']),
                ('compiler', ['LeanInformationAudit.Syntax', 'leanInspector/reportInspector'])]:
            command_started = time.monotonic()
            built = self.make_lean(*targets)
            cache = json.loads(next(line.removeprefix('LEAN_CACHE ')
                for line in built.stdout.splitlines() if line.startswith('LEAN_CACHE ')))
            self.assertEqual(cache['archive_status'], 'not_attempted')
            self.assertIsNone(cache['donor'])
            if phase == 'content':
                self.assertEqual(cache['project_olean_state'], 'cold')
            preparation['builds'].append(dict(phase=phase, argv=built.args, exit=built.returncode,
                elapsed_seconds=time.monotonic() - command_started,
                stdout=built.stdout, stderr=built.stderr))
            preparation['elapsed_seconds'] = time.monotonic() - started
            (output / 'prerequisite-build.json').write_text(json.dumps(preparation, indent=2))

    def test_reg_sidecar_publication(self):
        """Real enrollment, certificates and public report for the delta consumer."""
        import os
        import subprocess
        from pathlib import Path
        from test_native_support import ROOT

        output = Path(os.environ['REG_SIDECAR_NATIVE_OUT'])
        output.mkdir(parents=True, exist_ok=True)
        previous = str(self.root)
        self.root = Path(os.environ['STRATALINT_NATIVE_ENROLLMENT_ROOT'])
        self.env = {key: value.replace(previous, str(self.root)) for key, value in self.env.items()}
        self.compiler_seed = None
        for name in ['prerequisite.json', 'prerequisite-source-commands.json', 'prerequisite-build.json']:
            shutil.copy2(self.root.parent / name, output / name)
        paths = self.sidecar_source_paths()
        self.write('utility.json', '[]')
        owner = 'Reg/Support/SidecarOwner.lean'
        binder = 'Reg/Support/SidecarBinding.lean'
        self.write(owner, '''import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
namespace NativeSidecar
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit
def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not
instance : DecidableEq arena.State := instDecidableEqBool
information_theorem original in arena
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm
information_theorem unrelated in arena
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm
end NativeSidecar
''')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        self.assertEqual(policy['report_cache_release_semantic_version'], 9)
        policy['report_modules'] = dict(include=[dict(pattern=p, optional=False)
            for p in [owner, binder]], exclude=[])
        policy['dependency_sources']['include'].append(dict(pattern='D5/**/*.lean', optional=True))
        self.write('lean-report-inputs.json', json.dumps(policy))
        commands = []
        for mode in ['validated', 'unresolved', 'missing_slots']:
            directory = output / mode
            directory.mkdir()
            enrollment = '' if mode == 'unresolved' else 'register_information_template cutRealization\n'
            slots = '' if mode == 'missing_slots' else '\n  escape from (Bool) escape continues (open)'
            self.write(binder, 'import Reg.Support.SidecarOwner\nnamespace NativeSidecar\n'
                'open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates\n' + enrollment +
                'declare_information_template_binding original in arena\n'
                '  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))' +
                slots + '\nend NativeSidecar\n')
            for label, argv in [('lean', ['make', 'lean', 'LEAN_TARGETS=Reg.Support.SidecarBinding']),
                                ('report', ['make', 'lean-report'])]:
                command_started = time.monotonic()
                result = self.guarded_command(argv, cwd=self.root, env=self.env, timeout=120)
                (directory / (label + '.stdout.txt')).write_text(result.stdout)
                (directory / (label + '.stderr.txt')).write_text(result.stderr)
                commands.append(dict(mode=mode, phase='consumer', argv=argv, exit=result.returncode,
                    elapsed_seconds=time.monotonic() - command_started))
                (output / 'commands.json').write_text(json.dumps(commands, indent=2))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = self.root / '.lake/build/stratalint/raw-lean-report.json'
            rows = publication.validate_bundle(report, manifest=self.root / 'lean-report-inputs.json')
            self.assertEqual(len(rows), 2)
            by_path = {row['source_path']: row for row in rows}
            originals = by_path[owner]['information_templates']
            overlays = by_path[binder]['information_templates']
            self.assertEqual(len(originals['inventory']), 2)
            self.assertEqual(len(originals['records']), 2)
            self.assertEqual(overlays['inventory'], [])
            self.assertEqual(overlays['registered'], [])
            self.assertEqual(len(overlays['records']), 1)
            overlay = overlays['records'][0]
            self.assertEqual(overlay['key']['registration_module'], 'Reg.Support.SidecarOwner')
            self.assertEqual(overlay['binding_source_path'], binder)
            self.assertEqual(overlay['state'], 'declared_unresolved' if mode == 'unresolved'
                             else 'declared_validated')
            self.assertEqual(overlay['certificate'] is None, mode == 'unresolved')
            for artifact in report.parent.glob(report.name + '*'):
                if artifact.is_file():
                    shutil.copy2(artifact, directory / artifact.name)
            source_names = [p for p in paths if p and (self.root / p).is_file()] + [owner, binder, 'lean-toolchain']
            sources = {p: (self.root / p).read_text() for p in source_names
                       if p.endswith(('.lean', '.json', '.toml', '.yaml', '.cs', '.props', '.targets', '.txt'))
                       or p in ['lean-toolchain', 'Makefile', '.editorconfig']}
            # This is the actual report-selection manifest used by make.
            sources['lean-report-inputs.json'] = (self.root / 'lean-report-inputs.json').read_text()
            (directory / 'sources.json').write_text(json.dumps(sources, ensure_ascii=False))
            (directory / 'certificate.json').write_text(json.dumps(overlay, indent=2, ensure_ascii=False))
            for relative in ['.lake/build/reg/lib/lean/Reg/Support',
                             '.lake/build/lean-inspector/inputs', '.lake/build/lean-inspector/modules']:
                source = self.root / relative
                if source.exists():
                    target = directory / 'native' / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.mkdir()
                    for artifact in source.glob('Sidecar*' if source.name == 'Support' else 'Reg.Support.Sidecar*'):
                        if artifact.is_file():
                            shutil.copy2(artifact, target / artifact.name)
            (directory / 'publication.json').write_text(json.dumps(dict(
                validated=True, modules=len(rows), semantic_version=9,
                source_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=ROOT, text=True).strip(),
                report_sha256=publication.digest(report)), indent=2))


def stage_enrollment(output):
    """Class-owned real enrollment prerequisites; no repository build donor."""
    import unittest
    from test_native_support import NativeTestSupport

    class EnrollmentFixture(NativeRegTests, NativeTestSupport, unittest.TestCase):
        pass

    fixture = EnrollmentFixture()
    fixture.setUpClass()
    try:
        fixture.setUp()
        previous = str(fixture.root)
        destination = output / 'enrollment fixture'
        shutil.move(fixture.root, destination)
        fixture.root = destination
        fixture.env = {key: value.replace(previous, str(destination)) for key, value in fixture.env.items()}
        fixture.compiler_seed = None
        fixture.prepare_sidecar_enrollment(output)
    finally:
        # The moved fixture belongs to the C# class; its TemporaryDirectory
        # removes the compiled inputs after the consumer has completed.
        fixture.doCleanups()


if __name__ == '__main__':
    import sys
    from pathlib import Path
    stage_enrollment(Path(sys.argv[1]).resolve())
