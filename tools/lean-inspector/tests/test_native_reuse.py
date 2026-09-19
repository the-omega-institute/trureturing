"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION
import copy
import platform
import shlex


class NativeReuseTests:
    def inspect(self, *, success=True):
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env)
        if success:
            self.assertEqual(result.returncode, 0, '[FAIL] report_entry_success\n' + result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, '[FAIL] default_failure_blocks_reuse\n' + result.stdout + result.stderr)
        return result

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = copy.deepcopy(EXECUTION)
        policy['report_execution']['toolchain'] = dict(
            pin=(self.root / 'lean-toolchain').read_text().strip(), identities=[dict(
                platform={name: getattr(platform, name)() for name in EXECUTION['platform']},
                tools={name: subprocess.check_output([str(Path(self.lake).with_name(name)), '--version'],
                    text=True).strip() for name in EXECUTION['tools']})])
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh',
                     'tools/scripts/workflow/install-lean-toolchain.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        friend = 'tools/StrataLint.Lean/Properties/AssemblyInfo.cs'
        policy['producer_scopes']['lean-report']['include'].append(
            dict(pattern='tools/StrataLint.Lean/**/*.cs', optional=False))
        policy['producer_scopes']['lean-report']['exclude'] = json.loads(
            (ROOT / 'lean-report-inputs.json').read_text())['producer_scopes']['lean-report']['exclude']
        self.write(friend, '[assembly: InternalsVisibleTo("Existing.Tests")]\n')
        # Simulate activating the installed pinned toolchain only after a miss;
        # ensuing report/default work still runs the real compiler and Lake.
        self.write('tools/scripts/workflow/install-lean-toolchain.sh',
            '#!/bin/bash\nset -euo pipefail\n[[ "$2" == --github-path ]]\n'
            'printf "%s\\n" installed >> ' + shlex.quote(str(self.root / 'tool-installs')) + '\n'
            'printf "%s\\n" ' + shlex.quote(str(Path(self.lake).parent)) + ' > "$3"\n')
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()  # installs the collection's private compiler stage
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        first = self.inspect()
        self.assertIn('phase=report status=completed', first.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file(), '[FAIL] defaults_report_success_sealed')
        expected = output.read_bytes()
        seed = self.root / 'lightweight-seed' / output.name
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix), publication.member(seed, suffix))
        sealed = {suffix: publication.member(seed, suffix).read_bytes()
                  for suffix in (*publication.SUFFIXES, '.reuse.json')}
        def probe():
            result = self.guarded_command([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
                'probe', '--repository', str(self.root), '--report', str(seed), '--lake', self.lake], env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)['needs_lake'], '[FAIL] probe_only_selects_resources')
        probe()
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        (self.root / 'bin/python3').symlink_to(sys.executable)
        self.env['PATH'] = str(self.root / 'bin') + ':/usr/bin:/bin:/usr/sbin:/sbin'
        self.env['LAKE_BIN'] = ''
        self.write(friend, '[assembly: InternalsVisibleTo("Repository.Tests")]\n')
        reused = self.inspect()
        self.assertFalse((self.root / 'tool-installs').exists(), '[FAIL] reuse_must_not_activate_toolchain')
        self.assertNotIn('phase=ensure status=started', reused.stderr, '[FAIL] heavy_cache_not_required')
        self.assertNotIn('phase=report status=started', reused.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', reused.stdout)
        self.assertEqual(expected, output.read_bytes())
        self.assertFalse((self.root / '.lake/packages').exists())
        # Resource planning neither parses material semantics nor vouches for
        # bytes that may change before the normal entry consumes its seed.
        for damage in ('sealed-invalid-material', 'changed-after-probe'):
            with self.subTest(damage=damage):
                for suffix, data in sealed.items():
                    publication.member(seed, suffix).write_bytes(data)
                if damage == 'changed-after-probe':
                    probe()
                archive = publication.member(seed, '.materials.zip')
                with zipfile.ZipFile(archive, 'a') as target:
                    target.writestr('unreferenced', b'not an admitted report material')
                if damage == 'sealed-invalid-material':
                    receipt = json.loads(sealed['.reuse.json'])
                    receipt['bundle']['.materials.zip'] = publication.digest(archive)
                    publication.member(seed, '.reuse.json').write_text(json.dumps(receipt))
                    probe()
                shutil.rmtree(self.root / '.lake')
                recovered = self.inspect()
                self.assertTrue((self.root / 'tool-installs').exists(), '[FAIL] miss_activates_toolchain')
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr,
                              '[FAIL] invalid_seed_must_reenter_native_producer')
                self.assertEqual(expected, output.read_bytes())
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        for suffix, data in sealed.items():
            publication.member(seed, suffix).write_bytes(data)
        probe()
        # A successful planning probe never exempts the normal entry from the
        # default-only input obligation. A changed audit must reach Lake/fail.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        failed = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        publication.member(seed, '.reuse.json').unlink()
        recovered = self.inspect()
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write('lean-report-inputs.json', json.dumps(policy))
        invalid = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', invalid.stderr)
        self.assertNotIn('phase=report status=started', invalid.stderr)
