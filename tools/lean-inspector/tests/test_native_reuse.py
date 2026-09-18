"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION
import reuse


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
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
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
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        reused = self.inspect()
        self.assertNotIn('phase=ensure status=started', reused.stderr, '[FAIL] heavy_cache_not_required')
        self.assertNotIn('phase=report status=started', reused.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', reused.stdout)
        self.assertEqual(expected, output.read_bytes())
        self.assertFalse((self.root / '.lake/packages').exists())
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

    def test_fetched_package_absence_reuses_only_wholly_unmaterialized_snapshot(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        self.inspect()
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        seed = self.root / 'lightweight-seed' / 'raw-lean-report.json'
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix),
                            publication.member(seed, suffix))
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        reused = self.inspect()
        self.assertEqual(reused.returncode, 0, reused.stdout + reused.stderr)
        self.assertNotIn('phase=ensure status=started', reused.stderr)
        self.assertEqual(output.read_bytes(), seed.read_bytes())
        # A present but incomplete checkout is a miss even though the
        # producer-bound Git snapshot itself remains unchanged.
        partial = self.root / '.lake/packages/fetched/Foreign'
        partial.mkdir(parents=True)
        (partial / 'Thing.lean').write_text('def value : Nat := 9\n')
        captured = reuse.probe(self.root, seed, self.lake)
        self.assertTrue(captured['needs_lake'], captured)
