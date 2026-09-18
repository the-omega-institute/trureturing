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

    def test_fetched_default_only_failure_and_metadata_reuse(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        # Audit.lean is intentionally not manually registered: native defaults
        # must account for it and the fetched module used only by that default.
        self.build()
        self.inspect()
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        origins = self.origins()
        self.assertTrue(all(not any(item['module'] == 'Foreign.AuditOnly'
                                   for item in origin['external_inputs']) for origin in origins.values()))
        before = self.stamps()
        source = self.root / '.lake/packages/fetched/Foreign/AuditOnly.lean'
        original = source.read_bytes()
        source.write_text('def auditOnly : False := True.intro\n')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        failed = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        source.write_bytes(original)
        self.inspect()
        self.assertEqual(before, self.stamps())
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        oleans = {str(path): (path.stat().st_mtime_ns, publication.digest(path))
                  for path in (self.root / '.lake/build/lib/lean').rglob('*.olean*')}
        config = self.root / 'lakefile.toml'
        config.write_text(config.read_text() + '\n# compatible metadata\n')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        result = self.inspect()
        self.assertIn('extracted_modules=0', result.stdout)
        self.assertEqual(before, self.stamps())
        self.assertEqual(origins, self.origins())
        self.assertEqual(oleans, {str(path): (path.stat().st_mtime_ns, publication.digest(path))
                                 for path in (self.root / '.lake/build/lib/lean').rglob('*.olean*')})
        # A malformed descriptor cannot be replaced with yesterday's inputs.json.
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        descriptor.write_text('{broken')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        repaired = self.inspect()
        self.assertIn('phase=report status=completed', repaired.stderr)
        self.assertIn('extracted_modules=0', repaired.stdout)
        # A custom default is outside the native source population: execute it.
        config.write_text(config.read_text().replace('["Fixture", "Audit"]', '["Fixture", "Audit", "cache"]'))
        self.inspect()
        self.assertFalse(publication.member(output, '.reuse.json').exists())

    def test_fetched_entry_retains_preensure_root_capture(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        entry = self.root / 'tools/lean-inspector/inspect.sh'
        source = entry.read_text()
        marker = 'run_phase ensure /bin/bash'
        self.assertEqual(source.count(marker), 1)
        source = source.replace(marker,
            'printf "\\n-- changed after root capture\\n" >> "$REPOSITORY/D5/Alone.lean"\n' + marker)
        entry.write_text(source)
        result = self.inspect(success=False)
        self.assertIn('root inputs changed during report entry', result.stderr)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=capture-final', result.stderr)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertFalse(publication.member(output, '.reuse.json').exists())
