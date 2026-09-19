"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION


class NativeReuseTests:
    def inspect(self, *, success=True):
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        started = time.monotonic()
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env)
        report_started = 'phase=report status=started' in result.stderr
        build_output = Path(str(output) + '.logs/report.stdout.log')
        build_text = build_output.read_text() if report_started and build_output.is_file() else ''
        checks = getattr(self, '_entry_checks', [])
        checks.append(dict(exit=result.returncode, seconds=round(time.monotonic() - started, 3),
            built=sum('Built ' in line for line in build_text.splitlines()),
            report_started=report_started,
            work=[line for line in result.stdout.splitlines() if line.startswith('LEAN_INSPECTOR_WORK ')]))
        self._entry_checks = checks
        self.record_result('entry', dict(checks=checks))
        if success:
            self.assertEqual(result.returncode, 0, '[FAIL] report_entry_success\n' + result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, '[FAIL] default_failure_blocks_reuse\n' + result.stdout + result.stderr)
        return result

    def prepare_entry_seed(self):
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        # The fallback needs actual dependency artifacts at the cache owner's
        # normal dependency root. Building this tiny cache executable produces
        # them through its import; no fabricated olean or cold-build override.
        self.write('fixture-mathlib/lakefile.toml', '''name = "mathlib"
buildDir = "../.lake/packages/mathlib/.lake/build"
[[lean_lib]]
name = "Mathlib"
''')
        self.write('fixture-mathlib/Mathlib/Warm.lean', 'def cacheWarmth : Nat := 1\n')
        self.write('Cache.lean', 'import Mathlib.Warm\ndef main : IO Unit := pure ()\n')
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
        return output, expected, seed, sealed, policy

    def probe_seed(self, seed):
        result = self.guarded_command([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
            'probe', '--repository', str(self.root), '--report', str(seed), '--lake', self.lake], env=self.env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(json.loads(result.stdout)['needs_lake'], '[FAIL] probe_only_selects_resources')

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        output, expected, seed, _, policy = self.prepare_entry_seed()
        self.probe_seed(seed)
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        reused = self.inspect()
        self.assertNotIn('phase=ensure status=started', reused.stderr, '[FAIL] heavy_cache_not_required')
        self.assertNotIn('phase=report status=started', reused.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', reused.stdout)
        self.assertEqual(expected, output.read_bytes())
        self.assertFalse((self.root / '.lake/packages').exists())
        self.probe_seed(seed)
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

    def test_report_entry_rejects_damaged_seed_and_rebuilds(self):
        output, expected, seed, sealed, _ = self.prepare_entry_seed()
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        # Resource planning neither parses material semantics nor vouches for
        # bytes that may change before the normal entry consumes its seed.
        for damage in ('sealed-invalid-material', 'changed-after-probe'):
            with self.subTest(damage=damage):
                for suffix, data in sealed.items():
                    publication.member(seed, suffix).write_bytes(data)
                if damage == 'changed-after-probe':
                    self.probe_seed(seed)
                archive = publication.member(seed, '.materials.zip')
                with zipfile.ZipFile(archive, 'a') as target:
                    target.writestr('unreferenced', b'not an admitted report material')
                if damage == 'sealed-invalid-material':
                    receipt = json.loads(sealed['.reuse.json'])
                    receipt['bundle']['.materials.zip'] = publication.digest(archive)
                    publication.member(seed, '.reuse.json').write_text(json.dumps(receipt))
                    self.probe_seed(seed)
                shutil.rmtree(self.root / '.lake')
                recovered = self.inspect()
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr,
                              '[FAIL] invalid_seed_must_reenter_native_producer')
                self.assertEqual(expected, output.read_bytes())
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
