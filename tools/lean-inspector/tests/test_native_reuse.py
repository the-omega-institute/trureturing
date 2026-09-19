"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION


class NativeReuseTests:
    def inspect(self, *, success=True, phase='report-entry'):
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        started = time.monotonic()
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env)
        phases = [dict(field.split('=', 1) for field in line.split()[1:])
                  for line in result.stderr.splitlines() if line.startswith('LEAN_INSPECTOR_PHASE ')]
        logs = []
        for name in dict.fromkeys(row['phase'] for row in phases if row['status'] == 'completed'):
            for stream in ('stdout', 'stderr'):
                path = Path(str(output) + '.logs') / f'{name}.{stream}.log'
                if path.is_file():
                    logs.append(path.read_text())
        lines = '\n'.join(logs).splitlines()
        self.record_result(phase, dict(elapsed_seconds=time.monotonic() - started,
            exit_code=result.returncode, phases=phases,
            work=list(dict.fromkeys(line for line in [*result.stdout.splitlines(), *lines]
                                    if line.startswith('LEAN_INSPECTOR_WORK '))),
            lake_built_lines=sum('Built' in line.split() for line in lines)))
        if success:
            self.assertEqual(result.returncode, 0, '[FAIL] report_entry_success\n' + result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, '[FAIL] default_failure_blocks_reuse\n' + result.stdout + result.stderr)
        return result

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        targets = ['Audit', 'leanInspector/reportInspector']
        self.copy('tools/scripts/workflow/ci_plan.py')
        self.write('Meta/ci-resources.json', json.dumps(dict(schema='ci-resource-execution-v1',
            resources=[dict(id='fixture-program-build', projects=[], checks=[], steps=[], lean_targets=targets)])))
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        compiler_seed = self.compiler_seed
        self.build()  # installs the collection's private compiler stage
        # Observe the real entry's Lake calls without replacing compilation.
        calls = self.root / 'entry-lake-calls.jsonl'
        self.write('entry-tools/lake', '#!/usr/bin/env python3\nimport json, os, sys\n'
            + f'with open({str(calls)!r}, "a") as output: output.write(json.dumps(sys.argv[1:]) + "\\n")\n'
            + f'os.execv({self.lake!r}, [{self.lake!r}, *sys.argv[1:]])\n')
        (self.root / 'entry-tools/lake').chmod(0o755)
        (self.root / 'entry-tools/lean').symlink_to(Path(self.lake).with_name('lean'))
        self.env['LAKE_BIN'] = str(self.root / 'entry-tools/lake')
        def builds():
            return [args for line in calls.read_text().splitlines()
                    if (args := json.loads(line))[:1] == ['build']]
        def clear_calls():
            calls.write_text('')
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        first = self.inspect(phase='initial-publication')
        self.assertIn('phase=report status=completed', first.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file(), '[FAIL] defaults_report_success_sealed')
        expected = output.read_bytes()
        seed = self.root / 'lightweight-seed' / output.name
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix), publication.member(seed, suffix))
        sealed = {suffix: publication.member(seed, suffix).read_bytes()
                  for suffix in (*publication.SUFFIXES, '.reuse.json')}
        def probe(phase='report-probe'):
            started = time.monotonic()
            result = self.guarded_command([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
                'probe', '--repository', str(self.root), '--report', str(seed), '--lake', self.lake], env=self.env)
            self.record_result(phase, dict(elapsed_seconds=time.monotonic() - started,
                exit_code=result.returncode, output=result.stdout, phases=[], work=[], lake_built_lines=0))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)['needs_lake'], '[FAIL] probe_only_selects_resources')
        probe()
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        clear_calls()
        reused = self.inspect(phase='metadata-reuse')
        self.assertEqual(builds(), [])
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
                # Reuse only the class's read-only compiler stage. The damaged
                # report still crosses the same normal fallback and validator.
                if compiler_seed is not None:
                    self.ensure()
                    restored = self.guarded_command([self.lake, 'cache', 'unstage', compiler_seed, 'leanInspector'])
                    self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
                clear_calls()
                recovered = self.inspect(phase=damage)
                self.assertEqual(builds(), [['build', ':report']])
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr,
                              '[FAIL] invalid_seed_must_reenter_native_producer')
                self.assertEqual(expected, output.read_bytes())
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        for suffix, data in sealed.items():
            publication.member(seed, suffix).write_bytes(data)
        # This fixture now requests its explicitly registered program work.
        # Neither a valid nor invalid Audit edit changes report data.
        self.env.pop('STRATALINT_LEAN_BUILD_TARGETS')
        self.write('Audit.lean', 'def audit : Nat := 2\n')
        probe(phase='valid-audit-probe')
        clear_calls()
        compiled = self.inspect(phase='valid-audit-reuse')
        self.assertEqual(builds(), [['build', *targets]])
        self.assertNotIn('phase=report status=started', compiled.stderr)
        self.assertEqual(expected, output.read_bytes())
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # A successful planning probe never exempts the normal entry from the
        # default-only input obligation. A changed audit must reach Lake/fail.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        probe(phase='invalid-audit-probe')
        clear_calls()
        failed = self.inspect(success=False, phase='invalid-audit-reuse')
        self.assertEqual(builds(), [['build', *targets]])
        self.assertIn('LEAN_INSPECTOR_FAILED phase=programs', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        publication.member(seed, '.reuse.json').unlink()
        clear_calls()
        recovered = self.inspect(phase='programs-and-report-miss')
        self.assertEqual(builds(), [['build', ':report', *targets]])
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write('lean-report-inputs.json', json.dumps(policy))
        invalid = self.inspect(success=False, phase='invalid-execution-registration')
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', invalid.stderr)
        self.assertNotIn('phase=report status=started', invalid.stderr)
