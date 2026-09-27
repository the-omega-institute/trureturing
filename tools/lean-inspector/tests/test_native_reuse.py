"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION


class NativeReportConsumerTests:
    def test_impl_resource_rebuilds_production_reg_on_warm_report(self):
        # Use the actual Impl resource selection, package target declarations,
        # report entry and Lake compiler. Only the mathematical inputs are tiny.
        sys.path.insert(0, str(ROOT / 'tools/scripts/workflow'))
        import ci_plan
        read = lambda path: (ROOT / path).read_bytes()
        filemap = ci_plan.load_filemap(read(ci_plan.FILEMAP), read)
        resources = {row['id']: row for row in filemap['resources']}
        impl = 'tools/lean-inspector/LeanInformationAudit/RegistrationGates.lean'
        owner, = [row for row in filemap['files'] if ci_plan.glob(row['pattern']).fullmatch(impl)]
        selected = ci_plan.closure(resources, owner['require'])
        execution = ci_plan.execution_selection(read, [resources[key] for key in selected], resources)
        self.assertIn('lean-report', execution['steps'])
        self.reg_package()
        self.build()  # Restore the native fixture's private compiler stage.
        self.copy('tools/scripts/workflow/ci_plan.py')
        self.copy('Meta/ci-resources.json')
        root_config = self.root / 'lakefile.toml'
        root_config.write_text(root_config.read_text().replace(
            '[[lean_lib]]\nname = "LeanInformationAudit"\nglobs = ["LeanInformationAudit.+"]\n', ''))
        registry = 'LeanInformationAudit/Registry.lean'
        registry_owner = 'tools/lean-inspector/' + registry
        (self.root / registry_owner).parent.mkdir(parents=True, exist_ok=True)
        (self.root / registry).rename(self.root / registry_owner)
        with (self.root / 'tools/lean-inspector/lakefile.lean').open('a') as stream:
            stream.write('\nlean_lib LeanInformationAudit where\n'
                         '  globs := #[.submodules `LeanInformationAudit]\n')
        self.write(impl, 'def gateValue : Nat := 1\n')
        self.write('Reg/ProductionOnly.lean', 'import LeanInformationAudit.RegistrationGates\n'
                   'import D5.A\ndef productionValue : Nat := gateValue + value\n')
        # Required.lean deliberately imports no production Reg module.
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        for row in policy['dependency_sources']['include']:
            if row['pattern'] == registry:
                row['pattern'] = registry_owner
        policy['dependency_sources']['include'].append(dict(pattern=impl, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.env['STRATALINT_LEAN_BUILD_TARGETS'] = json.dumps(execution['lean_targets'])
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'

        def entry(phase):
            result = self.guarded_command(['make', 'lean-report'], env=self.env)
            logs = Path(str(output) + '.logs')
            paths = [path for path in logs.iterdir() if path.is_file()]
            self.record_result(phase, dict(exit_code=result.returncode,
                stdout=result.stdout, stderr=result.stderr, targets=execution['lean_targets']), paths)
            return result

        initial = entry('production-initial')
        self.assertEqual(initial.returncode, 0, initial.stdout + initial.stderr)
        expected = output.read_bytes()
        report_stamps = self.stamps()
        untouched = [* (self.root / '.lake/build/lib/lean/D5').rglob('*.olean'),
                     * (self.root / '.lake/packages/mathlib/.lake/build').rglob('*.olean')]
        self.assertTrue(untouched)
        stamps = {path: (path.stat().st_mtime_ns, publication.digest(path)) for path in untouched}
        production = self.root / '.lake/build/reg/lib/lean/Reg/ProductionOnly.olean'
        before = production.stat().st_mtime_ns
        self.write(impl, 'def gateValue : Nat := 2\n')
        import reuse
        self.assertFalse(reuse.probe(self.root, output)['needs_lake'])
        compiled = entry('production-warm')
        self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
        logs = Path(str(output) + '.logs')
        programs = (logs / 'programs.stdout.log').read_text() + (logs / 'programs.stderr.log').read_text()
        self.assertRegex(programs, r'Built LeanInformationAudit\.RegistrationGates(?:\s|$)')
        self.assertRegex(programs, r'Built Reg\.ProductionOnly(?:\s|$)',
                         '[FAIL] warm_report_must_compile_production_reg_outside_test_imports')
        self.assertNotEqual(before, production.stat().st_mtime_ns)
        self.assertNotRegex(programs, r'Built (?:D5\.|Mathlib\.)')
        self.assertEqual(stamps, {path: (path.stat().st_mtime_ns, publication.digest(path)) for path in untouched})
        self.assertEqual(report_stamps, self.stamps())
        self.assertEqual(expected, output.read_bytes())
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', compiled.stdout)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())

        # The Impl still compiles; its production-only consumer now fails.
        # No report-module edit or report miss is used to expose the failure.
        self.write(impl, 'def gateValue : Bool := true\n')
        self.assertFalse(reuse.probe(self.root, output)['needs_lake'])
        failed = entry('production-consumer-failure')
        self.assertNotEqual(failed.returncode, 0, '[FAIL] production_consumer_failure_must_block_reuse')
        errors = (logs / 'programs.stdout.log').read_text() + (logs / 'programs.stderr.log').read_text()
        self.assertIn('Reg/ProductionOnly.lean', errors)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=programs', failed.stdout + failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.assertEqual(expected, output.read_bytes())
        self.assertEqual(report_stamps, self.stamps())

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
        self.reg_package()
        targets = ['leanInspector/reportInspector', 'trureturing/Audit']
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
        workspace = ['-d', str((self.root / 'Reg').resolve())]
        def builds():
            return [args for line in calls.read_text().splitlines()
                    if (args := json.loads(line))[:3] == [*workspace, 'build']]
        def clear_calls():
            calls.write_text('')
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        first = self.inspect(phase='initial-publication')
        self.assertIn('phase=report status=completed', first.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file(), '[FAIL] defaults_report_success_sealed')
        expected = output.read_bytes()
        # An explicitly report-only resource must stay report-only on a miss too.
        # An invalid, unselected program proves the facet cannot demand defaults.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        publication.member(output, '.reuse.json').unlink()
        clear_calls()
        report_only = self.inspect(phase='report-only-miss-with-unselected-invalid-program')
        self.assertEqual(builds(), [[*workspace, 'build', ':report']])
        self.assertIn('phase=report status=completed', report_only.stderr)
        self.assertEqual(expected, output.read_bytes())
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        seed = self.root / 'lightweight-seed' / output.name
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix), publication.member(seed, suffix))
        sealed = {suffix: publication.member(seed, suffix).read_bytes()
                  for suffix in (*publication.SUFFIXES, '.reuse.json')}
        def probe(phase='report-probe'):
            started = time.monotonic()
            result = self.guarded_command([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
                'probe', '--repository', str(self.root), '--report', str(seed)], env=self.env)
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
                self.assertEqual(builds(), [[*workspace, 'build', ':report']])
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
        self.assertEqual(builds(), [[*workspace, 'build', *targets]])
        self.assertNotIn('phase=report status=started', compiled.stderr)
        self.assertEqual(expected, output.read_bytes())
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # A successful planning probe never exempts the normal entry from the
        # default-only input obligation. A changed audit must reach Lake/fail.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        probe(phase='invalid-audit-probe')
        clear_calls()
        failed = self.inspect(success=False, phase='invalid-audit-reuse')
        self.assertEqual(builds(), [[*workspace, 'build', *targets]])
        self.assertIn('LEAN_INSPECTOR_FAILED phase=programs', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        publication.member(seed, '.reuse.json').unlink()
        clear_calls()
        recovered = self.inspect(phase='programs-and-report-miss')
        self.assertEqual(builds(), [[*workspace, 'build', ':report', *targets]])
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write('lean-report-inputs.json', json.dumps(policy))
        invalid = self.inspect(success=False, phase='invalid-execution-registration')
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', invalid.stderr)
        self.assertNotIn('phase=report status=started', invalid.stderr)
