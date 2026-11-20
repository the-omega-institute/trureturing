"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION


class NativeLocalReportConsumerTests:
    def test_canonical_reader_runs_executable_git_adapter(self):
        result = self.guarded_command(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
            'bash', '-c', 'command -v git && git --version'],
            env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(str((self.root / 'tools/scripts/worktree/lean-git/git').resolve()), result.stdout)
        self.assertIn('git version ', result.stdout)

    def test_local_restored_format_keeps_native_incremental_extraction(self):
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        self.write('lean-report-inputs.json', json.dumps(policy))
        for name in ('lean_cache_release.py', 'lean_cache_release_io.py', 'lean_cache_topology.py', 'cache_material.py'):
            self.copy('tools/scripts/worktree/' + name)
        # Make owns the real native report build; only Release transport is replaced.
        compiler_seed = self.compiler_seed
        self.ensure()
        self.restore_compiler()
        if compiler_seed is not None:
            for material in Path(compiler_seed).iterdir():
                if material.name == 'outputs.jsonl':
                    continue
                private = self.root / '.lake/artifact-cache/artifacts' / material.name
                self.assertTrue(private.is_file(), '[FAIL] local_entry_must_restore_supplied_compiler')
                self.assertEqual(publication.digest(private), publication.digest(material))
                self.assertFalse(os.path.samestat(material.stat(), private.stat()))
        self.check_cold_project(self)
        self.prepare_report_modules(workspace='tools/lean-inspector-reg')
        first = self.guarded_command(['make', 'lean-report', 'REBUILD_REPORT_CACHE=1'],
            env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        saved = self.root / 'saved-seed'
        saved.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copy2(publication.member(output, suffix), publication.member(saved / output.name, suffix))
        before = self.stamps()
        receipt = publication.member(output, '.reuse.json')
        value = json.loads(receipt.read_text())
        value['inputs']['report_format'] = 'incompatible-report-format'
        receipt.write_text(json.dumps(value))
        self.write('tools/scripts/worktree/lean-cache-publish.sh', '#!/bin/bash\nset -euo pipefail\n'
            'printf "%s\\n" "$*" > fetch-call\ncp saved-seed/* .lake/build/stratalint/\n')
        self.write('D5/Alone.lean', 'def alone : Nat := 9\n')
        self.prepare_report_modules('D5.Alone')
        restored = self.guarded_command(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=fetch-or-fail'], env=self.env)
        self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
        self.assertIn('--refresh-stale --writer-owned', (self.root / 'fetch-call').read_text())
        changed = sorted(name for name, stamp in self.stamps().items() if stamp != before[name])
        self.assertEqual(changed, ['D5.Alone'], '[FAIL] restored_format_extracts_only_changed_module')
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=1 aggregates=1', restored.stdout)
        self.record_result('local-format-restored-incremental', dict(exit_code=restored.returncode,
            modules=len(before), extracted_modules=1, changed=changed))
        warm = self.guarded_command(['make', 'lean-report'], env=self.env)
        self.assertEqual(warm.returncode, 0, warm.stdout + warm.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', warm.stdout)


class NativeReportConsumerTests:
    def test_reg_dependency_closure_reassessment(self):
        # Typed Reg leaf and interface inputs select their compiler dependency closure.
        # Tiny typed transport inputs exercise production discovery, facets and publication;
        # mathematical assessment belongs to the compiled Reg judge tests.
        self.reg_package()
        core = self.root / 'tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/Core.lean'
        original = core.read_text()
        contract = '\nnamespace LeanInformationAudit.Contract\nstructure Registration where\n  value : Nat\nend LeanInformationAudit.Contract\n'
        core.write_text(original + contract)
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['config_inputs']['include'].append(dict(
            pattern='tools/lean-inspector-interface/**/*.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.write('Reg/Leaf.lean', 'import LeanInformationAuditInterface.Contract.Core\n'
            'def Reg.Leaf.entry : LeanInformationAudit.Contract.Registration := { value := 1 }\n')
        self.write('Reg/Parent.lean', 'import Reg.Leaf\n'
            'def Reg.Parent.entry : LeanInformationAudit.Contract.Registration := { value := Reg.Leaf.entry.value + 1 }\n')
        self.write('Reg/Unrelated.lean', 'def Reg.Unrelated.value : Nat := 1\n')
        work = self.root / 'module-work.jsonl'
        self.env['STRATALINT_INSPECTOR_MODULE_WORK'] = str(work)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'

        def entry(phase, *, env=None):
            work.write_text('')
            before = self.stamps()
            oleans = {path: (path.stat().st_mtime_ns, publication.digest(path))
                      for path in (self.root / '.lake/build/reg').rglob('*.olean')}
            self.prepare_report_modules(workspace='tools/lean-inspector-reg')
            result = self.guarded_command(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'],
                env=dict(self.env if env is None else env, TEST_REPORT_REGISTRATION_GATE='1'))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            records = [json.loads(line) for line in work.read_text().splitlines()]
            data = dict(exit_code=result.returncode, modules=len(self.stamps()),
                extracted=sorted(row['module'] for row in records if row['operation'] == 'extract'),
                assessed=sorted(row['module'] for row in records if row['operation'] == 'assess'),
                reg_recompiled=sorted(path.relative_to(self.root).as_posix() for path in oleans
                    if (path.stat().st_mtime_ns, publication.digest(path)) != oleans[path]),
                report_changed=sorted(name for name, stamp in self.stamps().items()
                    if name not in before or stamp != before[name]),
                whole_report_reused='LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0' in result.stdout)
            self.record_result(phase, data, [work])
            return data

        # Hold the shared prerequisite inside Lake's lookup/create gap until
        # an independent consumer contends on graphFetch or creates it again.
        # Observe a pending predecessor after the real atomic queue append;
        # never infer overlap from time or replace the queue algorithm.
        config = self.root / 'lakefile.toml'
        config.write_text(config.read_text().replace(
            'name = "LeanInformationAudit"\n',
            'name = "LeanInformationAudit"\nneeds = ["leanInspector/compilerRegistrationGate"]\n'))
        producer_config = self.root / 'tools/lean-inspector/lakefile.lean'
        source = producer_config.read_text()
        schedule = '''
structure RegistrationSchedule where
  state : Std.Mutex (Nat × Nat)
  firstRegistration : IO.Promise Unit
  release : IO.Promise String

package_facet compilerRegistrationState (_pkg : Package) : RegistrationSchedule := do
  Job.async do return ⟨← Std.Mutex.new (0, 0), ← IO.Promise.new, ← IO.Promise.new⟩

'''
        queued = '''  unless ← IO.hasFinished previous do
    let schedule ← liftM (m := FetchM) do
      (← fetch <| (← getWorkspace).root.facet `compilerRegistrationState).await
    liftM (m := BaseIO) <| schedule.state.atomically fun state => do
      let (registered, waiting) ← state.get
      state.set (registered, waiting + 1)
      if registered > 0 then schedule.release.resolve "contended"
'''
        # Only the test observer needs FetchM. All production call sites already
        # run in FetchM or JobM; their critical sections remain unchanged.
        mutex = 'private def CompilerMutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]\n'
        wait = '  discard <| IO.wait previous\n'
        self.assertEqual(source.count(mutex), 1)
        self.assertEqual(source.count(wait), 1)
        source = source.replace(mutex, schedule + mutex.replace(
            '[MonadFinally m]', '[MonadLiftT FetchM m] [MonadFinally m]')).replace(
            wait, queued + wait)
        contender = '''
package_facet compilerRegistrationContender (pkg : Package) : Unit := do
  let schedule ← (← fetch <| (← getWorkspace).root.facet `compilerRegistrationState).await
  let reportState ← (← fetch <| pkg.facet `reportBatch).await
  let some registry := (← getWorkspace).findModule? `LeanInformationAudit.TemplateEnrollment
    | error "missing fixture enrollment module"
  Job.async do
    discard <| IO.wait schedule.firstRegistration.result!
    let enrollment ← reportState.graphFetch.atomically fun _ =>
      JobM.runFetchM registry.exportInfo.fetch
    discard <| enrollment.await

'''
        if 'import Std.Sync.Mutex\n' not in source:
            source = 'import Std.Sync.Mutex\n' + source
        batch = 'package_facet reportBatch (_pkg : Package) : ReportState := do\n'
        inputs = 'package_facet reportInputs (pkg : Package) : FilePath := do\n'
        enrollment = '      let enrollment ← reportState.graphFetch.atomically fun _ =>\n'
        self.assertEqual(source.count(inputs), 1)
        self.assertEqual(source.count(enrollment), 1)
        producer_config.write_text(source.replace(
            batch, batch + '  discard <| (← fetch <| (← getWorkspace).root.facet `compilerRegistrationState).await\n').replace(
            inputs, contender + inputs).replace(enrollment,
                '      let contender ← JobM.runFetchM <| fetch <| pkg.facet `compilerRegistrationContender\n'
                '      deps := deps.add contender\n' + enrollment))
        with producer_config.open('a') as target:
            target.write('''\ntarget compilerRegistrationGate pkg : Unit := do
  unless (← IO.getEnv "TEST_REPORT_REGISTRATION_GATE") == some "1" do return Job.nil
  let root ← repositoryDir pkg
  let schedule ← (← fetch <| (← getWorkspace).root.facet `compilerRegistrationState).await
  schedule.state.atomically fun state => do
    let (registered, waiting) ← state.get
    state.set (registered + 1, waiting)
    IO.FS.withFile (root / "compiler-registrations") .append fun out => out.putStrLn "registered"
    if registered == 0 then schedule.firstRegistration.resolve ()
    if registered > 0 then schedule.release.resolve "duplicate"
    else if waiting > 0 then schedule.release.resolve "contended"
  let reason ← IO.wait schedule.release.result!
  IO.FS.writeFile (root / "compiler-registration-sync") reason
  return Job.nil
''')
        # Like the other direct-entry consumers, restore only the supplied
        # compiler material. Lake still builds every private project/report
        # output from cold and validates the modified contract traces.
        self.ensure()
        self.restore_compiler()
        self.check_cold_project(self)
        initial = entry('initial', env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
        sync = self.root / 'compiler-registration-sync'
        registrations = self.root / 'compiler-registrations'
        self.record_result('compiler-registration', dict(
            registrations=registrations.read_text().splitlines(), release=sync.read_text()), [registrations, sync])
        self.assertEqual((self.root / 'compiler-registrations').read_text().splitlines(), ['registered'],
                         '[FAIL] shared compiler prerequisites must be registered once per Lake invocation')
        self.assertEqual(sync.read_text(), 'contended', '[FAIL] compiler registration overlap must be controlled')
        self.assertEqual(initial['assessed'], ['Reg.Leaf', 'Reg.Parent'])
        driver = self.root / 'LeanInformationAudit/TemplateEnrollment.lean'
        driver.write_text('def fixtureDriver : Nat := 2\n')
        warm = entry('implementation')
        self.assertEqual(warm['extracted'], [])
        self.assertEqual(warm['assessed'], [])
        self.assertEqual(warm['reg_recompiled'], [])
        self.assertTrue(warm['whole_report_reused'])
        leaf = self.root / 'Reg/Leaf.lean'
        leaf.write_text(leaf.read_text().replace('value := 1', 'value := 2'))
        changed = entry('leaf')
        self.assertEqual(changed['extracted'], ['Reg.Leaf', 'Reg.Parent'])
        self.assertEqual(changed['assessed'], ['Reg.Leaf', 'Reg.Parent'])
        core.write_text(original + contract.replace('value : Nat', 'value : Int'))
        changed = entry('interface')
        self.assertEqual(changed['extracted'], ['Reg.Leaf', 'Reg.Parent'])
        self.assertEqual(changed['assessed'], ['Reg.Leaf', 'Reg.Parent'])
        self.assertEqual(len(changed['reg_recompiled']), 2)

    def test_impl_resource_preserves_production_reg_on_warm_report(self):
        # Use the default program targets of a direct report call, the package
        # target declarations, report entry and Lake compiler. Only the
        # mathematical inputs are tiny.
        implementations = ('CompiledAssessment', 'ArtifactAssessment')
        targets = ['leanInspector/LeanInformationAudit', 'leanInspector/reportInspector',
                   'leanInspectorInterface/LeanInformationAuditInterface', 'reg/Reg']
        self.reg_package()
        # Restore the same compiler materials without producing an unrelated
        # report before this case has installed its production configuration.
        self.ensure()
        self.restore_compiler()
        self.check_cold_project(self)
        root_config = self.root / 'lakefile.toml'
        source = root_config.read_text()
        start = source.index('[[lean_lib]]\nname = "LeanInformationAudit"\n')
        stop = source.find('[[', start + 2)
        root_config.write_text(source[:start] + (source[stop:] if stop != -1 else ''))
        registry = 'LeanInformationAudit/TemplateEnrollment.lean'
        registry_owner = 'tools/lean-inspector/' + registry
        for module in [registry]:
            owner = self.root / 'tools/lean-inspector' / module
            owner.parent.mkdir(parents=True, exist_ok=True)
            (self.root / module).rename(owner)
        inspector_config = self.root / 'tools/lean-inspector/lakefile.lean'
        source = inspector_config.read_text()
        start = source.index('lean_lib LeanInformationAudit where\n')
        stop = source.index('lean_exe reportInspector where', start)
        inspector_config.write_text(source[:start] + 'lean_lib LeanInformationAudit where\n'
            '  globs := #[.submodules `LeanInformationAudit]\n\n' + source[stop:])
        def implementation(name, body):
            return (f'namespace LeanInformationAudit.{name}\n'
                    f'def fixtureValue (input : Nat) : Nat := {body}\n'
                    f'end LeanInformationAudit.{name}\n')
        for name in implementations:
            self.write(f'tools/lean-inspector/LeanInformationAudit/{name}.lean',
                       implementation(name, 'input + 1'))
        # CompiledAssessment is an actual import of the fixture's report driver, so
        # its body edit exercises the TemplateEnrollment closure as well as defaults.
        driver = self.root / registry_owner
        driver.write_text('import LeanInformationAudit.ArtifactAssessment\n'
                          'import LeanInformationAudit.CompiledAssessment\n' + driver.read_text())
        self.write('Reg/ProductionOnly.lean', 'import LeanInformationAuditInterface.Contract.Core\n'
                   'import D5.A\ndef productionValue : Nat := value\n')
        # Required.lean deliberately imports no production Reg module.
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        for row in policy['dependency_sources']['include']:
            if row['pattern'] == registry:
                row['pattern'] = registry_owner
        for name in implementations:
            policy['dependency_sources']['include'].append(dict(
                pattern=f'tools/lean-inspector/LeanInformationAudit/{name}.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.env['STRATALINT_LEAN_BUILD_TARGETS'] = json.dumps(targets)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'

        def entry(phase, *, env=None):
            result = self.guarded_command(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'],
                env=self.env if env is None else env)
            logs = Path(str(output) + '.logs')
            paths = [path for path in logs.iterdir() if path.is_file()]
            self.record_result(phase, dict(exit_code=result.returncode,
                stdout=result.stdout, stderr=result.stderr, targets=targets), paths)
            return result

        self.assertFalse(output.exists(), '[FAIL] configured_report_must_start_cold')
        self.assertEqual(self.stamps(), {}, '[FAIL] no_report_before_configured_production')
        self.prepare_report_modules(workspace='tools/lean-inspector-reg')
        initial = entry('production-initial', env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
        self.assertEqual(initial.returncode, 0, initial.stdout + initial.stderr)
        expected = output.read_bytes()
        report_stamps = self.stamps()
        untouched = [* (self.root / '.lake/build/lib/lean/D5').rglob('*.olean'),
                     * (self.root / '.lake/build/reg/lib/lean/Reg').rglob('*.olean'),
                     * (self.root / '.lake/build/lean-inspector/interface').rglob('*.olean'),
                     * (self.root / '.lake/packages/mathlib/.lake/build').rglob('*.olean')]
        self.assertTrue(untouched)
        self.assertTrue(any('interface' in path.parts for path in untouched))
        stamps = {path: (path.stat().st_mtime_ns, publication.digest(path)) for path in untouched}
        production = self.root / '.lake/build/reg/lib/lean/Reg/ProductionOnly.olean'
        self.assertIn(production, stamps)
        import reuse
        logs = Path(str(output) + '.logs')
        for name in implementations:
            with self.subTest(implementation=name):
                self.write(f'tools/lean-inspector/LeanInformationAudit/{name}.lean',
                           implementation(name, 'input + 2'))
                self.assertFalse(reuse.probe(self.root, output)['needs_lake'])
                compiled = entry(f'production-warm-{name}')
                self.assertNotIn('phase=programs ', compiled.stderr)
                self.assertEqual(stamps, {path: (path.stat().st_mtime_ns, publication.digest(path))
                                          for path in untouched})
                self.assertEqual(report_stamps, self.stamps())
                self.assertEqual(expected, output.read_bytes())
                self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', compiled.stdout)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())

        self.write('tools/lean-inspector/LeanInformationAudit/ArtifactAssessment.lean',
                   implementation('ArtifactAssessment', 'true'))
        self.assertFalse(reuse.probe(self.root, output)['needs_lake'])
        reused = entry('production-consumer-reuse')
        self.assertEqual(reused.returncode, 0, reused.stderr)
        self.assertNotIn('phase=programs ', reused.stderr)
        self.assertEqual(expected, output.read_bytes())
        self.assertEqual(report_stamps, self.stamps())

    def inspect(self, *, success=True, phase='report-entry', env=None):
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        started = time.monotonic()
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env if env is None else env)
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
            build_work=[line for line in result.stdout.splitlines() if line.startswith('LEAN_BUILD_WORK ')],
            lake_built_lines=sum('Built' in line.split() for line in lines)))
        if success:
            self.assertEqual(result.returncode, 0, '[FAIL] report_entry_success\n' + result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, '[FAIL] default_failure_blocks_reuse\n' + result.stdout + result.stderr)
        return result

    def test_report_can_restore_from_store_without_materializing_git_packages(self):
        self.reg_package()
        self.prepare_report_modules(workspace='tools/lean-inspector-reg')
        output = self.root / 'reports' / publication.RAW
        command = ['make', 'lean-report', 'FULL_BUILD=1', 'LEAN_REPORT=' + str(output),
                   'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build']
        lake_wrapper = self.root / 'bin' / 'observed-lake'
        lake_wrapper.write_text('#!/bin/sh\ntest -d .lake/build && echo build >> lake-started || '
                                'echo empty >> lake-started\nexec "$REAL_LAKE" "$@"\n')
        lake_wrapper.chmod(0o755)
        environment = dict(self.env, REAL_LAKE=self.lake, LAKE_BIN=str(lake_wrapper))
        started = self.root / 'lake-started'
        build = self.root / '.lake/build'
        shutil.rmtree(build)
        store = Path(environment['LAKE_CACHE_DIR'])

        def cached_files():
            return {p.relative_to(store): (p.stat().st_size, p.stat().st_mtime_ns)
                    for p in store.rglob('*') if p.is_file()}

        cached = cached_files()
        self.assertTrue(cached)
        restored = self.guarded_command(command, env=environment)
        self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
        self.assertEqual(cached_files(), cached, 'analysis must treat the shared store as read-only')
        self.assertEqual(started.read_text().splitlines(), ['empty'])
        self.assertTrue((build / 'lib/lean/ClaimSupport.olean').is_file())
        publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        expected = output.read_bytes()
        started.unlink()

        mathlib = self.root / '.lake/packages/mathlib'
        mathlib.rename(self.root / 'saved-mathlib')
        missing = self.guarded_command(command, env=environment)
        self.assertNotEqual(missing.returncode, 0)
        self.assertIn('Missing prebuilt Git dependency mathlib', missing.stderr)
        self.assertFalse(started.exists())
        self.assertFalse(mathlib.exists())
        self.assertEqual(output.read_bytes(), expected)

        explicit = self.guarded_command(['make', 'lean', 'LEAN_TARGETS=+D5.Alone'], env=self.env)
        self.assertEqual(explicit.returncode, 0, explicit.stdout + explicit.stderr)
        subprocess.run(['git', '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                        '-c', 'commit.gpgsign=false', 'commit', '--allow-empty', '-qm', 'different revision'],
                       cwd=mathlib, check=True)
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib)
        stale = self.guarded_command(command, env=environment)
        self.assertNotEqual(stale.returncode, 0)
        self.assertIn('Prebuilt Git dependency mathlib is not checked out at', stale.stderr)
        self.assertFalse(started.exists())
        self.assertEqual(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib), revision)
        self.assertEqual(output.read_bytes(), expected)

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        self.reg_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.ensure()
        self.restore_compiler()
        self.prepare_report_modules(workspace='tools/lean-inspector-reg')
        report = self.root / '.lake/build/stratalint/raw-lean-report.json'
        first = self.inspect(phase='current-artifacts')
        self.assertIn('phase=report status=completed', first.stderr)
        expected = report.read_bytes()
        receipt = publication.member(report, '.reuse.json')
        self.assertTrue(receipt.is_file())
        warm = self.inspect(phase='native-trace-reuse')
        self.assertIn('phase=report status=completed', warm.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', warm.stdout)
        self.assertEqual(expected, report.read_bytes())

        # An older release can contain all compiled modules but no workspace configuration.
        config = self.root / 'tools/lean-inspector-reg/.lake/config'
        config.rename(config.with_name('prepared-config'))
        missing_config = self.inspect(success=False, phase='missing-lake-configuration')
        self.assertIn('make lean-report-prepare', missing_config.stderr)
        self.assertFalse(config.exists())
        self.assertEqual(expected, report.read_bytes())
        config.with_name('prepared-config').rename(config)

        dependency = self.root / '.lake/build/lib/lean/ClaimSupport.olean'
        original = dependency.read_bytes()
        dependency.unlink()
        self.inspect(phase='restore-prebuilt-cache')
        self.assertEqual(original, dependency.read_bytes())
        self.assertEqual(expected, report.read_bytes())
        dependency.unlink()
        shutil.rmtree(self.root / '.lake/artifact-cache')
        missing = self.inspect(success=False, phase='missing-prebuilt-dependency')
        self.assertIn('ClaimSupport', missing.stderr)
        self.assertFalse(dependency.exists(), 'analysis must leave a missing compiler output absent')
        self.assertEqual(expected, report.read_bytes())
        self.prepare_report_modules('ClaimSupport', workspace='tools/lean-inspector-reg')
        self.assertEqual(original, dependency.read_bytes())
        self.inspect(phase='restored-inputs')
        self.assertEqual(expected, report.read_bytes())
        self.assertTrue(receipt.is_file())
        source = self.root / 'ClaimSupport.lean'
        source.write_text(source.read_text() + 'def extraDependencyValue : Nat := 1\n')
        stale = self.inspect(success=False, phase='stale-prebuilt-dependency')
        self.assertIn('ClaimSupport', stale.stderr)
        self.assertEqual(original, dependency.read_bytes())
        self.assertEqual(expected, report.read_bytes())
        policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write('lean-report-inputs.json', json.dumps(policy))
        invalid = self.inspect(success=False, phase='invalid-execution-registration')
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', invalid.stderr)
        self.assertNotIn('phase=report status=started', invalid.stderr)
