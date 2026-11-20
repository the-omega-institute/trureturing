"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION


class NativeLocalReportConsumerTests:
    def test_indexed_push_repairs_evicted_compiler_shard_with_current_report(self):
        for name in ('ci_checks.py', 'ci_compute.py', 'ci_contract.py', 'ci_detect.py', 'judge-lean-producer.sh'):
            self.copy('tools/scripts/workflow/' + name)
        for name in ('lean_actions.py', 'lean_actions_shards.py', 'lean_artifact_inventory.py',
                     'lean_cache_shards.py', 'lean_release_index.py'):
            self.copy('tools/scripts/worktree/' + name)
        for name in ('ci-units.json', 'ci-cache-paths.json', 'FILEMAP.toml'):
            self.copy('Meta/' + name)
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['report_modules']['include'] = [
            dict(pattern='D5/**/*.lean', optional=False), dict(pattern='Reg/**/*.lean', optional=False)]
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.write('utility.json', '[]')
        self.write('Reg/Required.lean', 'def regRequired : Nat := 1\n')
        self.write('tools/lean-inspector/LeanInformationAuditRegTests/Required.lean',
                   'def requiredCheck : Bool := true\n')
        dotnet = self.root / 'bin/dotnet'
        dotnet.write_text(dotnet.read_text().replace('if sys.argv[1] == "build":',
            'if sys.argv[1] == "restore": raise SystemExit(0)\nif sys.argv[1] == "build":'))
        self.write('.gitignore', '.lake/\nbuild/\n__pycache__/\nfixture-mathlib/\n')
        self.write('changed-paths', '')
        self.write('current-budget', '7200\n')
        self.env.update(GITHUB_ACTIONS='true', GITHUB_EVENT_NAME='push',
            GITHUB_REF='refs/heads/integration-ci-cache-tests', GITHUB_REF_PROTECTED='true',
            GITHUB_RUN_ID='12', GITHUB_RUN_ATTEMPT='1', STRATALINT_CACHE_WRITES='true',
            STRATALINT_REPORT_SUCCEEDED='true', STRATALINT_CACHE_PRODUCER_COMPLETE='true',
            STRATALINT_ACCEPT_COLD_BUILD='1', STRATALINT_LEAN_BUILD_TARGETS='["leanInspector/reportInspector"]',
            STRATALINT_CI_COMPUTE_BUDGET=str(self.root / 'current-budget'))

        def run(*args, **env):
            return self.guarded_command(args, env=dict(self.env, **env), timeout=120)

        for args in (('add', '.'), ('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                                   '-c', 'commit.gpgsign=false', 'commit', '-qm', 'native shard fixture')):
            git = run('git', *args)
            self.assertEqual(0, git.returncode, git.stdout + git.stderr)
        anchor = run('git', 'rev-parse', 'HEAD').stdout.strip()
        self.restore_compiler()
        report = (sys.executable, 'tools/scripts/workflow/ci_checks.py', 'current', 'lean-report',
                  '--changed', 'changed-paths')
        full = run(*report, PARTIAL_INDEXED_PROJECT='false')
        self.assertEqual(0, full.returncode, full.stdout + full.stderr)

        shards = (sys.executable, 'tools/scripts/worktree/lean_actions_shards.py')
        snapshot = run(*shards, 'prepare', '--anchor', anchor)
        self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
        index = self.root / 'project-index.json'
        index.write_text(snapshot.stdout.splitlines()[-1] + '\n')
        record = json.loads(index.read_text())
        key = next(key for key, group in record['layout'].items() if any('D5.Alone' in shard for shard in group))
        evicted = record['entries'][key]
        (self.root / 'build/lean-cache/shards/payload' / (evicted + '.tar.gz')).unlink()
        shutil.rmtree(self.root / '.lake/build')
        restored = run(*shards, 'install', '--index', str(index))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        installed = json.loads(restored.stdout.splitlines()[-1])
        self.assertFalse(installed['complete'])
        self.assertEqual([evicted], installed['missing'])
        self.assertGreater(installed['available'], 0)
        build = self.root / '.lake/build'
        compiler = build / 'lib/lean/D5/Alone.olean'
        retained = build / 'reg/lib/lean/Reg/Required.olean'
        retained_mtime = retained.stat().st_mtime_ns
        receipt = build / 'stratalint/raw-lean-report.json.reuse.json'
        self.assertTrue(receipt.is_file())
        self.assertFalse(compiler.exists())

        reused = run(*report, PARTIAL_INDEXED_PROJECT='false')
        self.assertEqual(0, reused.returncode, reused.stdout + reused.stderr)
        self.assertIn('complete-entry-reused', reused.stdout)
        rejected = run(*shards, 'prepare', '--anchor', anchor)
        self.assertIn('project snapshot is missing compiler or report outputs', rejected.stderr)
        self.assertNotEqual(0, rejected.returncode)

        repaired = run(*report, PARTIAL_INDEXED_PROJECT='true')
        self.assertEqual(0, repaired.returncode, repaired.stdout + repaired.stderr)
        self.assertIn('complete-entry-reused', repaired.stdout)
        self.assertTrue(compiler.is_file())
        self.assertEqual(retained_mtime, retained.stat().st_mtime_ns)
        self.write('available-shards.json', json.dumps(sorted(set(record['entries'].values()) - {evicted})))
        published = run(*shards, 'prepare', '--index', str(index), '--available', 'available-shards.json')
        self.assertEqual(0, published.returncode, published.stdout + published.stderr)
        self.assertIn('"complete": true', published.stdout)
        index.write_text(published.stdout.splitlines()[-1] + '\n')
        shutil.rmtree(build)
        complete = run(*shards, 'install', '--index', str(index), '--require-complete')
        self.assertEqual(0, complete.returncode, complete.stdout + complete.stderr)
        self.assertTrue(json.loads(complete.stdout.splitlines()[-1])['complete'])
        self.assertTrue(compiler.is_file())
        self.assertTrue(receipt.is_file())

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
        restored = self.guarded_command(['make', 'lean-report'], env=self.env)
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
            result = self.guarded_command(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'],
                env=self.env if env is None else env)
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
                self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
                programs = ((logs / 'programs.stdout.log').read_text()
                            + (logs / 'programs.stderr.log').read_text())
                self.assertRegex(programs, rf'Built LeanInformationAudit\.{name}(?:\s|$)')
                self.assertNotRegex(programs, r'Built (?:Reg\.|D5\.|Mathlib\.|LeanInformationAuditInterface(?:\.|\s|$))',
                                    '[FAIL] implementation_edit_must_preserve_content_oleans')
                self.assertEqual(stamps, {path: (path.stat().st_mtime_ns, publication.digest(path))
                                          for path in untouched})
                self.assertEqual(report_stamps, self.stamps())
                self.assertEqual(expected, output.read_bytes())
                self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', compiled.stdout)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())

        # A malformed registered implementation still blocks the program build;
        # cached report data cannot conceal that failed obligation.
        receipt_before_failure = publication.member(output, '.reuse.json').read_bytes()
        self.write('tools/lean-inspector/LeanInformationAudit/ArtifactAssessment.lean',
                   implementation('ArtifactAssessment', 'true'))
        self.assertFalse(reuse.probe(self.root, output)['needs_lake'])
        failed = entry('production-consumer-failure')
        self.assertNotEqual(failed.returncode, 0, '[FAIL] production_consumer_failure_must_block_reuse')
        errors = (logs / 'programs.stdout.log').read_text() + (logs / 'programs.stderr.log').read_text()
        self.assertIn('LeanInformationAudit/ArtifactAssessment.lean', errors)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=programs', failed.stdout + failed.stderr)
        self.assertEqual(receipt_before_failure, publication.member(output, '.reuse.json').read_bytes(),
                         '[FAIL] program_failure_preserves_successful_report_receipt')
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

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        self.reg_package()
        targets = ['leanInspector/reportInspector', 'trureturing/Audit']
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        compiler_seed = self.compiler_seed
        self.ensure()
        self.restore_compiler()
        self.check_cold_project(self)
        # Observe the real entry's Lake calls without replacing compilation.
        calls = self.root / 'entry-lake-calls.jsonl'
        self.write('entry-tools/lake', '#!/usr/bin/env python3\nimport json, os, sys\n'
            + f'with open({str(calls)!r}, "a") as output: output.write(json.dumps(sys.argv[1:]) + "\\n")\n'
            + f'os.execv({self.lake!r}, [{self.lake!r}, *sys.argv[1:]])\n')
        (self.root / 'entry-tools/lake').chmod(0o755)
        (self.root / 'entry-tools/lean').symlink_to(Path(self.lake).with_name('lean'))
        self.env['LAKE_BIN'] = str(self.root / 'entry-tools/lake')
        workspace = ['--log-level=error', '-d', str((self.root / 'tools/lean-inspector-reg').resolve())]
        def builds():
            return [args for line in calls.read_text().splitlines()
                    if (args := json.loads(line))[:len(workspace) + 1] == [*workspace, 'build']]
        def clear_calls():
            calls.write_text('')
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertEqual(self.stamps(), {}, '[FAIL] first_entry_must_produce_its_cold_report')
        first = self.inspect(phase='initial-publication',
                             env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
        fact = self.root / 'build/lean-cache/build-work.json'
        self.assertTrue(fact.is_file(), '[FAIL] invocation_work_fact')
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
        work = json.loads(fact.read_text())
        self.assertEqual((0, 0), (work['report'], work['programs']))
        self.assertEqual(expected, output.read_bytes())
        self.assertFalse((self.root / '.lake/packages').exists())
        # Resource planning neither parses material semantics nor vouches for
        # bytes that may change before the normal entry consumes its seed.
        for damage in ('changed-after-probe',):
            with self.subTest(damage=damage):
                for suffix, data in sealed.items():
                    publication.member(seed, suffix).write_bytes(data)
                probe()
                archive = publication.member(seed, '.materials.zip')
                with zipfile.ZipFile(archive, 'a') as target:
                    target.writestr('unreferenced', b'not an admitted report material')
                shutil.rmtree(self.root / '.lake')
                # Reuse only the class's read-only compiler stage. The damaged
                # report still crosses the same normal fallback and validator.
                if compiler_seed is not None:
                    self.ensure()
                    restored = self.guarded_command([self.lake, 'cache', 'unstage', compiler_seed, 'leanInspector'])
                    self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
                clear_calls()
                recovered = self.inspect(phase=damage, env=dict(self.env, STRATALINT_ACCEPT_COLD_BUILD='1'))
                self.assertEqual(builds(), [[*workspace, 'build', ':report']])
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr,
                              '[FAIL] invalid_seed_must_reenter_native_producer')
                self.assertEqual(expected, output.read_bytes())
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        for suffix, data in sealed.items():
            publication.member(seed, suffix).write_bytes(data)
        # This fixture requests its program work through the public override.
        # Neither a valid nor invalid Audit edit changes report data.
        self.env['STRATALINT_LEAN_BUILD_TARGETS'] = json.dumps(targets)
        self.write('Audit.lean', 'def audit : Nat := 2\n')
        probe(phase='valid-audit-probe')
        clear_calls()
        compiled = self.inspect(phase='valid-audit-reuse')
        work = json.loads(fact.read_text())
        self.assertEqual(0, work['report'])
        self.assertGreater(work['programs'], 0)
        self.assertEqual(builds(), [[*workspace, 'build', *targets]])
        self.assertNotIn('phase=report status=started', compiled.stderr)
        self.assertEqual(expected, output.read_bytes())
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # A successful planning probe never exempts the normal entry from the
        # default-only input obligation. A changed audit must reach Lake/fail.
        receipt_before_failure = publication.member(output, '.reuse.json').read_bytes()
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        probe(phase='invalid-audit-probe')
        clear_calls()
        failed = self.inspect(success=False, phase='invalid-audit-reuse')
        self.assertFalse(fact.exists(), '[FAIL] failed_build_has_no_successful_work_fact')
        self.assertEqual(builds(), [[*workspace, 'build', *targets]])
        self.assertIn('LEAN_INSPECTOR_FAILED phase=programs', failed.stderr)
        self.assertEqual(receipt_before_failure, publication.member(output, '.reuse.json').read_bytes(),
                         '[FAIL] program_failure_preserves_successful_report_receipt')
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
