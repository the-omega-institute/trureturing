"""Compiler provenance through native links, imports and the actual report facet."""
import re
from test_native_support import *


class NativeOriginTests:
    def measure_origin_commands(self):
        checks = []
        run_lake = self.run_lake
        def measured(*args, **kwargs):
            started = time.monotonic()
            result = run_lake(*args, **kwargs)
            built = re.findall(r'Built (\S+) \(', result.stdout + result.stderr)
            work = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
            counts = {kind: sum(row['count'] for row in work if row['kind'] == kind)
                for kind in ('extract', 'aggregate')} if args[:2] == ('build', ':report') else None
            checks.append(dict(command=list(args), exit=result.returncode,
                seconds=round(time.monotonic() - started, 3),
                built=len(built), compiled_modules=[name for name in built if ':' not in name and '/' not in name],
                work=counts))
            self.record_result('measurements', dict(checks=checks))
            return result
        self.run_lake = measured
        self.addCleanup(setattr, self, 'run_lake', run_lake)
        return checks

    def test_stock_package_cache_miss_and_source_invalidation(self):
        checks = self.measure_origin_commands()
        self.write('fixture-mathlib/lakefile.toml', 'name = "mathlib"\n[[lean_lib]]\nname = "Stock"\n')
        self.write('D5/A.lean', 'import D5.B\nimport Stock\ndef value : Nat := D5.hidden\n')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['dependency_sources']['include'].append(dict(pattern='fixture-mathlib/Stock.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        traces = []
        for fields in ('(n : Nat)', '(n m : Nat)'):
            self.write('fixture-mathlib/Stock.lean', '''import Lean
run_elab
  let some sysroot ← IO.getEnv "LEAN_SYSROOT" | throwError "missing stock sysroot"
  unless (← IO.getEnv "LEAN_COMPILER_ORIGIN").isNone do throwError "stock origin environment leaked"
  let child ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
  unless child.exitCode == 0 && child.stdout.trimAscii.toString == sysroot do
    throwError "stock child compiler escaped its toolchain"
inductive Stock where | mk ''' + fields + '\n')
            self.build()
            path = self.root / 'fixture-mathlib/.lake/build/lib/lean/Stock.trace'
            trace = json.loads(path.read_text())
            compiler = [row for row in trace['inputs'] if row[0].startswith('Lean ')]
            self.assertEqual([row[0] for row in compiler],
                ['Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17'])
            self.assertNotIn('compiler origin:', json.dumps(trace['inputs']))
            traces.append(trace['depHash'])
            self.run_lake('env', str(self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'),
                '--output', 'stock.json', '--material-spool', 'stock-materials',
                'Stock', 'fixture-mathlib/Stock.lean',
                'sha256:' + publication.digest(self.root / 'fixture-mathlib/Stock.lean'))
            rows = json.loads((self.root / 'stock.json').read_text())['modules']
            for name in ('Stock.mk.inj', 'Stock.mk.injEq', 'Stock.mk.sizeOf_spec'):
                declaration = next(d for d in rows[0]['declarations'] if d['name'] == name)
                self.assertFalse(declaration['generated_companion'], name)
                self.assertTrue(declaration['include_in_statement'], name)
            shutil.rmtree(self.root / 'stock-materials')
        self.assertNotEqual(*traces)
        self.record_result('verified', dict(checks=checks, source_mutation_invalidated=True,
            stock_cache_misses=2, stock_companions_remain_selected=3, owned_live_processes=0))

    def test_compiler_origin_imports_and_invalidation(self):
        checks = self.measure_origin_commands()
        # A fetched package is really compiled by the stock producer before
        # the instrumented build. Its cache and unknown-origin classification
        # must survive both initial admission and a compiler recipe change.
        self.write('fixture-mathlib/lakefile.toml', 'name = "mathlib"\n[[lean_lib]]\nname = "Stock"\n')
        self.write('fixture-mathlib/Stock.lean', 'inductive Stock where | mk (n : Nat)\n')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['dependency_sources']['include'].append(dict(pattern='fixture-mathlib/Stock.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        stock_build = self.guarded_command([self.lake, 'build', 'Stock'], env=self.env)
        self.assertEqual(stock_build.returncode, 0, stock_build.stdout + stock_build.stderr)
        stock_paths = list((self.root / 'fixture-mathlib/.lake/build/lib/lean').glob('Stock.*'))
        self.assertTrue(stock_paths)
        stock_inputs = {path: (publication.digest(path), path.stat().st_mtime_ns) for path in stock_paths}
        # Compiler companion metadata survives even when the content imports
        # no Lean producer API. Query imports belong to the report environment.
        self.write('D5/MinimalOrigin.lean', '''inductive Minimal where
  | mk (n : Nat)
def visited : Nat → Nat | 0 => 0 | n + 1 => visited n + 1
def visitedWitness := @visited.eq_def
''')
        self.write('D5/Origin.lean', '''import Lean
import Stock
open Lean Elab Command
inductive Ranged where
  | mk (n : Nat)
run_elab addDeclarationRanges `Ranged.mk.inj default
def simple (n : Nat) := n + 1
def simpleWitness := @simple.eq_def
def wf (n : Nat) : Nat := if n = 0 then 0 else wf (n - 1) + 1
termination_by n
decreasing_by omega
def wfWitness := @wf.eq_def
def loop (n : Nat) : Option Nat := if n == 0 then some 0 else loop (n + 1)
partial_fixpoint
def loopWitness := @loop.eq_def
private theorem privateAuthored : True := True.intro
''')
        self.write('D5/Via.lean', 'import D5.Origin\n')
        self.write('OriginNative.lean', '''import Lean
import Lean.CompanionOrigin
open Lean
unsafe def produced (env : Environment) : IO NameSet := do
  let mut names : NameSet := {}
  for (owner, query) in #[
      (`Lean.Meta.Injective, `Lean.Meta.compilerGeneratedCompanionNamesInjective),
      (`Lean.Meta.SizeOf, `Lean.Meta.compilerGeneratedCompanionNamesSizeOf),
      (`Lean.Meta.Eqns, `Lean.Meta.compilerGeneratedCompanionNamesEqns),
      (`Lean.Elab.PreDefinition.Structural.Eqns, `Lean.Elab.Structural.compilerGeneratedCompanionNamesStructuralEqns),
      (`Lean.Elab.PreDefinition.WF.Unfold, `Lean.Elab.WF.compilerGeneratedCompanionNamesWFUnfold),
      (`Lean.Elab.PreDefinition.WF.Eqns, `Lean.Elab.WF.compilerGeneratedCompanionNamesWFEqns),
      (`Lean.Elab.PreDefinition.PartialFixpoint.Eqns, `Lean.Elab.PartialFixpoint.compilerGeneratedCompanionNamesPartialFixpointEqns),
      (`Lean.Meta.CongrTheorems, `Lean.Meta.compilerGeneratedCompanionNamesCongrTheorems)] do
    let some index := env.getModuleIdxFor? query
      | throw <| IO.userError s!"missing producer query: {query}"
    unless env.header.moduleNames[index.toNat]! == owner do
      throw <| IO.userError s!"misowned producer query: {query}"
    let driver ← IO.ofExcept <| env.evalConstCheck (Environment → Array Name) {}
      `Lean.CompilerGeneratedCompanionDriver query
    for name in driver env do names := names.insert name
  return names
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let direct ← importModules #[{module := `D5.Origin}] {} (loadExts := true) (leakEnv := true)
  enableInitializersExecution
  let transitive ← importModules #[{module := `D5.Via}] {} (loadExts := true) (leakEnv := true)
  let directNames ← produced direct
  let transitiveNames ← produced transitive
  for name in [`Stock.mk.inj, `Stock.mk.injEq, `Stock.mk.sizeOf_spec] do
    if directNames.contains name || transitiveNames.contains name then
      throw <| IO.userError s!"stock cache acquired compiler origin: {name}"
  for name in [`Ranged.mk.inj, `Ranged.mk.injEq, `Ranged.mk.sizeOf_spec,
      `simple.eq_def, `wf.eq_def, `loop.eq_def] do
    unless directNames.contains name && transitiveNames.contains name do
      throw <| IO.userError s!"lost imported origin: {name}"
  let some (.thmInfo theoremValue) := direct.find? `Ranged.mk.inj
    | throw <| IO.userError "missing imported theorem"
  let record : CompilerProducedTheorem := { owner := `D5.Origin, theoremValue }
  unless record.matches direct && record.matches transitive do
    throw <| IO.userError "exact imported record rejected"
  for bad in #[{ record with owner := `D5.Via },
      { record with theoremValue := { theoremValue with name := `Missing } },
      { record with theoremValue := { theoremValue with levelParams := [`u] } },
      { record with theoremValue := { theoremValue with type := mkConst ``False } },
      { record with theoremValue := { theoremValue with value := mkConst ``True.intro } }] do
    if bad.matches direct || bad.matches transitive then
      throw <| IO.userError "mismatched imported record accepted"
  enableInitializersExecution
  let some env ← Elab.runFrontend "import Lean\\ninductive GeneratedNative where | mk (n : Nat)"
    {} "Native.lean" `Native
    | throw <| IO.userError "native runFrontend failed"
  unless (← produced env).contains `GeneratedNative.mk.inj do
    throw <| IO.userError "native archive did not retain generator instrumentation"
''')
        with (self.root / 'lakefile.toml').open('a') as config:
            config.write('\n[[lean_exe]]\nname = "originNative"\nroot = "OriginNative"\nsupportInterpreter = true\n'
                'needs = ["leanInspector/compilerInput"]\nmoreLinkObjs = ["leanInspector/compilerArchive"]\n')
        self.build()
        self.assertEqual(stock_inputs,
            {path: (publication.digest(path), path.stat().st_mtime_ns) for path in stock_paths})
        self.run_lake('build', 'originNative')
        self.run_lake('env', str(self.root / '.lake/build/bin/originNative'))
        # Source/olean instrumentation alone does not replace the compiler
        # generators linked into a native frontend. Link the same consumer
        # against the untouched archive plus only the provenance registry.
        compiler = self.root / 'build/compiler-origin' / self.origins()['D5.Origin']['compiler_input_sha256']
        driver = json.loads((compiler / 'driver.json').read_text())
        compiled = self.guarded_command([str(compiler / 'bin/lean'),
            '-c', 'OriginNative.c', 'OriginNative.lean'], env=dict(self.env,
                LEAN_SYSROOT=str(compiler), LEAN_PATH=str(compiler / 'lib/lean')))
        self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
        source_only = self.root / 'source-only-native'
        linked = self.guarded_command([driver['leanc'],
            '-Wl,-export_dynamic' if sys.platform == 'darwin' else '-Wl,--export-dynamic',
            '-o', str(source_only), 'OriginNative.c', str(compiler / 'lib/lean/Lean/CompanionOrigin.o')],
            env=dict(self.env, LEAN_SYSROOT=driver['base']))
        self.assertEqual(linked.returncode, 0, linked.stdout + linked.stderr)
        control = self.run_lake('env', str(source_only), success=False)
        # The private producer extension has its own native initializer. A
        # stock archive cannot load it from the patched olean alone; runtimes
        # which load it dynamically still lack the generator insertion hook.
        diagnostic = control.stdout + control.stderr
        self.assertTrue(any(expected in diagnostic for expected in (
            "cannot evaluate `[init]` declaration '_private.Lean.Meta.Injective.0.Lean.Meta.compilerProducedTheoremsInjective'",
            'native archive did not retain generator instrumentation')), diagnostic)
        rows = self.report()[0]
        # Inspect this module alone: importing Origin would otherwise load
        # Lean and conceal a missing report-owned query closure.
        self.run_lake('env', str(self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'),
            '--output', 'minimal.json', '--material-spool', 'minimal-materials',
            'D5.MinimalOrigin', 'D5/MinimalOrigin.lean',
            'sha256:' + publication.digest(self.root / 'D5/MinimalOrigin.lean'))
        minimal = json.loads((self.root / 'minimal.json').read_text())['modules'][0]
        for name in ['Minimal.mk.inj', 'Minimal.mk.injEq', 'Minimal.mk.sizeOf_spec', 'visited.eq_def']:
            self.assertTrue(next(d for d in minimal['declarations'] if d['name'] == name)['generated_companion'], name)
        origin_row = next(r for r in rows if r['module'] == 'D5.Origin')
        declarations = {d['name']: d for d in origin_row['declarations']}
        self.assertFalse(declarations['Ranged.mk.inj']['generated_companion'])
        for name in ['Ranged.mk.injEq', 'Ranged.mk.sizeOf_spec', 'simple.eq_def', 'wf.eq_def', 'loop.eq_def']:
            self.assertTrue(declarations[name]['generated_companion'], name)
        private = [d for n, d in declarations.items() if n.endswith('.privateAuthored')]
        self.assertEqual(len(private), 1)
        self.assertFalse(private[0]['generated_companion'])
        before = self.origins()
        recipe = self.root / 'tools/lean-inspector/compiler/CompanionOrigin.lean'
        recipe.write_text(recipe.read_text() + '\n-- compiler-input invalidation control\n')
        self.build()
        after = self.origins()
        self.assertEqual(stock_inputs,
            {path: (publication.digest(path), path.stat().st_mtime_ns) for path in stock_paths})
        self.run_lake('build', 'originNative')
        self.run_lake('env', str(self.root / '.lake/build/bin/originNative'))
        self.assertNotEqual(before['D5.Origin']['compiler_input_sha256'], after['D5.Origin']['compiler_input_sha256'])
        self.assertEqual([(r['module'], [(d['name'], d['statement_id'], d['axioms']) for d in r['declarations']]) for r in rows],
            [(r['module'], [(d['name'], d['statement_id'], d['axioms']) for d in r['declarations']]) for r in self.report()[0]])
        self.record_result('verified', dict(exit=0, query_apis=8, imported_companions=6,
            exact_record_mismatches=5, explicit_source_veto='Ranged.mk.inj',
            stock_archive_control_exit=control.returncode,
            stock_archive_control_diagnostic=diagnostic.strip(),
            compiler_before=before['D5.Origin']['compiler_input_sha256'],
            compiler_after=after['D5.Origin']['compiler_input_sha256'],
            recipe_invalidation=True, identities_and_axioms_unchanged=True,
            stock_cache_files=len(stock_paths), stock_cache_unchanged=True,
            stock_companions_remain_unknown=True,
            minimal_import_companions=4,
            checks=checks, owned_live_processes=0))

    def test_compiler_origin_report_binding_recovery(self):
        checks = self.measure_origin_commands()
        self.write('D5/BindingOrigin.lean', 'inductive BoundOrigin where | mk (n : Nat)\n')
        self.build()
        rows = self.report()[0]
        declarations = next(r for r in rows if r['module'] == 'D5.BindingOrigin')['declarations']
        self.assertTrue(next(d for d in declarations if d['name'] == 'BoundOrigin.mk.inj')['generated_companion'])
        before = self.origins()
        # Legacy and stale compiler evidence must fail at the real publisher,
        # then re-enter the canonical report facet without guessed provenance.
        for damage in ('missing', 'stale'):
            artifacts = [*self.root.glob('.lake/build/lean-inspector/modules/*.zip'),
                         self.root / '.lake/build/lean-inspector/report.zip']
            for artifact in artifacts:
                with zipfile.ZipFile(artifact) as archive:
                    entries = [(info, archive.read(info)) for info in archive.infolist()]
                artifact.unlink()  # Do not mutate a linked Lake cache artifact.
                with zipfile.ZipFile(artifact, 'w') as archive:
                    for info, data in entries:
                        if info.filename.endswith('.provenance.json'):
                            origin = json.loads(data)
                            records = origin['module_origins'].values() if 'module_origins' in origin else [origin]
                            for record in records:
                                if damage == 'missing':
                                    record.pop('compiler_input_sha256')
                                else:
                                    record['compiler_input_sha256'] = '0' * 64
                            data = json.dumps(origin).encode()
                        archive.writestr(info, data)
            rejected = self.root / ('rejected-' + damage + '.json')
            result = self.guarded_command([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
                'publish', str(self.root), str(rejected)], env=self.env, capture_output=True, timeout=120)
            self.assertNotEqual(result.returncode, 0, damage)
            self.assertFalse(rejected.exists(), damage)
            self.build()
            self.assertEqual(before, self.origins(), damage)
            self.assertEqual(rows, self.report()[0], damage)
        self.record_result('verified', dict(missing_and_stale_provenance_rejected=True,
            generated_companions_and_rows_preserved=True, checks=checks, owned_live_processes=0))

    def test_compiler_origin_output_and_receipt_recovery(self):
        checks = self.measure_origin_commands()
        self.build()
        before = self.origins()
        report_before = self.report()
        selected = next(p for p in (self.root / 'build/compiler-origin').iterdir()
            if p.name == before['Fixture']['compiler_input_sha256'])
        registry = selected / 'lib/lean/Lean/CompanionOrigin.olean'
        expected = publication.digest(registry)
        registry.write_bytes(b'corrupt compiler output')
        self.build()
        self.assertEqual(publication.digest(registry), expected)
        self.assertEqual(self.report(), report_before)
        self.assertEqual(self.origins(), before)
        # Optional compiler receipts have the same recovery contract as outputs.
        # Exercise the canonical entry after a valid build, including its lock.
        origins_before = before
        receipt = selected / 'artifacts.json'
        receipt_before = receipt.read_bytes()
        # Root can read mode-000 files; only claim the permission-denied
        # injection on hosts where that filesystem failure is enforceable.
        damages = ('truncated', 'unreadable') if os.geteuid() != 0 else ('truncated',)
        for damage in damages:
            with self.subTest(receipt=damage):
                if damage == 'truncated':
                    receipt.write_bytes(b'{"truncated":')
                else:
                    receipt.chmod(0)
                    with self.assertRaises(PermissionError):
                        receipt.read_bytes()
                self.build()
                self.assertEqual(receipt.read_bytes(), receipt_before)
                self.assertFalse(receipt.with_suffix('.json.tmp').exists())
                self.assertEqual(self.report(), report_before)
                self.assertEqual(self.origins(), origins_before)
        self.record_result('verified', dict(corruption_recovered=True,
            receipt_controls=damages, identities_and_axioms_unchanged=True,
            compiler=before['Fixture']['compiler_input_sha256'], checks=checks))
