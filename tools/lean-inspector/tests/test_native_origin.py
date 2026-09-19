"""Compiler provenance through native links, imports and the actual report facet."""
from test_native_support import *


class NativeOriginTests:
    def test_compiler_origin_imports_and_invalidation(self):
        self.write('D5/Origin.lean', '''import Lean
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
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let direct ← importModules #[{module := `D5.Origin}] {} (loadExts := true) (leakEnv := true)
  enableInitializersExecution
  let transitive ← importModules #[{module := `D5.Via}] {} (loadExts := true) (leakEnv := true)
  for name in [`Ranged.mk.inj, `Ranged.mk.injEq, `Ranged.mk.sizeOf_spec,
      `simple.eq_def, `wf.eq_def, `loop.eq_def] do
    let origin := companionOrigin? direct name
    unless origin.isSome && origin == companionOrigin? transitive name do
      throw <| IO.userError s!"lost imported origin: {name}"
  enableInitializersExecution
  let some env ← Elab.runFrontend "inductive GeneratedNative where | mk (n : Nat)"
    {} "Native.lean" `Native
    | throw <| IO.userError "native runFrontend failed"
  unless (companionOrigin? env `GeneratedNative.mk.inj).isSome do
    throw <| IO.userError "native archive did not retain generator instrumentation"
''')
        with (self.root / 'lakefile.toml').open('a') as config:
            config.write('\n[[lean_exe]]\nname = "originNative"\nroot = "OriginNative"\nsupportInterpreter = true\n')
        self.build()
        self.run_lake('build', 'originNative')
        self.run_lake('env', str(self.root / '.lake/build/bin/originNative'))
        rows = self.report()[0]
        origin_row = next(r for r in rows if r['module'] == 'D5.Origin')
        declarations = {d['name']: d for d in origin_row['declarations']}
        self.assertFalse(declarations['Ranged.mk.inj']['generated_companion'])
        for name in ['Ranged.mk.injEq', 'Ranged.mk.sizeOf_spec', 'simple.eq_def', 'wf.eq_def', 'loop.eq_def']:
            self.assertTrue(declarations[name]['generated_companion'], name)
        private = [d for n, d in declarations.items() if n.endswith('.privateAuthored')]
        self.assertEqual(len(private), 1)
        self.assertFalse(private[0]['generated_companion'])
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
            result = subprocess.run([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
                'publish', str(self.root), str(rejected)], env=self.env, capture_output=True, timeout=120)
            self.assertNotEqual(result.returncode, 0, damage)
            self.assertFalse(rejected.exists(), damage)
            self.build()
            self.assertEqual(before, self.origins(), damage)
            self.assertEqual(rows, self.report()[0], damage)
        recipe = self.root / 'tools/lean-inspector/compiler/CompanionOrigin.lean'
        recipe.write_text(recipe.read_text() + '\n-- compiler-input invalidation control\n')
        self.build()
        after = self.origins()
        self.assertNotEqual(before['D5.Origin']['compiler_input_sha256'], after['D5.Origin']['compiler_input_sha256'])
        self.assertEqual([(r['module'], [(d['name'], d['statement_id']) for d in r['declarations']]) for r in rows],
            [(r['module'], [(d['name'], d['statement_id']) for d in r['declarations']]) for r in self.report()[0]])
        selected = next(p for p in (self.root / 'build/compiler-origin').iterdir()
            if p.name == after['D5.Origin']['compiler_input_sha256'])
        registry = selected / 'lib/lean/Lean/CompanionOrigin.olean'
        expected = publication.digest(registry)
        registry.write_bytes(b'corrupt compiler output')
        self.build()
        self.assertEqual(publication.digest(registry), expected)
