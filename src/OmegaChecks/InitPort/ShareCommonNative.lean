module
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.EmitC
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.LogicalHandle
meta import OmegaChecks.InitPort.LogicalHandle

open Lean OmegaChecks.InitPort

/-- Bind the opaque state allocator to its pinned implementation and keep the same sharing operation. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let api := LogicalHandle.shareState
  let official ← importModules #[{module := api.owner}] {}
  let some impl := Compiler.getImplementedBy? official api.allocator | throw <| IO.userError "missing state allocator implementation"
  let some (.fdecl _ args .tobject _ _) := IR.findEnvDecl official impl | throw <| IO.userError "missing native state allocator"
  unless impl == `ShareCommon.mkStateImpl && args.map (fun a => (a.ty, a.borrow)) == #[(.tobject, false)] &&
      impl.mangle (pre := "l_") == api.nativeAllocator do
    throw <| IO.userError "unexpected native state allocator ABI"
  let share := `ShareCommon.State.shareCommon
  let shareSymbol := "lean_state_sharecommon"
  let shareArgs := #[(IR.IRType.erased, false), (.tobject, true), (.tobject, false), (.tobject, false)]
  NativeState.verify official share shareArgs .object shareSymbol
  searchPathRef.set [lib]
  let env ← importModules #[{module := api.privateOwner, importAll := true}] {}
  let roots := [(api.allocator, api.nativeAllocator), (share, shareSymbol)].filter fun (n, _) => env.contains (`Omega ++ n)
  if roots.isEmpty then return
  let wrappers := [`ShareCommon.instInhabitedState, `ShareCommonT.run, `ShareCommonM.run].map (`Omega ++ ·)
  let wrappers := wrappers.filter env.contains
  let names := roots.map (fun (n, _) => `Omega ++ n) ++ wrappers
  let ctx ← NativeState.localEnv env api.privateOwner names.toArray
  let compiled ← NativeState.compile ctx do
    for (n, symbol) in roots do
      let strict := `Omega ++ n
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := strict) e (strict, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[strict] {}
    for strict in wrappers do
      modifyEnv fun e => privateConstKindsExt.insert e strict .defn
      (← compileDeclsRef.get) #[strict] {}
  for (n, symbol) in roots do
    if n == api.allocator then
      NativeState.verify compiled (`Omega ++ n) #[(.tobject, false)] .tobject symbol
    else
      NativeState.verify compiled (`Omega ++ n) shareArgs .object symbol
  NativeState.writeCode lib api.privateOwner compiled (NativeState.codeExtensions ++ #[privateConstKindsExt.name])
  NativeState.emitBridge compiled api.privateOwner none output #[{module := `OmegaInit.Control.State}]
