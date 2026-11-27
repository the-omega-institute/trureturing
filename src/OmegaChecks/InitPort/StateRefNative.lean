module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.StateRunner
import OmegaChecks.InitPort.StateRunner
import all Lean.OriginalConstKind
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType
import Lean

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

/-- Compile the transformer setter and the private state read used by its runners. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let original ← importModules #[{module := `Init.System.ST}] {}
  searchPathRef.set [lib]
  let owner := `OmegaInit.Control.StateRef
  let setter := `Omega.StateRefT'.set
  let read := InitKernelPort.portName OmegaChecks.InitPort.StateRunner.support
  let env ← importModules #[{module := owner, importAll := true}] {}
  let names := #[setter, read].filter env.contains
  if names.isEmpty then return
  let context ← localEnv env owner names
  let compiled ← compile context do
    if names.contains read then
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := read) e (read, ⟨[.standard `all "omega_state_ref_read_with_initial"]⟩)
      (← compileDeclsRef.get) #[read] {}
    if names.contains setter then
      modifyEnv fun e => Lean.privateConstKindsExt.insert e setter .defn
      (← compileDeclsRef.get) #[setter] {}
  if names.contains read then
    verify original `ST.Prim.Ref.get #[(.erased, false), (.erased, false), (.tobject, true), (.void, false)]
      .tobject "lean_st_ref_get"
    verify compiled read #[(.erased, false), (.erased, false), (.tobject, false), (.tobject, true), (.tobject, false)]
      .object "omega_state_ref_read_with_initial"
    let some (some ref) := impureTrivialStructureInfoExt.find? env `Omega.ST.Ref
      | throw <| IO.userError "missing strict reference representation"
    unless ref.numParams == 2 && ref.fieldIdx == 0 do throw <| IO.userError "unexpected strict reference layout"
    let some pair := ctorLayoutExt.find? env `Omega.ST.Out.mk | throw <| IO.userError "missing strict ST.Out"
    let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "incorrect strict ST.Out fields"
    unless pair.ctorInfo.cidx == 0 && pair.ctorInfo.size == 2 && pair.ctorInfo.usize == 0 && pair.ctorInfo.ssize == 0 do
      throw <| IO.userError "incorrect strict ST.Out layout"
  writeCode lib owner compiled (codeExtensions ++ #[Lean.privateConstKindsExt.name])
  emitBridge compiled owner none output
