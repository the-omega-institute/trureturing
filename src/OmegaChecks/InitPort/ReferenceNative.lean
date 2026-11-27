module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import all Lean.OriginalConstKind
import all Lean.Environment
import Lean
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

open OmegaChecks.InitPort.NativeState

namespace ReferenceNative

private def owner := `OmegaInit.System.ST
private def allocation := `Omega.ST.Prim.mkRef
private def entries := #[(allocation, "omega_st_mk_ref"), (`Omega.ST.Prim.Ref.swap, "omega_st_ref_swap"),
  (`Omega.ST.Prim.Ref.set, "omega_st_ref_set"), (`Omega.ST.Prim.Ref.ptrEq, "omega_st_ref_ptr_eq")]
private def lifted := #[`Omega.ST.mkRef, `Omega.ST.Ref.swap, `Omega.ST.Ref.set, `Omega.ST.Ref.ptrEq]

public unsafe def install (lib output : System.FilePath) : IO Unit := do
  let original ← importModules #[{module := `Init.System.ST}] {}
  verify original `ST.Prim.mkRef #[(.erased, false), (.erased, false), (.tobject, false), (.void, false)]
    .tobject "lean_st_mk_ref"
  verify original `ST.Prim.Ref.swap #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, false), (.void, false)]
    .tobject "lean_st_ref_swap"
  verify original `ST.Prim.Ref.ptrEq #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, true), (.void, false)]
    .uint8 "lean_st_ref_ptr_eq"
  searchPathRef.set [lib]
  let imports := #[{module := owner : Import}]
  let env ← importModules imports {}
  unless entries.any (fun e => env.contains e.1) do return
  installStateLayout lib env
  let env ← importModules imports {}
  let some (.inductInfo ref) := env.find? `Omega.ST.Ref | throw <| IO.userError "missing reference type"
  let names := ((entries.map Prod.fst) ++ lifted).filter env.contains
  let contextEnv ← localEnv env owner (#[ref.name] ++ ref.ctors.toArray ++ names)
  let compiled ← compile contextEnv do
    (← compileDeclsRef.get) #[ref.name] {}
    for (n, symbol) in entries do
      if names.contains n then
        modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
        (← compileDeclsRef.get) #[n] {}
    for n in lifted do
      if names.contains n then
        modifyEnv fun e => Lean.privateConstKindsExt.insert e n .defn
        (← compileDeclsRef.get) #[n] {}
  let some (some layout) := impureTrivialStructureInfoExt.find? compiled ref.name
    | throw <| IO.userError "expected an unboxed reference handle"
  unless layout.numParams == 2 && layout.fieldIdx == 0 && ref.ctors == [layout.ctorName] do
    throw <| IO.userError "unexpected strict reference layout"
  let implicitArgs := #[(IR.IRType.erased, false), (.erased, false)]
  for (n, symbol) in entries do
    unless names.contains n do continue
    let parameters := if n == allocation then #[(.tobject, false)]
      else if n == `Omega.ST.Prim.Ref.ptrEq then #[(.tobject, true), (.tobject, true)]
      else #[(.tobject, n == `Omega.ST.Prim.Ref.swap), (.tobject, false)]
    verify compiled n (implicitArgs ++ parameters ++ #[(.tobject, false)]) .object symbol
  writeCode lib owner compiled (layouts ++ codeExtensions ++ #[Lean.privateConstKindsExt.name])
  emitBridge compiled owner "src/OmegaChecks/InitPort/reference_runtime.c" output

end ReferenceNative

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  ReferenceNative.install lib output
