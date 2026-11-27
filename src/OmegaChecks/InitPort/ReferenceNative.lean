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
private def world := `Omega.Void.mk
private def entries := #[(world, "lean_void_mk"), (allocation, "omega_st_mk_ref"), (`Omega.ST.Prim.Ref.swap, "omega_st_ref_swap"),
  (`Omega.ST.Prim.Ref.set, "omega_st_ref_set"), (`Omega.ST.Prim.Ref.ptrEq, "omega_st_ref_ptr_eq")]
private def operations := #[`Omega.ST.pure, `Omega.ST.bind, `Omega.EST.pure, `Omega.EST.bind,
  `Omega.EST.throw, `Omega.EST.tryCatch, `Omega.runST, `Omega.runEST]

private def lifted := #[`Omega.ST.mkRef, `Omega.ST.Ref.swap, `Omega.ST.Ref.set, `Omega.ST.Ref.ptrEq]

public unsafe def install (lib output : System.FilePath) (interpreter : Bool) : IO Unit := do
  let original ← importModules #[{module := `Init.System.ST}] {}
  verify original `Void.mk #[(.erased, false), (.tobject, false)] .void "lean_void_mk"
  verify original `ST.Prim.mkRef #[(.erased, false), (.erased, false), (.tobject, false), (.void, false)]
    .tobject "lean_st_mk_ref"
  verify original `ST.Prim.Ref.swap #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, false), (.void, false)]
    .tobject "lean_st_ref_swap"
  verify original `ST.Prim.Ref.ptrEq #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, true), (.void, false)]
    .uint8 "lean_st_ref_ptr_eq"
  searchPathRef.set [lib]
  let imports := #[{module := owner, importAll := true : Import}]
  let env ← importModules imports {}
  let externs := entries.filter fun (n, _) => env.contains n && (!interpreter || n == world)
  if externs.isEmpty && !(operations.any env.contains) then return
  if !interpreter then
    if env.contains `Omega.ST.Out then installStateLayout lib env
    for n in [`Omega.EST.Out, `Omega.Except] do
      if env.contains n && (monoTypeExt.find? env n).isNone then
        let idx := (env.getModuleIdxFor? n).get!
        writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  let ref? := if interpreter then none else env.find? `Omega.ST.Ref
  let refNames := if let some (.inductInfo ref) := ref? then #[ref.name] ++ ref.ctors.toArray else #[]
  let wrappers := if interpreter then #[] else (operations ++ lifted).filter env.contains
  -- The four pinned matchers lower the ST/EST return and exception cases.
  let matchers := #[`Omega.ST.bind.match_1, `Omega.EST.bind.match_1, `Omega.runST.match_1, `Omega.runEST.match_1]
    |>.map (mkPrivateNameCore owner) |>.filter fun n =>
      wrappers.any fun w => ((env.find? w).bind (·.value?)).any (fun e => e.getUsedConstants.contains n)
  let names := externs.map Prod.fst ++ matchers ++ wrappers
  let ctx ← localEnv env owner (refNames ++ names)
  let compiled ← compile ctx do
    if let some (.inductInfo ref) := ref? then (← compileDeclsRef.get) #[ref.name] {}
    for (n, symbol) in externs do
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
    for n in matchers ++ wrappers do
      modifyEnv fun e => Lean.privateConstKindsExt.insert e n .defn
      (← compileDeclsRef.get) #[n] {}
  if let some (.inductInfo ref) := ref? then
    let some (some layout) := impureTrivialStructureInfoExt.find? compiled ref.name
      | throw <| IO.userError "expected an unboxed reference handle"
    unless layout.numParams == 2 && layout.fieldIdx == 0 && ref.ctors == [layout.ctorName] do
      throw <| IO.userError "unexpected strict reference layout"
  let implicitArgs := #[(IR.IRType.erased, false), (.erased, false)]
  for (n, symbol) in externs do
    if n == world then
      verify compiled n #[(.erased, false), (.tobject, false)] .tobject symbol
      continue
    let parameters := if n == allocation then #[(.tobject, false)]
      else if n == `Omega.ST.Prim.Ref.ptrEq then #[(.tobject, true), (.tobject, true)]
      else #[(.tobject, n == `Omega.ST.Prim.Ref.swap), (.tobject, false)]
    verify compiled n (implicitArgs ++ parameters ++ #[(.tobject, false)]) .object symbol
  if interpreter then
    emitBridge compiled `StrictVoidInterpreter none output
  else
    writeCode lib owner compiled (layouts ++ codeExtensions ++ #[Lean.privateConstKindsExt.name])
    emitBridge compiled owner "src/OmegaChecks/InitPort/reference_runtime.c" output

end ReferenceNative

public unsafe def main (args : List String) : IO Unit := do
  let (interpreter, args) := if args.head? == some "--interpreter" then (true, args.drop 1) else (false, args)
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  ReferenceNative.install lib output interpreter
