module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.ReferenceModify
import OmegaChecks.InitPort.ReferenceModify
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
private def elim := `Omega.EST.Out.ctorElim
private def readForModify := InitKernelPort.portName OmegaChecks.InitPort.ReferenceModify.support
private def modify := `Omega.ST.Prim.Ref.modify
private def entries := #[(world, "lean_void_mk"), (elim, "omega_est_out_elim"), (allocation, "omega_st_mk_ref"), (`Omega.ST.Prim.Ref.swap, "omega_st_ref_swap"),
  (`Omega.ST.Prim.Ref.put, "omega_st_ref_put"),
  (modify, "omega_st_ref_modify"), (readForModify, "omega_st_ref_read_for_modify"),
  (`Omega.ST.Prim.Ref.set, "omega_st_ref_set"), (`Omega.ST.Prim.Ref.ptrEq, "omega_st_ref_ptr_eq")]
private def operations := #[`Omega.ST.pure, `Omega.ST.bind, `Omega.EST.pure, `Omega.EST.bind,
  `Omega.EST.throw, `Omega.EST.tryCatch, `Omega.runST, `Omega.runEST,
  `Omega.Void.nonemptyType, `Omega.ST.RefPointed, `Omega.EST.Out.ctorIdx, `Omega.EST.Out.ok.elim,
  `Omega.EST.Out.error.elim, `Omega.instMonadST, `Omega.instMonadEST, `Omega.instMonadExceptOfEST,
  `Omega.instInhabitedST, `Omega.instInhabitedEST, `Omega.instSTWorldST, `Omega.instSTWorldEST,
  `Omega.instSTWorldOfMonadLift, `Omega.instMonadFinallyST, `Omega.instMonadFinallyEST,
  `Omega.instMonadAttachST, `Omega.instMonadAttachEST, `Omega.instMonadLiftSTEST]

private def referenceWrappers := #[`Omega.ST.Prim.Ref.modifyUnsafe, `Omega.ST.mkRef, `Omega.ST.Ref.put, `Omega.ST.Ref.swap, `Omega.ST.Ref.set, `Omega.ST.Ref.modify, `Omega.ST.Ref.ptrEq]

public unsafe def install (lib output : System.FilePath) (interpreter : Bool) : IO Unit := do
  let original ← importModules #[{module := `Init.System.ST}] {}
  verify original `Void.mk #[(.erased, false), (.tobject, false)] .void "lean_void_mk"
  verify original `ST.Prim.mkRef #[(.erased, false), (.erased, false), (.tobject, false), (.void, false)]
    .tobject "lean_st_mk_ref"
  verify original `ST.Prim.Ref.swap #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, false), (.void, false)]
    .tobject "lean_st_ref_swap"
  verify original `ST.Prim.Ref.put #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, false), (.void, false)]
    .tagged "lean_st_ref_put"
  verify original `ST.Prim.Ref.ptrEq #[(.erased, false), (.erased, false), (.tobject, true), (.tobject, true), (.void, false)]
    .uint8 "lean_st_ref_ptr_eq"
  searchPathRef.set [lib]
  let imports := #[{module := owner, importAll := true : Import}]
  let env ← importModules imports {}
  let externs := entries.filter fun (n, _) => env.contains n && (!interpreter || n == world || n == elim)
  if externs.isEmpty && !(operations.any env.contains) then return
  if !interpreter then
    if env.contains `Omega.ST.Out then installStateLayout lib env
    for n in [`Omega.EST.Out, `Omega.Except, `Omega.Option, `Omega.STWorld, `Omega.MonadFinally, `Omega.MonadAttach,
        `Omega.MonadExceptOf, `Omega.Monad, `Omega.MonadLift, `PULift] do
      if env.contains n && (monoTypeExt.find? env n).isNone then
        let idx := (env.getModuleIdxFor? n).get!
        writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  let ref? := if interpreter then none else env.find? `Omega.ST.Ref
  let refNames := if let some (.inductInfo ref) := ref? then #[ref.name] ++ ref.ctors.toArray else #[]
  let wrappers := if interpreter then #[] else (operations ++ referenceWrappers).filter env.contains
  -- Some translated matchers have a private lexical name, while others are public.
  let matchers := wrappers.foldl (init := #[]) fun ns w => Id.run do
    let some value := (env.find? w).bind (·.value?) | return ns
    let mut ns := ns
    for n in value.getUsedConstants do
      let .str _ suffix := privateToUserName? n |>.getD n | continue
      if suffix.startsWith "match_" && env.getModuleIdxFor? n == env.getModuleIdx? owner && !ns.contains n then
        ns := ns.push n
    return ns
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
  for n in wrappers do
    unless (IR.findEnvDecl compiled n).isSome do throw <| IO.userError s!"missing strict executable {n}"
  if externs.any (·.1 == elim) then
    for (n, tag) in [(`Omega.EST.Out.ok, 0), (`Omega.EST.Out.error, 1)] do
      let some layout := ctorLayoutExt.find? compiled n | throw <| IO.userError s!"missing constructor layout for {n}"
      let #[.object 0 _, .object 1 _] := layout.fieldInfo | throw <| IO.userError s!"invalid field order for {n}"
      unless layout.ctorInfo.cidx == tag && layout.ctorInfo.size == 2 && layout.ctorInfo.usize == 0 &&
          layout.ctorInfo.ssize == 0 do throw <| IO.userError s!"incorrect strict fields for {n}"
    let some (some info) := impureTrivialStructureInfoExt.find? compiled `PULift
      | throw <| IO.userError "expected an unboxed EST eliminator continuation"
    unless info.ctorName == `PULift.up && info.fieldIdx == 0 do throw <| IO.userError "incorrect continuation layout"
  if externs.any (·.1 == modify) then
    verify original `ST.Prim.Ref.take #[(.erased, false), (.erased, false), (.tobject, true), (.void, false)]
      .tobject "lean_st_ref_take"
    verify original `ST.Prim.Ref.get #[(.erased, false), (.erased, false), (.tobject, true), (.void, false)]
      .tobject "lean_st_ref_get"
    let some opt := ctorLayoutExt.find? compiled `Omega.Option.some | throw <| IO.userError "missing Option.some layout"
    let #[.object 0 _] := opt.fieldInfo | throw <| IO.userError "invalid Option.some field"
    unless opt.ctorInfo.cidx == 1 && opt.ctorInfo.size == 1 && opt.ctorInfo.usize == 0 && opt.ctorInfo.ssize == 0 do
      throw <| IO.userError "incorrect strict optional reference read layout"
  let implicitArgs := #[(IR.IRType.erased, false), (.erased, false)]
  for (n, symbol) in externs do
    if n == elim then
      verify compiled n (Array.replicate 4 (.erased, false) ++ #[(.tobject, false), (.object, false),
        (.erased, false), (.tobject, false)]) .tobject symbol
      continue
    if n == world then
      verify compiled n #[(.erased, false), (.tobject, false)] .tobject symbol
      continue
    let parameters := if n == readForModify then #[(.tobject, true)]
      else if n == modify then #[(.tobject, false), (.tobject, false)]
      else if n == allocation then #[(.tobject, false)]
      else if n == `Omega.ST.Prim.Ref.ptrEq then #[(.tobject, true), (.tobject, true)]
      else #[(.tobject, n == `Omega.ST.Prim.Ref.swap || n == `Omega.ST.Prim.Ref.put), (.tobject, false)]
    verify compiled n (implicitArgs ++ parameters ++ #[(.tobject, false)]) .object symbol
  if interpreter then
    emitBridge compiled `StrictVoidInterpreter "src/OmegaChecks/InitPort/est_out_elim.h" output
  else
    writeCode lib owner compiled (layouts ++ codeExtensions ++ #[Lean.privateConstKindsExt.name])
    let modifyUnsafe := InitKernelPort.portName OmegaChecks.InitPort.ReferenceModify.implementation
    if env.contains modifyUnsafe then
      let publicEnv ← importModules #[{module := owner}] {}
      let some idx := publicEnv.getModuleIdx? owner | throw <| IO.userError s!"missing {owner}"
      unless (impureSigExt.getModuleEntries publicEnv idx).any (·.name == modifyUnsafe) do
        throw <| IO.userError s!"missing exported native signature for {modifyUnsafe}"
    emitBridge compiled owner "src/OmegaChecks/InitPort/reference_runtime.c" output

end ReferenceNative

public unsafe def main (args : List String) : IO Unit := do
  let (interpreter, args) := if args.head? == some "--interpreter" then (true, args.drop 1) else (false, args)
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  ReferenceNative.install lib output interpreter
