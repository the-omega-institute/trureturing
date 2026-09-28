import LeanInformationAudit.Registry.Enrollment

namespace LeanInformationAudit.Tests.OwnerGraphMemo
open Lean Meta Elab Command
-- Exercise the owned implementation without adding a production test wrapper.
run_cmd do
  for name in #[`CompileState, `CompileM, `charge, `independentSource,
      `occurrenceIdentity, `compileExpr, `eraseInput] do
    let desired := `LeanInformationAudit.TemplateAudit ++ name
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      privateToUserName? n == some desired
    let [(actual, _)] := found | throwError "owned helper must be unique: {desired}"
    modifyEnv fun env => addAlias env (`LeanInformationAudit.Tests.OwnerGraphMemo ++ name) actual
  for (localName, desired) in #[
      (`makeState, `LeanInformationAudit.TemplateAudit.CompileState.mk),
      (`remaining, `LeanInformationAudit.TemplateAudit.CompileState.remaining),
      (`owners, `LeanInformationAudit.TemplateAudit.CompileState.independentOwners),
      (`identity, `LeanInformationAudit.TemplateAudit.CompileState.identityState),
      (`makeHeader, `Lean.EnvironmentHeader.mk),
      (`makeKernel, `Lean.Kernel.Environment.mk),
      (`extensions, `Lean.Kernel.Environment.extensions),
      (`irExtensions, `Lean.Kernel.Environment.irBaseExts)] do
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      privateToUserName? n == some desired
    let [(actual, _)] := found | throwError "fixture accessor must be unique: {desired}"
    modifyEnv fun env =>
      addAlias env (`LeanInformationAudit.Tests.OwnerGraphMemo ++ localName) actual

theorem target : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
theorem otherTarget : Nat.lt 1 (Nat.succ 1) := Nat.lt_succ_self 1
def first : Bool := false
def second : Bool := true
def independent : Bool := true

private def check (label : String) (ok : Bool) : MetaM Unit := do
  unless ok do throwError "[FAIL] {label}"
  logInfo m!"[PASS] {label}"

-- Preserve all real constants and extensions, varying only their synthetic
-- ownership/import metadata. A visits independent B before reaching T.
private def graph (env : Environment) (reaches : Bool := true)
    (missing : Bool := false) : Environment := Id.run do
  let base := env.header.modules.size
  let names := #[`OwnerMemo.T, `OwnerMemo.B, `OwnerMemo.A, `OwnerMemo.U]
  let modules := env.header.modules ++ names.map fun n =>
    ({ module := n, irPhases := .all, hasData := true } : EffectiveImport)
  let empty : ModuleData := {
    isModule := false, imports := #[], constNames := #[]
    constants := #[], extraConstNames := #[], entries := #[] }
  let imports : Array Import := if reaches then #[{module := names[0]!}, {module := names[1]!}]
    else #[{module := names[1]!}]
  let data := env.header.moduleData ++ #[empty, empty, { empty with imports }, empty]
  let indices := (List.range modules.size).foldl
    (fun map i => map.insert modules[i]!.module (i : ModuleIdx)) ({} : Std.HashMap Name ModuleIdx)
  let header := makeHeader env.header.trustLevel env.header.mainModule false
    env.header.imports env.header.regions modules indices (modules.filter (·.importAll))
    (if missing then data.extract 0 (base + 2) else data)
  let owners := env.toKernelEnv.const2ModIdx
    |>.insert ``target base |>.insert ``independent (base + 1)
    |>.insert ``first (base + 2) |>.insert ``second (base + 2)
    |>.insert ``otherTarget (base + 3)
  let kernel := env.toKernelEnv
  let constants := #[``target, ``otherTarget, ``first, ``second, ``independent].foldl
    (fun cs n => cs.insert n (env.find? n).get!) { kernel.constants with stage₁ := true }
  return .ofKernelEnv (makeKernel constants.switch kernel.quotInit kernel.diagnostics
    owners (extensions kernel) (irExtensions kernel) header)

private def initial (name : Name := ``target) (fuel : Nat := 100) : MetaM CompileState := do
  let identity ← LeanInformationAudit.RegistrationGates.argumentIdentityState name 524288
  return makeState fuel (some identity) #[] #[] {} {} {}

private def query (name : Name) : CompileM Bool := do
  -- Production callers have already charged; the lookup adds no extra debit.
  charge
  independentSource name

private def caught (action : CompileM Unit) : CompileM (Option String) := do
  try action; return none
  catch ex => return some (← ex.toMessageData.toString)

run_meta do
  let env ← getEnv
  withEnv (graph env) do
    for reverse in #[false, true] do
      let action : CompileM Unit := do
        if reverse then
          unless ← query ``independent do throwError "independent first"
        unless !(← query ``first) do throwError "dependent answer"
        let s ← get
        unless (owners s)[`OwnerMemo.A]? == some false &&
            (owners s)[`OwnerMemo.T]? == none &&
            (owners s)[`OwnerMemo.B]? == (if reverse then some true else none) do
          throwError "queried-owner-only memo"
        unless ← query ``independent do throwError "branch poisoned independent B"
        let before := (remaining (← get))
        unless !(← query ``second) do throwError "same owner answer"
        unless before - (remaining (← get)) == 1 do throwError "negative memo not reused"
        let before := (remaining (← get))
        unless ← query ``independent do throwError "warm positive answer"
        unless before - (remaining (← get)) == 1 do throwError "positive memo changed accounting"
      discard <| action.run (← initial)
      check s!"both_polarities_order_{reverse}_branch_and_constant_reuse" true
    let cold : CompileM Unit := do
      let error ← caught (discard <| query ``first)
      unless error == some "incomplete_closure:E8.work" &&
          (owners (← get))[`OwnerMemo.A]? == none do throwError "cold failure memoized"
    discard <| cold.run (← initial (fuel := 3))
    check "cold_exhaustion_before_target_pop_no_memo" true
    let (answer, exact) ← (query ``first).run (← initial (fuel := 4))
    check "exact_completion_budget" (!answer && (remaining exact) == 0 &&
      (owners exact)[`OwnerMemo.A]? == some false)
    for fuel in #[0, 1] do
      let action : CompileM Unit := do
        let error ← caught do
          discard <| query ``second
          charge
        unless error == some "incomplete_closure:E8.work" do throwError "warm downstream budget"
      discard <| action.run (makeState fuel (identity exact) #[] #[] {} (owners exact) {})
      check s!"warm_downstream_exhaustion_{fuel}" true
    let (answer, _) ← (query ``first).run (← initial ``otherTarget)
    check "fresh_target_changes_answer" answer
    let identityAction : CompileM Unit := do
      discard <| query ``first
      discard <| query ``independent
      let before ← get
      let envBefore ← getEnv
      occurrenceIdentity (mkConst ``Bool.false)
      let after ← get
      let envAfter ← getEnv
      unless envAfter.header.moduleNames == envBefore.header.moduleNames &&
          envAfter.header.moduleData.map (fun d => d.imports.map (·.module)) ==
            envBefore.header.moduleData.map (fun d => d.imports.map (·.module)) &&
          envAfter.const2ModIdx.toList == envBefore.const2ModIdx.toList do
        throwError "identity changed owner graph"
      unless (identity after).map (·.theoremName) == (identity before).map (·.theoremName) &&
          (owners after).toList == (owners before).toList do
        throwError "identity changed memo lifetime"
    discard <| identityAction.run (← initial (fuel := 1000))
    check "occurrence_identity_preserves_target_and_owner_memo" true
    let statement := (← getConstInfo ``target).type
    let proof := mkConst ``target
    let falseValue := mkConst ``Bool.false
    let bad := #[proof, statement,
      mkApp (.lam `dead statement falseValue .default) proof,
      Expr.letE `dead statement proof falseValue false]
    for i in [:bad.size] do
      let action : CompileM Unit := do
        discard <| query ``first
        discard <| query ``independent
        let error ← caught (discard <| compileExpr (← eraseInput bad[i]!) 0 false)
        unless error == some "forbidden_dependency:dtr.argument_audit" do
          throwError "warm guard {i}: {error}"
      discard <| action.run (← initial (fuel := 10000))
      check s!"warm_both_polarities_raw_proof_dead_argument_guard_{i}" true
    for (expression, depth, expected) in #[
        (mkConst ``String, 0, "forbidden_dependency:E6.closed_identity"),
        (mkConst ``Bool.false, 257, "incomplete_closure:E8.depth")] do
      let action : CompileM Unit := do
        discard <| query ``first
        discard <| query ``independent
        let error ← caught (discard <| compileExpr expression depth false)
        unless error == some expected do throwError "warm raw/depth guard: {error}"
      discard <| action.run (← initial (fuel := 10000))
      check s!"warm_guard_{expected}" true
    let (_, absent) ← (query ``first).run (makeState 100 none #[] #[] {} {} {})
    check "absent_identity_uncached" (owners absent).isEmpty
  withEnv (graph env false) do
    let (answer, _) ← (query ``first).run (← initial)
    check "fresh_environment_same_owner_changes_answer" answer
  withEnv (graph env true true) do
    let action : CompileM Unit := do
      for name in #[``first, ``second, `Missing.constant] do
        unless !(← query name) && (owners (← get)).isEmpty do
          throwError "missing metadata memoized"
    discard <| action.run (← initial)
    check "missing_metadata_and_unknown_constant_uncached" true

run_meta do
  let oversized := Expr.lit (.strVal (String.ofList (List.replicate 65536 'x')))
  check "source_identity_65536_byte_cap" (match TemplateAudit.compactRawIdentity [] oversized with
    | .error "incomplete_closure:E8.source_identity_bytes" => true
    | _ => false)

end LeanInformationAudit.Tests.OwnerGraphMemo
