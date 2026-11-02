import Mathlib.Combinatorics.Derangements.Finite
import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
import LeanInformationAuditRegTests.SearchReduction.SingleSourceModel
import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline
import LeanInformationAuditRegTests.SearchReduction.Baseline

/-! Actual metaprogram probes connect the syntax, query and certificates. -/
namespace LeanInformationAudit.Tests.SearchReduction.SingleSourceTests
open Lean Meta Elab LeanInformationAudit.SearchReduction
open PresentationBaseline

private def statement (s : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm s (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def probe (label : String) (t s : Syntax) (expected : Bool) : TermElabM Unit := do
  let target ← statement t
  let source ← statement s
  let env ← getEnv
  let ta ← match normalizedAtoms env target with
    | .ok atoms => pure atoms
    | .error err => throwError "target normalization failed: {err}"
  let sa ← match normalizedAtoms env source with
    | .ok atoms => pure atoms
    | .error err => throwError "source normalization failed: {label}: {err}"
  let hits := presentationLookup ta [(`source, sa)]
  if expected && hits.isEmpty then
    throwError "directional lookup lost {label}: {reprStr ta}, {reprStr sa}"
  let saved ← saveState
  let conversion ← singleSourceConversion target source
  unless conversion.isSome == expected do throwError "single source mismatch: {label}"
  if let some proof := conversion then
    discard <| checkProof (← mkFreshUserName `_singleSourceTest) [] (← mkArrow source target) proof
  saved.restore
  logInfo m!"single-source {label}: expected={expected}, candidates={hits.length}, kernel-checked"

private def legacyProbe (memo : IO.Ref LegacyNormalizationMemo) (index : FactIndex)
    (label : String) (t s : Syntax) (expected : Bool) : TermElabM Unit := do
  let target ← statement t
  let source ← statement s
  let saved ← saveState
  let old ← restatementConversion target source index
  unless old.isSome == expected do throwError "legacy fixture mismatch: {label}"
  saved.restore
  for _ in [:2] do
    let conversion ← restatementConversion target source index (some memo)
    unless conversion.isSome == old.isSome do
      throwError "memo changed the legacy restatement relation: {label}"
    if let some proof := conversion then
      discard <| checkProof (← mkFreshUserName `_legacyMemoTest) []
        (← mkArrow source target) proof
    saved.restore
  logInfo m!"legacy-restatement {label}: old={expected}, memo=cold-and-warm, kernel-checked"

private theorem legacy_bounds (n : Nat) : ramp n ≤ n+n+n ∧ n+n+n ≤ ramp n := by
  rw [ramp_value]
  exact ⟨le_rfl, le_rfl⟩

set_option maxHeartbeats 0 in
run_elab do
  let memo ← IO.mkRef ({} : LegacyNormalizationMemo)
  let index : FactIndex := {}
  legacyProbe memo index "joint arithmetic restatement"
    (← `(∀ n m : Nat, n = m)) (← `(∀ n m : Nat, n ≤ m ∧ m ≤ n)) true
  legacyProbe memo index "source packing and arithmetic"
    (← `(∀ n : Nat, n+n = 2*n)) (← `(∀ n : Nat, True ∧ n*2 = n+n)) true
  legacyProbe memo index "permuted conjunction"
    (← `(∀ P Q : Prop, Q ∧ P)) (← `(∀ P Q : Prop, P ∧ Q)) true
  legacyProbe memo index "full telescope Iff projection"
    (← `(∀ P Q : Prop, P → Q)) (← `(∀ P Q : Prop, P ↔ Q)) true
  legacyProbe memo index "added premise retained"
    (← `(∀ n : Nat, n = n)) (← `(∀ n : Nat, n = 0 → n = n)) false
  legacyProbe memo index "binder kind retained"
    (← `(∀ n : Nat, n = n)) (← `(∀ {n : Nat}, n = n)) false
  legacyProbe memo index "dependent domain retained"
    (← `(∀ n : Nat, ∀ i : Fin n, i = i))
    (← `(∀ n : Nat, ∀ i : Fin (n+1), i = i)) false
  legacyProbe memo index "foreign component not inferred"
    (← `(∀ P Q : Prop, P ∧ Q)) (← `(∀ P Q : Prop, P)) false
  legacyProbe memo index "explicit telescope self conversion"
    (← `(∀ n : Nat, n = n)) (← `(∀ n : Nat, n = n)) true
  let explicitSize := (← memo.get).values.size
  legacyProbe memo index "implicit telescope self conversion"
    (← `(∀ {n : Nat}, n = n)) (← `(∀ {n : Nat}, n = n)) true
  unless (← memo.get).values.size > explicitSize do
    throwError "legacy memo erased telescope binder annotations"
  let target ← statement (← `(∀ n : Nat, ramp n = n+n+n))
  let source := (← getConstInfo ``legacy_bounds).type
  if (← singleSourceConversion target source).isSome then
    throwError "legacy-only regression is already covered by the single-source guard"
  let saved ← saveState
  let rejected ← try
    copyStructure (← getEnv) `_legacyPackingTarget target ``legacy_bounds index
      (normalization? := some memo)
    pure false
    catch ex =>
      let message ← ex.toMessageData.toString
      unless message.startsWith "search.target_restatement:" do throw ex
      pure true
  saved.restore
  unless rejected do throwError "legacy-only target packing escaped copyStructure"
  let state ← memo.get
  unless state.hits > 0 && state.misses > 0 do throwError "legacy memo was not exercised"
  for (key, value) in state.values.toList do
    if key.val.hasFVar || key.val.hasMVar || key.val.hasLooseBVars ||
        value.hasFVar || value.hasMVar || value.hasLooseBVars then
      throwError "legacy memo leaked a local context"
    let original ← withReducible <| reduce key.val (skipTypes := false)
    unless original.equal value do throwError "memo differs from the pinned full reduction"
  logInfo m!"legacy normalization memo: hits={state.hits}, misses={state.misses}, \
    closed-keys=true, original-normal-forms=true, legacy-only-copy=rejected"

run_elab do
  probe "arithmetic alias" (← `(∀ n : Nat, ramp n = 3*n))
    (← `(∀ n : Nat, ramp n = n+n+n)) true
  probe "neutral packing" (← `(∀ n : Nat, ramp n = 3*n ∧ 0≤n))
    (← `(∀ n : Nat, ramp n = n+n+n)) true
  probe "neutral True packing" (← `(∀ n : Nat, 0 < n+1 ∧ True))
    (← `(∀ n : Nat, 0 ≤ n)) true
  probe "opaque projection inclusion" (← `(∀ n : Nat, ramp n = 3*n))
    (← `(∀ n : Nat, ramp n = 3*n ∧ n % 2 = 0)) true
  probe "projection inclusion" (← `(∀ P Q : Prop, P))
    (← `(∀ P Q : Prop, P ∧ Q)) true
  probe "single source pack" (← `(∀ P Q : Prop, Q ∧ P))
    (← `(∀ P Q : Prop, P ∧ Q)) true
  probe "no foreign baseline component" (← `(∀ P Q : Prop, P ∧ Q))
    (← `(∀ P Q : Prop, P)) false
  probe "no baseline-supplied exact component" (← `(∀ n : Nat, ramp n = n+n+n))
    (← `(∀ n : Nat, n=n)) false
  probe "no baseline-supplied arithmetic" (← `(∀ n : Nat, ramp n = 3*n))
    (← `(∀ n : Nat, n=n)) false
  probe "iff direction" (← `(∀ P Q : Prop, P → Q))
    (← `(∀ P Q : Prop, P ↔ Q)) true
  let target ← statement (← `(∀ P Q : Prop, P ∧ Q))
  let left ← statement (← `(∀ P Q : Prop, P))
  let right ← statement (← `(∀ P Q : Prop, Q))
  unless ← collectionLeak target #[left, right] do
    throwError "split S components escaped the collection guard"
  let env ← getEnv
  let target ← statement (← `(∀ n : Nat, ramp n = 3*n))
  let .ok ta := normalizedAtoms env target | throwError "normalization failed"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.endsWith "card_derangements_fin_add_two" ||
        name == `Circle.path_self || name == `Circle.range_path_ssubset_univ ||
        name.toString.endsWith "blastDivSubtractShift._proof_8" then
      let bound := (rawOrigins env info.type).run' {}
      if rawNecessary env ta bound then
        throwError "unrelated derangements declaration passed the raw necessary condition"
      checked := checked + 1
  unless checked > 0 do throwError "derangements fixture was not loaded"
  logInfo m!"raw dependency rejection: unrelated declarations={checked}, \
    normalizations=0, conversions=0"
  let source ← statement (← `(∀ n : Nat, ramp n = n+n+n ∧ n % 2 = 0))
  let bound := (rawOrigins env source).run' {}
  unless rawNecessary env ta bound do throwError "raw filter lost a packaged source"
  let rawEquality := (ta.flatMap (·.constants)).filter (originAnchor env) |>.eraseDups
  unless rawEquality.any (fun n => !bound.names.contains n) ||
      bound.names.toList.any (fun n => !rawEquality.contains n) do
    throwError "full-constant equality mutation is not distinguished"
  logInfo "raw equality mutant rejected; directional raw filter retained packaged source"
  let scopedTarget ← statement (← `(∀ (X : Type) (P : X → Prop) (x : X), P x → P x))
  let unrelated ← statement (← `(∀ (X : Type) (n : Nat), n = n + 0))
  let targetKeys ← match normalizedAtoms env scopedTarget with
    | .ok keys => pure keys | .error err => throwError "scope target: {err}"
  if rawNecessary env targetKeys ((rawOrigins env unrelated).run' {}) then
    throwError "rigid telescope mismatch passed the raw necessary condition"
  logInfo "rigid telescope mismatch rejected without normalization"
  -- Mutation: erasing neutral scope markers makes True.intro a false hit.
  let neutralTarget ← statement (← `(∀ n : Nat, n = n))
  let neutralSource := (← getConstInfo ``True.intro).type
  let .ok nt := normalizedAtoms env neutralTarget | throwError "neutral target normalization"
  let .ok ns := normalizedAtoms env neutralSource | throwError "neutral source normalization"
  if supportIncluded nt ns then throwError "neutral telescope was erased from production keys"
  unless supportIncluded (nt.filter (! ·.isScope)) (ns.filter (! ·.isScope)) do
    throwError "neutral telescope-erasure mutant is not distinguished"
  unless !sourceScopeNecessary env unrelated targetKeys do
    throwError "production telescope prefilter weakening was not detected"
  let commuted := (← getConstInfo
    ``LeanInformationAudit.Tests.SearchReduction.Baseline.commuted)
  let entry := (`LeanInformationAudit.Tests.SearchReduction.Baseline.commuted, commuted)
  unless (productionDomain #[entry]).any (fun e => e.1 == entry.1) do
    throwError "production domain lost actual source"
  let direction ← statement (← `(∀ P Q : Prop, P ∧ Q → Q ∧ P))
  let .ok dk := normalizedAtoms env direction | throwError "direction normalization"
  let bound := (rawOrigins env commuted.type).run' {}
  let .ok sk := normalizedAtomsWithOrigins env commuted.type bound
    | throwError "actual source normalization"
  unless sourceScopeNecessary env commuted.type dk &&
      rawNecessary env dk bound && supportIncluded dk sk do
    throwError "production coverage bridge lost actual Iff direction"
  if supportIncluded dk ns then throwError "unscoped source passed the production query"
  logInfo "production coverage: actual domain, early scope, origins, N, directional query checked"
  logInfo "scope-erasure and weakened-telescope-filter mutants rejected"
  let index ← factIndex
  let (outcome, evidence, detail) ← baselinePresentation env [] target (some index)
  unless outcome == .found && evidence.isSome do
    throwError "full-environment single-source lookup: {reprStr outcome}: {detail}"
  logInfo m!"full-environment single-source lookup: found; {detail}"
end LeanInformationAudit.Tests.SearchReduction.SingleSourceTests
