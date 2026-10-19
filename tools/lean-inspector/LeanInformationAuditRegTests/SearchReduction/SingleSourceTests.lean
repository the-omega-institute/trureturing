import Mathlib.Combinatorics.Derangements.Finite
import LeanInformationAuditRegAnalysis.SearchReduction.Isolation
import LeanInformationAuditRegTests.SearchReduction.SingleSourceModel
import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline

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

run_elab do
  probe "arithmetic alias" (← `(∀ n : Nat, ramp n = 3*n))
    (← `(∀ n : Nat, ramp n = n+n+n)) true
  probe "neutral packing" (← `(∀ n : Nat, ramp n = 3*n ∧ 0≤n))
    (← `(∀ n : Nat, ramp n = n+n+n)) true
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
  let index ← factIndex
  let (outcome, evidence, detail) ← baselinePresentation env [] target (some index)
  unless outcome == .found && evidence.isSome do
    throwError "full-environment single-source lookup: {reprStr outcome}: {detail}"
  logInfo m!"full-environment single-source lookup: found; {detail}"
end LeanInformationAudit.Tests.SearchReduction.SingleSourceTests
