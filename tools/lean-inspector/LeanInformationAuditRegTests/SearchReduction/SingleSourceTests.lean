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
  let .ok ta := normalizedAtoms env target | throwError "target normalization failed"
  let .ok sa := normalizedAtoms env source | throwError "source normalization failed"
  let hits := presentationLookup ta [(`source, sa)]
  if expected && hits.isEmpty then throwError "directional lookup lost {label}: {ta}, {sa}"
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
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if name.toString.endsWith "card_derangements_fin_add_two" then
      let .ok sa := normalizedAtoms env info.type | throwError "normalization failed"
      unless (presentationLookup ta [(name, sa)]).isEmpty do
        throwError "unrelated derangements candidate reached conversion"
      checked := checked + 1
  unless checked > 0 do throwError "derangements fixture was not loaded"
  logInfo m!"actual syntax unrelated derangements declarations checked={checked}, conversion candidates=0"
end LeanInformationAudit.Tests.SearchReduction.SingleSourceTests
