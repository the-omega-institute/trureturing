import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the optimal hyperbolic coefficient. -/

namespace Reg.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
open _root_.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep the complete claim and observe the coefficient in its sharpness premise. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ a b : ℝ, a ≠ 0 → b ≠ 0 → a ≠ b →
      lhs a b ≤ (1 / Real.sqrt 2) * Real.sqrt (radicand a b)) ∧
    ∀ C : ℝ, R.readout () () C < 1 / Real.sqrt 2 →
      ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
        C * Real.sqrt (radicand a b) < lhs a b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, ha, hb, hab, hstrict⟩ := h.2 (1 / Real.sqrt 2) (by
    change (0 : ℝ) < 1 / Real.sqrt 2
    positivity)
  exact (not_lt_of_ge (result.1 a b ha hb hab)) hstrict

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
    definition := some {
      owner := `D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
      name := `D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Analytic.Hyperbolic.HiraiNieuwboerWalterCothConstant
