import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.PolynomialStrictTransition
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Interpolation.PolynomialStrictTransition

open Set Polynomial LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x g => g x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ[X]) (g w : ℝ → ℝ) {l r : ℝ}, l < r →
    (∀ x ∈ Icc l r, 0 < w x) →
    (∀ x ∈ Icc l r, w x * g x = p.eval x) →
    0 < g l → g r < 0 →
    ∃ ξ δ : ℝ, 0 < δ ∧ Icc (ξ - δ) (ξ + δ) ⊆ Ioo l r ∧
      R.readout () ξ g = 0 ∧ (∀ x ∈ Ioo (ξ - δ) ξ, 0 < g x) ∧
      (∀ x ∈ Ioo ξ (ξ + δ), g x < 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ξ, δ, hδ, hsub, hz, hleft, hright⟩ :=
    h (-X) (fun x : ℝ => -x) (fun _ => 1) (l := -1) (r := 1)
      (by norm_num) (by intros; norm_num) (by intros; simp) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨0, (fun _ => 0), (fun _ => 1), by simp [actual, realize]⟩

def family : Registration arena
    (type_of% (@_root_.D5.S3.Analytic.Interpolation.PolynomialStrictTransition.strict_downward_of_polynomial_multiplier)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Analytic.Interpolation.PolynomialStrictTransition.strict_downward_of_polynomial_multiplier,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Analytic.Interpolation.PolynomialStrictTransition.strict_downward_of_polynomial_multiplier)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Interpolation.PolynomialStrictTransition.strictDownwardUnit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.PolynomialStrictTransition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x g => g x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.PolynomialStrictTransition
    definition := none
    coordinates := #[10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.PolynomialStrictTransition
