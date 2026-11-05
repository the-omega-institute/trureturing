import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence
import Reg.Support.SingleDependentReadout

/-! Retain the complete inverse-square envelope, continuity and pointwise
limit telescope, as well as the original completed-zeta Gamma consequence.
Only the displayed logarithmic error integrand in the actual integrability
domain is intervened on; the integral-to-zero conclusion is retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence
open LeanInformationAudit MeasureTheory Filter Real
open scoped Topology

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ t z => (1 + Real.log (1 + |t|)) * Complex.normSq z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : ℝ → ℂ} {V : ℕ → ℝ → ℂ} {D : ℝ},
    Continuous U → (∀ n, Continuous (V n)) →
    (∀ n t, ‖V n t‖ ≤ D / (1 + t ^ (2 : ℕ))) →
    (∀ t, Tendsto (fun n => V n t) atTop (𝓝 (U t))) →
    Integrable (fun t : ℝ =>
      (1 + Real.log (1 + |t|)) * Complex.normSq (U t)) ∧
    (∀ n, Integrable (fun t : ℝ => R.readout () t (V n t - U t))) ∧
    Tendsto (fun n => ∫ t : ℝ,
      (1 + Real.log (1 + |t|)) * Complex.normSq (V n t - U t)) atTop (𝓝 0) ∧
    Integrable (fun t : ℝ =>
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (U t)) ∧
    (∀ n, Integrable (fun t : ℝ =>
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (V n t))) ∧
    Tendsto (fun n => (1 / (2 * Real.pi)) * ∫ t : ℝ,
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (V n t)) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ t : ℝ,
        (2 * Real.pi * Zeta23.mu t) * Complex.normSq (U t)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hall := h (U := fun _ => 0) (V := fun _ _ => 0) (D := 0)
    continuous_const (fun _ => continuous_const)
    (by intro n t; simp) (fun _ => tendsto_const_nhds)
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) := hall.2.1 0
  letI : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hi
  simpa only [Real.volume_univ, lt_self_iff_false] using
    (measure_lt_top volume (Set.univ : Set ℝ))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (1 + Real.log (1 + |(0 : ℝ)|)) * Complex.normSq 0 ≠
    (1 + Real.log (1 + |(0 : ℝ)|)) * Complex.normSq 1
  norm_num

def evidence : Registration arena
    (type_of% @actual_gamma_tendsto_of_uniform_inverse_square) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_gamma_tendsto_of_uniform_inverse_square, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_gamma_tendsto_of_uniform_inverse_square)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ t z => (1 + Real.log (1 + |t|)) * Complex.normSq z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "body", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.InverseSquareGammaConvergence
