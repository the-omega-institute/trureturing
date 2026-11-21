import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget
import Reg.Support.SingleDependentReadout

/-! The real part of the zero-frequency limit is the readout in the boundary bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory ProbabilityTheory
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {μ : Measure ℝ} {γ : ℝ} {z₀ z₁ z₂ : ℂ},
    (∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ) →
    Tendsto (fun σ : ℝ => (σ : ℂ) * complexMGF id μ (-(σ : ℂ))) (𝓝[>] 0) (𝓝 z₀) →
    Tendsto (fun σ : ℝ => (σ : ℂ) * complexMGF id μ (-((σ : ℂ) + (γ : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 z₁) →
    Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 z₂) →
    (Real.sqrt (‖z₂‖ ^ 2 + 8 * ‖z₁‖ ^ 2) - ‖z₂‖) / 2 ≤ V.readout () () z₀

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds
  have hi := h (μ := 0) (γ := 0) (z₀ := 0) (z₁ := 0) (z₂ := 0)
    (fun _ _ => integrable_zero_measure)
    (by simpa [complexMGF] using hz) (by simpa [complexMGF] using hz)
    (by simpa [complexMGF] using hz)
  norm_num [rejected, realize] at hi

def family : Registration arena (type_of% @two_harmonic_boundary_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_harmonic_boundary_budget, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    intro _
    exact ⟨(), 0, 1, by simpa [actual, realize] using (zero_ne_one : (0 : ℝ) ≠ 1)⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@two_harmonic_boundary_budget) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget.two_harmonic_boundary_budget.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget
