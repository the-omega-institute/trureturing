import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.AbscissaSingularity
import Reg.Support.DependentFamily

/-! Full-law audit of the actual-cut singularity theorem. The observed value is
H(z). A translated readout is rejected using counting measure and X(n)=n. -/

open _root_.D5.S3.Analytic.Laplace.AbscissaSingularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Reg.D5.S3.Analytic.Laplace.AbscissaSingularity
noncomputable section
universe u

abbrev signature : Signature where
  Params := ℂ → ℂ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H z => H z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ H z => H (z - 1)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law Q := ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ},
    AEMeasurable X μ → (∀ᵐ ω ∂μ, 0 ≤ X ω) →
    (convergenceSet X μ).Nonempty → BddBelow (convergenceSet X μ) →
    ∀ {R : ℝ} {H : ℂ → ℂ}, 0 < R →
    ¬ (DifferentiableOn ℂ H (Metric.ball ((sInf (convergenceSet X μ) : ℝ) : ℂ) R) ∧
      ∀ z ∈ Metric.ball ((sInf (convergenceSet X μ) : ℝ) : ℂ) R,
        sInf (convergenceSet X μ) < z.re →
          Q.readout () H z = complexMGF X μ (-z))

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let μ : Measure (ULift.{u} ℕ) :=
    Measure.map (MeasurableEquiv.ulift.symm : ℕ ≃ᵐ ULift.{u} ℕ) Measure.count
  let X : ULift.{u} ℕ → ℝ := fun ω => ω.down
  have hC : convergenceSet X μ = Ioi (0 : ℝ) := by
    ext s
    change Integrable (fun ω => Real.exp (-s * X ω)) μ ↔ 0 < s
    rw [show μ = Measure.map (MeasurableEquiv.ulift.symm : ℕ ≃ᵐ ULift.{u} ℕ)
      Measure.count from rfl, integrable_map_equiv]
    change Integrable (fun n : ℕ => Real.exp (-s * (n : ℝ))) Measure.count ↔ 0 < s
    rw [integrable_count_iff]
    simp only [Real.norm_eq_abs, Real.abs_exp]
    simp_rw [mul_comm (-s)]
    rw [Real.summable_exp_nat_mul_iff]
    exact neg_lt_zero
  have hE : integrableExpSet X μ = Iio (0 : ℝ) := by
    ext s
    have he := congrArg (fun S : Set ℝ => -s ∈ S) hC
    simpa [convergenceSet, integrableExpSet] using he
  have hσ : sInf (convergenceSet X μ) = 0 := by simp [hC]
  let H : ℂ → ℂ := fun z => complexMGF X μ (-(z + 1))
  have hXm : AEMeasurable X μ := by dsimp [X]; fun_prop
  have hX : ∀ᵐ ω ∂μ, 0 ≤ X ω := ae_of_all _ (fun ω => Nat.cast_nonneg _)
  have hne : (convergenceSet X μ).Nonempty := by rw [hC]; exact ⟨1, by norm_num⟩
  have hbdd : BddBelow (convergenceSet X μ) := by rw [hC]; exact bddBelow_Ioi
  have hH : DifferentiableOn ℂ H (Metric.ball ((sInf (convergenceSet X μ) : ℝ) : ℂ) (1 / 2)) := by
    intro z hz
    have hz' : ‖z‖ < (1 : ℝ) / 2 := by simpa [hσ, Metric.mem_ball, dist_zero_right] using hz
    have hre : 0 < z.re + 1 := by have hl := (abs_le.mp (Complex.abs_re_le_norm z)).1; linarith
    have hd : (-(z + 1)).re ∈ interior (integrableExpSet X μ) := by
      simp only [hE, isOpen_Iio.interior_eq, mem_Iio, Complex.neg_re,
        Complex.add_re, Complex.one_re]
      linarith
    exact ((hasDerivAt_complexMGF hd).differentiableAt.comp z
      (differentiableAt_id.add_const 1).neg).differentiableWithinAt
  apply h hXm hX hne hbdd (R := 1 / 2) (H := H) (by norm_num)
  refine ⟨hH, ?_⟩
  intro z hz hzr
  change complexMGF X μ (-((z - 1) + 1)) = complexMGF X μ (-z)
  congr 1
  ring

def registration : Registration arena.{u} (type_of% (@no_holomorphic_extension_at_abscissa.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_holomorphic_extension_at_abscissa.{u}, rejected, rejected_fails⟩
  sensitivity := by
    dsimp only [Sensitivity, arena]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨id, 0, 1, zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_holomorphic_extension_at_abscissa.{u})
    (type_of% (realize signature (fun _ H z => H z) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.AbscissaSingularity.no_holomorphic_extension_at_abscissa.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.AbscissaSingularity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H z => H z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.AbscissaSingularity
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Laplace.AbscissaSingularity
