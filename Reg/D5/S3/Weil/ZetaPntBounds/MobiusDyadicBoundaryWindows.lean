import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Registration of the reciprocal-window bound on a zero-free line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex MeasureTheory

namespace BoundaryWindowsLinearWitness

noncomputable section

def f (z : ℂ) : ℂ := z - (1 / 4 : ℝ)

private def point (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I

def density (y : ℝ) : ℝ := 1 / ((1 + |y|) ^ 2 * ‖f (point y)‖ ^ 2)

theorem differentiable_f : Differentiable ℂ f :=
  differentiable_id.sub (differentiable_const ((1 / 4 : ℝ) : ℂ))

theorem deriv_f (z : ℂ) : deriv f z = 1 :=
  ((hasDerivAt_id z).sub_const ((1 / 4 : ℝ) : ℂ)).deriv

theorem root_f : f (((1 / 4 : ℝ) : ℂ)) = 0 := by simp [f]

theorem norm_f_pos (y : ℝ) : (1 / 4 : ℝ) ≤ ‖f (point y)‖ := by
  have hre : (f (point y)).re = 1 / 4 := by
    norm_num [f, point, Complex.mul_re]
  have h := Complex.abs_re_le_norm (f (point y))
  rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
  exact h

theorem zero_free (y : ℝ) : f (point y) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 4).trans_le (norm_f_pos y)

theorem integrable_density : Integrable density := by
  have hbase : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-2 : ℝ)) :=
    integrable_one_add_norm (by simp)
  have hdom : Integrable (fun y : ℝ => 16 * ((1 + |y|)⁻¹) ^ 2) := by
    refine (hbase.const_mul 16).congr ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  have hcont : Continuous density := by
    apply Continuous.div continuous_const
    · unfold f point
      fun_prop
    · intro y
      exact mul_ne_zero (by positivity) (pow_ne_zero _ (norm_ne_zero_iff.mpr (zero_free y)))
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hden : (1 + |y|) ^ 2 * (1 / 4 : ℝ) ^ 2 ≤ (1 + |y|) ^ 2 * ‖f (point y)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (norm_f_pos y) 2) (by positivity)
  have hdensity : 0 ≤ density y := by unfold density; positivity
  rw [Real.norm_of_nonneg hdensity]
  calc
    density y ≤ 1 / ((1 + |y|) ^ 2 * (1 / 4 : ℝ) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by
      rw [inv_pow]
      field_simp
      ring

end

end BoundaryWindowsLinearWitness

namespace Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows

noncomputable section

open Complex MeasureTheory Set
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows
open scoped BigOperators Function

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ g => integral volume g) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (t : Finset ι) (f : ℂ → ℂ) (θ : ℝ) (ρ : ι → ℂ) (M : ι → ℝ),
    (∀ i ∈ t, f (ρ i) = 0) →
    (∀ i ∈ t, (ρ i).re < θ) →
    (∀ i ∈ t, θ - (ρ i).re ≤ 1) →
    (∀ i ∈ t, 0 < M i) →
    (∀ y : ℝ, f ((θ : ℂ) + (y : ℂ) * I) ≠ 0) →
    (∀ i ∈ t, ∀ z ∈ rectangle θ (ρ i), DifferentiableAt ℂ f z) →
    (∀ i ∈ t, ∀ z ∈ rectangle θ (ρ i), ‖deriv f z‖ ≤ M i) →
    Set.Pairwise (↑t) (Disjoint on fun i => window θ (ρ i)) →
    Integrable (reciprocalDensity f θ) →
    (∑ i ∈ t, 1 / (8 * (θ - (ρ i).re) * (M i) ^ 2 * (1 + |(ρ i).im|) ^ 2)) ≤
      R.readout () () (reciprocalDensity f θ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let i : PUnit.{u + 1} := PUnit.unit
  let a : ℂ := ((1 / 4 : ℝ) : ℂ)
  have hρ (_ : PUnit.{u + 1}) : BoundaryWindowsLinearWitness.f a = 0 :=
    BoundaryWindowsLinearWitness.root_f
  have hdiff (z : ℂ) : DifferentiableAt ℂ BoundaryWindowsLinearWitness.f z :=
    BoundaryWindowsLinearWitness.differentiable_f z
  have hderiv (z : ℂ) : ‖deriv BoundaryWindowsLinearWitness.f z‖ ≤ 1 := by
    simp [BoundaryWindowsLinearWitness.deriv_f]
  have hsingle :
      Set.Pairwise (({i} : Finset PUnit.{u + 1}) : Set PUnit.{u + 1})
        (Disjoint on fun _ => window (1 / 2) a) := by
    intro j _ k _ hjk
    exact (hjk (Subsingleton.elim j k)).elim
  have hfalse := h ({i} : Finset PUnit.{u + 1}) BoundaryWindowsLinearWitness.f (1 / 2)
    (fun _ => a) (fun _ => 1) (fun j _ => hρ j)
    (fun _ _ => by norm_num [a]) (fun _ _ => by norm_num [a])
    (fun _ _ => by norm_num) BoundaryWindowsLinearWitness.zero_free
    (fun _ _ z _ => hdiff z) (fun _ _ z _ => hderiv z) hsingle
    BoundaryWindowsLinearWitness.integrable_density
  change (∑ j ∈ ({i} : Finset PUnit.{u + 1}),
    1 / (8 * (1 / 2 - a.re) * (1 : ℝ) ^ 2 * (1 + |a.im|) ^ 2)) ≤ 0 at hfalse
  have hvalue :
      1 / (8 * (1 / 2 - a.re) * (1 : ℝ) ^ 2 * (1 + |a.im|) ^ 2) = (1 / 2 : ℝ) := by
    norm_num [a]
  rw [Finset.sum_singleton, hvalue] at hfalse
  exact (by norm_num : ¬ (1 / 2 : ℝ) ≤ 0) hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (Icc (0 : ℝ) 1).indicator 1, ?_⟩
  change (∫ _ : ℝ, (0 : ℝ)) ≠ ∫ y : ℝ, (Icc (0 : ℝ) 1).indicator 1 y
  rw [integral_zero, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc]
  norm_num

def family : Registration arena.{u}
    (type_of% @finite_gap_mass_le_integral_reciprocalDensity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_gap_mass_le_integral_reciprocalDensity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_gap_mass_le_integral_reciprocalDensity.{u})
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows.finite_gap_mass_le_integral_reciprocalDensity.audit
  realizationName :=
    `Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g => integral volume g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundaryWindows
