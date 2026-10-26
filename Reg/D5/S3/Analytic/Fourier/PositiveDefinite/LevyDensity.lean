import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
import Reg.Support.DependentFamily
import Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Typed realization contracts for the positive definite function library. -/

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
open _root_.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
open _root_.Reg.D5.S3.Analytic.Fourier.PositiveDefinite.Closure
open MeasureTheory Set Filter
open scoped ComplexOrder Topology
noncomputable section

abbrev densitySignature : Signature where
  Params := Σ _ : (ℝ → ℝ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def densityActual : Realization densitySignature :=
  realize densitySignature (fun _ p t => (Real.exp (-p.2 * (2 *
    ∫ s in Ioi 0, (1 - Real.cos (t * s)) * p.1 s / s)) : ℂ)) (fun e => nomatch e)

def densityRejected : Realization densitySignature :=
  realize densitySignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev densityArena : Arena where
  signature := densitySignature
  Law R := ∀ {D : ℝ → ℝ}, (∀ s, 0 < s → 0 ≤ D s) →
    (∀ n : ℕ, IntegrableOn (fun s => D s / s)
      (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))) →
    (∀ t, IntegrableOn (fun s => (1 - Real.cos (t * s)) * D s / s) (Ioi 0)) →
    ∀ {r : ℝ}, 0 < r → PositiveDefinite (R.readout () ⟨D, r⟩)

private theorem densityRejectedLaw : ¬ densityArena.Law densityRejected := by
  intro h
  have H := (h (D := fun _ => 0) (by simp)
    (by intro n; simpa using integrableOn_zero)
    (by intro t; simpa using integrableOn_zero)
    (r := 1) (by norm_num) 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num [densityRejected, realize] at H

private def cutoffDensity (s : ℝ) : ℝ :=
  if s ∈ Ioc (0 : ℝ) 1 then s else 0

private theorem cutoff_integral :
    (∫ s in Ioi 0, (1 - Real.cos (Real.pi * s)) * cutoffDensity s / s) = 1 := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ hs => hs.1
  have he : (∫ s in Ioi 0, (1 - Real.cos (Real.pi * s)) * cutoffDensity s / s) =
      ∫ s in Ioc (0 : ℝ) 1, 1 - Real.cos (Real.pi * s) := by
    calc
      _ = ∫ s in Ioi 0, (Ioc (0 : ℝ) 1).indicator
          (fun s => 1 - Real.cos (Real.pi * s)) s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        by_cases hm : s ∈ Ioc (0 : ℝ) 1
        · simp only [cutoffDensity, if_pos hm, Set.indicator_of_mem hm]
          exact mul_div_cancel_right₀ _ (ne_of_gt hs)
        · simp [cutoffDensity, hm]
      _ = _ := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr hsub]
  rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun s => s - Real.sin (Real.pi * s) / Real.pi)
    (f' := fun s => 1 - Real.cos (Real.pi * s))
    (fun s hs => by
      convert (hasDerivAt_id s).sub
        (((Real.hasDerivAt_sin (Real.pi * s)).comp s
          ((hasDerivAt_id s).const_mul Real.pi)).div_const Real.pi) using 1
      all_goals (try funext z)
      all_goals (try dsimp [Function.comp_def])
      all_goals field_simp [Real.pi_ne_zero]
      all_goals ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
  simpa using H

private theorem densityDependence : ObservationalDependence densitySignature densityActual := by
  intro i
  refine ⟨⟨cutoffDensity, 1⟩, 0, Real.pi, ?_⟩
  simp only [densityActual, realize, zero_mul, Real.cos_zero, sub_self, zero_mul, zero_div,
    integral_zero, mul_zero, Real.exp_zero, Complex.ofReal_one, cutoff_integral, one_mul]
  intro h
  have H : (1 : ℂ) = (Real.exp (-2) : ℂ) := by convert h using 1 <;> norm_num
  have HH : (1 : ℝ) = Real.exp (-2) := Complex.ofReal_inj.mp H
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

def densitySource : Registration densityArena (type_of% @positiveDefinite) where
  actual := densityActual
  bridge := Iff.rfl
  variation := ⟨positiveDefinite, densityRejected, densityRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨densityRejected, ?_, rfl, densityRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := densityDependence

def densityAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positiveDefinite) (Realization densitySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.densityUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.densitySource
  realizationSource := none
  generated := false
  arena := .source ⟨densityArena⟩
  objectArena := .source ⟨densityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source densityArena ⟨densitySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize densitySignature (fun _ p t => (Real.exp (-p.2 * (2 *
    ∫ s in Ioi 0, (1 - Real.cos (t * s)) * p.1 s / s)) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms densityAudit


abbrev finiteSignature : Signature where
  Params := Σ _ : MeasureTheory.Measure ℝ, Σ _ : (ℝ → ℝ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ p t => (Real.exp (-p.2.2 * ∫ s, (1 - Real.cos (t * s)) * p.2.1 s ∂p.1) : ℂ)) (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev finiteArena : Arena where
  signature := finiteSignature
  Law R := ∀ {μ : MeasureTheory.Measure ℝ} {d : ℝ → ℝ}, (∀ᵐ s ∂μ, 0 ≤ d s) → MeasureTheory.Integrable d μ → ∀ {r : ℝ}, 0 ≤ r → PositiveDefinite (R.readout () ⟨μ, d, r⟩)

private theorem finiteRejectedLaw : ¬ finiteArena.Law finiteRejected := by
  intro h
  exact negativeKernel_not_PD (h (μ := MeasureTheory.Measure.dirac (0 : ℝ)) (d := fun _ => 0) (by simp) (MeasureTheory.integrable_zero _ _ _) (r := 1) (by norm_num))

private theorem finiteDependence : ObservationalDependence finiteSignature finiteActual := by
  intro i
  refine ⟨⟨volume.restrict (Ioi (0 : ℝ)), (fun s => cutoffDensity s / s), 2⟩, 0, Real.pi, ?_⟩
  have HH : (∫ s in Ioi 0, (1 - Real.cos (Real.pi * s)) * (cutoffDensity s / s)) = 1 := by
    convert cutoff_integral using 1
    congr 1
    funext s
    ring
  simp only [finiteActual, realize, zero_mul, Real.cos_zero, sub_self, zero_mul,
    integral_zero, mul_zero, Real.exp_zero, Complex.ofReal_one, HH]
  intro h
  have H : (1 : ℂ) = (Real.exp (-2) : ℂ) := by convert h using 1 <;> norm_num
  have H' : (1 : ℝ) = Real.exp (-2) := Complex.ofReal_inj.mp H
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

def finiteSource : Registration finiteArena (type_of% @finite_density) where
  actual := finiteActual
  bridge := Iff.rfl
  variation := ⟨finite_density, finiteRejected, finiteRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finiteRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := finiteDependence

def finiteAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_density) (Realization finiteSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.finiteUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.finiteSource
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature (fun _ p t => (Real.exp (-p.2.2 * ∫ s, (1 - Real.cos (t * s)) * p.2.1 s ∂p.1) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms finiteAudit


abbrev exhaustionSignature : Signature where
  Params := Σ _ : MeasureTheory.Measure ℝ, Σ _ : (ℝ → ℝ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def exhaustionActual : Realization exhaustionSignature :=
  realize exhaustionSignature (fun _ p t => (Real.exp (-p.2.2 * ∫ s, (1 - Real.cos (t * s)) * p.2.1 s ∂p.1) : ℂ)) (fun e => nomatch e)

def exhaustionRejected : Realization exhaustionSignature :=
  realize exhaustionSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev exhaustionArena : Arena where
  signature := exhaustionSignature
  Law R := ∀ {μ : MeasureTheory.Measure ℝ} {d : ℝ → ℝ}, (∀ᵐ s ∂μ, 0 ≤ d s) → ∀ (K : ℕ → Set ℝ), (∀ n, MeasurableSet (K n)) → (∀ᵐ s ∂μ, ∀ᶠ n in atTop, s ∈ K n) → (∀ n, IntegrableOn d (K n) μ) → (∀ t, MeasureTheory.Integrable (fun s => (1 - Real.cos (t * s)) * d s) μ) → ∀ {r : ℝ}, 0 ≤ r → PositiveDefinite (R.readout () ⟨μ, d, r⟩)

private theorem exhaustionRejectedLaw : ¬ exhaustionArena.Law exhaustionRejected := by
  intro h
  exact negativeKernel_not_PD (h (μ := MeasureTheory.Measure.dirac (0 : ℝ)) (d := fun _ => 0) (by simp) (fun _ => Set.univ) (by simp) (by simp) (by intro n; exact MeasureTheory.integrable_zero _ _ _) (by intro t; simp) (r := 1) (by norm_num))

private theorem exhaustionDependence : ObservationalDependence exhaustionSignature exhaustionActual := by
  intro i
  refine ⟨⟨volume.restrict (Ioi (0 : ℝ)), (fun s => cutoffDensity s / s), 2⟩, 0, Real.pi, ?_⟩
  have HH : (∫ s in Ioi 0, (1 - Real.cos (Real.pi * s)) * (cutoffDensity s / s)) = 1 := by
    convert cutoff_integral using 1
    congr 1
    funext s
    ring
  simp only [exhaustionActual, realize, zero_mul, Real.cos_zero, sub_self, zero_mul,
    integral_zero, mul_zero, Real.exp_zero, Complex.ofReal_one, HH]
  intro h
  have H : (1 : ℂ) = (Real.exp (-2) : ℂ) := by convert h using 1 <;> norm_num
  have H' : (1 : ℝ) = Real.exp (-2) := Complex.ofReal_inj.mp H
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

def exhaustionSource : Registration exhaustionArena (type_of% @of_truncations) where
  actual := exhaustionActual
  bridge := Iff.rfl
  variation := ⟨of_truncations, exhaustionRejected, exhaustionRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exhaustionRejected, ?_, rfl, exhaustionRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := exhaustionDependence

def exhaustionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@of_truncations) (Realization exhaustionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.exhaustionUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity.exhaustionSource
  realizationSource := none
  generated := false
  arena := .source ⟨exhaustionArena⟩
  objectArena := .source ⟨exhaustionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exhaustionArena ⟨exhaustionSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize exhaustionSignature (fun _ p t => (Real.exp (-p.2.2 * ∫ s, (1 - Real.cos (t * s)) * p.2.1 s ∂p.1) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
    definition := none
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exhaustionAudit
end
end Reg.D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
