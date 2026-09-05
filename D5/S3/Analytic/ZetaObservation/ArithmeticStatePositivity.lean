/- GID: D5/S3/Analytic/ZetaObservation/ArithmeticStatePositivity
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ArithmeticStatePositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta state induces a positive arithmetic Hilbert completion. -/
/- Library-search audit trail (2026-09-04):
   * `ZetaGibbs.zetaDist` is the existing normalized integer law and remains the family SSOT.
   * `ZetaEntropy.zeta_real_apply` and `ZetaGibbs.partition_function_toReal_eq_riemannZeta`
     give the pointwise mass and normalization identities used below.
   * Mathlib hits `PMF.integral_eq_tsum`, `BoundedContinuousFunction.integrable`,
     `PreInnerProductSpace.Core`, and `UniformSpace.Completion` supply the canonical construction.
   * D5, pinned Mathlib, and Loogle searches found no existing theorem combining the state
     positivity, normalized series, seminorm identity, separation, and Hilbert completion. -/

import D5.S3.Analytic.Zeta.ZetaEntropy
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.ArithmeticStatePositivity

open scoped BoundedContinuousFunction ComplexConjugate ComplexOrder ENNReal
open MeasureTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy

noncomputable section

/-- Bounded complex arithmetic observables. -/
abbrev ArithmeticObservable := ℕ →ᵇ ℂ

/-- The zeta expectation of a bounded arithmetic observable. -/
noncomputable def arithmeticState (s : ℝ) (hs : 1 < s)
    (F : ArithmeticObservable) : ℂ :=
  ∫ n, F n ∂(zetaDist s hs).toMeasure

set_option linter.unusedVariables false in
/-- The state-seminormed copy of the bounded arithmetic observables. -/
def ArithmeticPreHilbert (s : ℝ) (hs : 1 < s) := ArithmeticObservable

instance (s : ℝ) (_hs : 1 < s) : AddCommGroup (ArithmeticPreHilbert s _hs) :=
  inferInstanceAs (AddCommGroup ArithmeticObservable)

instance (s : ℝ) (hs : 1 < s) : Module ℂ (ArithmeticPreHilbert s hs) :=
  inferInstanceAs (Module ℂ ArithmeticObservable)

/-- Move an observable to the state-seminormed copy. -/
def toArithmeticPreHilbert (s : ℝ) (hs : 1 < s) :
    ArithmeticObservable ≃ₗ[ℂ] ArithmeticPreHilbert s hs :=
  LinearEquiv.refl ℂ _

/-- Recover the bounded function underlying a state-seminormed observable. -/
def ofArithmeticPreHilbert (s : ℝ) (hs : 1 < s) :
    ArithmeticPreHilbert s hs ≃ₗ[ℂ] ArithmeticObservable :=
  (toArithmeticPreHilbert s hs).symm

private lemma arithmetic_product_integrable (s : ℝ) (hs : 1 < s)
    (F G : ArithmeticObservable) :
    Integrable (fun n => conj (F n) * G n) (zetaDist s hs).toMeasure := by
  let H : ArithmeticObservable := star F * G
  convert BoundedContinuousFunction.integrable (zetaDist s hs).toMeasure H using 1
  ext n
  simp [H, RCLike.star_def]

/-- The zeta state supplies the pre-inner product used by the arithmetic completion. -/
@[instance_reducible]
noncomputable def arithmeticPreInnerProductCore (s : ℝ) (hs : 1 < s) :
    PreInnerProductSpace.Core ℂ (ArithmeticPreHilbert s hs) where
  inner F G := arithmeticState s hs
    (star (ofArithmeticPreHilbert s hs F) * ofArithmeticPreHilbert s hs G)
  conj_inner_symm F G := by
    rw [arithmeticState, arithmeticState, ← integral_conj]
    apply integral_congr_ae
    filter_upwards with n
    simp [RCLike.star_def, mul_comm]
  re_inner_nonneg F := by
    rw [arithmeticState]
    change 0 ≤ (∫ n, conj ((ofArithmeticPreHilbert s hs F) n) *
      (ofArithmeticPreHilbert s hs F) n ∂(zetaDist s hs).toMeasure).re
    have hIntegrable := arithmetic_product_integrable s hs
      (ofArithmeticPreHilbert s hs F) (ofArithmeticPreHilbert s hs F)
    have hNonneg : 0 ≤ ∫ n, RCLike.re
        (conj ((ofArithmeticPreHilbert s hs F) n) *
          (ofArithmeticPreHilbert s hs F) n) ∂(zetaDist s hs).toMeasure :=
      integral_nonneg fun n => by
        rw [Complex.conj_mul', ← Complex.ofReal_pow]
        change (0 : ℝ) ≤ ‖(ofArithmeticPreHilbert s hs F) n‖ ^ 2
        exact sq_nonneg _
    rw [integral_re hIntegrable] at hNonneg
    exact hNonneg
  add_left F G H := by
    rw [arithmeticState, arithmeticState, arithmeticState]
    let f := ofArithmeticPreHilbert s hs F
    let g := ofArithmeticPreHilbert s hs G
    let h := ofArithmeticPreHilbert s hs H
    calc
      (∫ n, (star (ofArithmeticPreHilbert s hs (F + G)) * h) n
          ∂(zetaDist s hs).toMeasure) =
          ∫ n, (conj (f n) * h n + conj (g n) * h n)
            ∂(zetaDist s hs).toMeasure := by
            apply integral_congr_ae
            filter_upwards with n
            simp [f, g, h, RCLike.star_def]
            ring
      _ = (∫ n, conj (f n) * h n ∂(zetaDist s hs).toMeasure) +
          ∫ n, conj (g n) * h n ∂(zetaDist s hs).toMeasure :=
        integral_add (arithmetic_product_integrable s hs f h)
          (arithmetic_product_integrable s hs g h)
      _ = _ := by
        simp [f, g, h, RCLike.star_def]
  smul_left F G c := by
    rw [arithmeticState, arithmeticState]
    let f := ofArithmeticPreHilbert s hs F
    let g := ofArithmeticPreHilbert s hs G
    calc
      (∫ n, (star (ofArithmeticPreHilbert s hs (c • F)) * g) n
          ∂(zetaDist s hs).toMeasure) =
          ∫ n, conj c * (conj (f n) * g n) ∂(zetaDist s hs).toMeasure := by
            apply integral_congr_ae
            filter_upwards with n
            simp [f, g, RCLike.star_def]
      _ = conj c * (∫ n, conj (f n) * g n ∂(zetaDist s hs).toMeasure) :=
        integral_const_mul _ _
      _ = _ := by simp [f, g, RCLike.star_def]

noncomputable instance (s : ℝ) (hs : 1 < s) :
    SeminormedAddCommGroup (ArithmeticPreHilbert s hs) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup
    (c := arithmeticPreInnerProductCore s hs)

noncomputable instance (s : ℝ) (hs : 1 < s) :
    InnerProductSpace ℂ (ArithmeticPreHilbert s hs) :=
  InnerProductSpace.ofCore (arithmeticPreInnerProductCore s hs)

/-- The arithmetic Hilbert space is the separated completion of the state seminorm. -/
abbrev ArithmeticHilbertSpace (s : ℝ) (hs : 1 < s) :=
  UniformSpace.Completion (ArithmeticPreHilbert s hs)

private lemma arithmetic_state_self_real (s : ℝ) (hs : 1 < s)
    (F : ArithmeticObservable) :
    (arithmeticState s hs (star F * F)).re =
      ∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure := by
  rw [arithmeticState]
  change (∫ n, conj (F n) * F n ∂(zetaDist s hs).toMeasure).re = _
  have hIntegrable := arithmetic_product_integrable s hs F F
  calc
    (∫ n, conj (F n) * F n ∂(zetaDist s hs).toMeasure).re =
        ∫ n, RCLike.re (conj (F n) * F n) ∂(zetaDist s hs).toMeasure :=
      (integral_re hIntegrable).symm
    _ = ∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure := by
      apply integral_congr_ae
      filter_upwards with n
      rw [Complex.conj_mul', ← Complex.ofReal_pow]
      change ‖F n‖ ^ 2 = ‖F n‖ ^ 2
      rfl

private lemma arithmetic_state_self_eq_ofReal (s : ℝ) (hs : 1 < s)
    (F : ArithmeticObservable) :
    arithmeticState s hs (star F * F) =
      ((∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure : ℝ) : ℂ) := by
  have hIntegrable := arithmetic_product_integrable s hs F F
  apply Complex.ext
  · simpa using arithmetic_state_self_real s hs F
  · rw [arithmeticState]
    calc
      (∫ n, conj (F n) * F n ∂(zetaDist s hs).toMeasure).im =
          ∫ n, (conj (F n) * F n).im ∂(zetaDist s hs).toMeasure :=
        (integral_im hIntegrable).symm
      _ = ∫ n, (((‖F n‖ ^ 2 : ℝ) : ℂ)).im
          ∂(zetaDist s hs).toMeasure := by
        apply integral_congr_ae
        filter_upwards with n
        rw [Complex.conj_mul', ← Complex.ofReal_pow]
      _ = ∫ _n : ℕ, (0 : ℝ) ∂(zetaDist s hs).toMeasure := by
        apply integral_congr_ae
        filter_upwards with n
        exact Complex.ofReal_im _
      _ = 0 := by simp
      _ = ((∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure : ℝ) : ℂ).im := by simp

private lemma arithmetic_square_integrable (s : ℝ) (hs : 1 < s)
    (F : ArithmeticObservable) :
    Integrable (fun n => ‖F n‖ ^ 2) (zetaDist s hs).toMeasure := by
  have hComplex := arithmetic_product_integrable s hs F F
  simpa [norm_mul, sq] using hComplex.norm

private lemma partition_toReal_eq_zeta_re (s : ℝ) (hs : 1 < s) :
    (partitionFunction s).toReal = (riemannZeta (s : ℂ)).re := by
  exact congrArg Complex.re (partition_function_toReal_eq_riemannZeta s hs)

/-- The normalized zeta state is positive, has its exact integer expansion, induces the
arithmetic seminorm, identifies precisely its zero-norm observations in the completion, and
has a dense complete inner-product completion. -/
theorem arithmetic_positivity (s : ℝ) (hs : 1 < s) (F : ArithmeticObservable) :
    0 ≤ (1 / (riemannZeta (s : ℂ)).re) *
        ∑' n : ℕ, ‖F n‖ ^ 2 * (n : ℝ) ^ (-s) ∧
      arithmeticState s hs (star F * F) =
        (((1 / (riemannZeta (s : ℂ)).re) *
          ∑' n : ℕ, ‖F n‖ ^ 2 * (n : ℝ) ^ (-s) : ℝ) : ℂ) ∧
      ((‖toArithmeticPreHilbert s hs F‖ ^ 2 : ℝ) : ℂ) =
        arithmeticState s hs (star F * F) ∧
      (((toArithmeticPreHilbert s hs F : ArithmeticPreHilbert s hs) :
          ArithmeticHilbertSpace s hs) = 0 ↔
        ‖toArithmeticPreHilbert s hs F‖ = 0) ∧
      DenseRange ((↑) : ArithmeticPreHilbert s hs → ArithmeticHilbertSpace s hs) ∧
      CompleteSpace (ArithmeticHilbertSpace s hs) ∧
      ∀ x : ArithmeticHilbertSpace s hs,
        ‖x‖ ^ 2 = (inner ℂ x x).re := by
  have hReal := arithmetic_state_self_real s hs F
  have hState := arithmetic_state_self_eq_ofReal s hs F
  have hExpansion :
      (∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure : ℝ) =
        (1 / (riemannZeta (s : ℂ)).re) *
          ∑' n : ℕ, ‖F n‖ ^ 2 * (n : ℝ) ^ (-s) := by
    rw [PMF.integral_eq_tsum _ _ (arithmetic_square_integrable s hs F)]
    simp only [smul_eq_mul]
    change (∑' n : ℕ, pmfReal (zetaDist s hs) n * ‖F n‖ ^ 2) = _
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [zeta_real_apply, partition_toReal_eq_zeta_re s hs]
    ring
  have hSeminormReal :
      ‖toArithmeticPreHilbert s hs F‖ ^ 2 =
        ∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure := by
    calc
      ‖toArithmeticPreHilbert s hs F‖ ^ 2 =
          (inner ℂ (toArithmeticPreHilbert s hs F)
            (toArithmeticPreHilbert s hs F)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (arithmeticState s hs (star F * F)).re := rfl
      _ = ∫ n, ‖F n‖ ^ 2 ∂(zetaDist s hs).toMeasure := hReal
  constructor
  · rw [← hExpansion]
    exact integral_nonneg fun n => sq_nonneg ‖F n‖
  constructor
  · rw [hState, hExpansion]
  constructor
  · exact (congrArg (fun r : ℝ => (r : ℂ)) hSeminormReal).trans hState.symm
  constructor
  · rw [← norm_eq_zero, UniformSpace.Completion.norm_coe]
  constructor
  · exact UniformSpace.Completion.denseRange_coe
  constructor
  · infer_instance
  · intro x
    exact norm_sq_eq_re_inner (𝕜 := ℂ) x

#print axioms arithmetic_positivity

end


end D5.S3.Analytic.ZetaObservation.ArithmeticStatePositivity
