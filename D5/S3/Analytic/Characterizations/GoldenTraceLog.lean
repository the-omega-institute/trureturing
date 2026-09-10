/- GID: D5/S3/Analytic/Characterizations/GoldenTraceLog
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenTraceLog
   mirror-E: none(waiver:analytically-proved)
   anchors: []
   utility: none
   digest: The trace series gives the determinant's local negative principal logarithm. -/

import D5.S0.Observation.MatrixTracePowerSum
import D5.S1.Eigenstructure.FibonacciMatrixDiscriminant
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
The positive exponential of the infinite trace series is defined only on the local disk.
The two-root logarithm identity gives its principal branch and identifies the separate
rational expression there. Pole and word-growth statements are owned by
GoldenDynamicalDeterminant in this characterization family.
-/

open scoped Matrix
open Filter

noncomputable section

namespace D5.S3.Analytic.Characterizations.GoldenTraceLog

def adjacency : Matrix (Fin 2) (Fin 2) ℂ :=
  D5.S1.Scale.fibonacciSubstitution.map Complex.ofReal

def traceTerm : ℂ → ℕ → ℂ :=
  fun z n => Matrix.trace (adjacency ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1)

def localDomain : Set ℂ := {z | ‖z‖ < Real.goldenRatio⁻¹}

def traceSum : localDomain → ℂ := fun z => ∑' n : ℕ, traceTerm z.val n

def dynamicalZeta : localDomain → ℂ := fun z => Complex.exp (traceSum z)

def continuation : ℂ → ℂ := fun z => 1 / (1 - z - z ^ 2)

/-- The actual matrix series, its principal branch, and the local exponential identity. -/
def localContract : Prop :=
  (∀ z : ℂ,
    Matrix.det (1 - z • adjacency) = 1 - z - z ^ 2 ∧
    1 - z - z ^ 2 = (1 - (Real.goldenRatio : ℂ) * z) *
      (1 + ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * z)) ∧
  (∀ n : ℕ, Matrix.trace (adjacency ^ n) =
    (Real.goldenRatio : ℂ) ^ n + (Real.goldenConj : ℂ) ^ n) ∧
  (∀ z : localDomain,
    0 < (Matrix.det (1 - z.val • adjacency)).re ∧
    Matrix.det (1 - z.val • adjacency) ≠ 0 ∧
    Summable (fun n : ℕ => ‖traceTerm z.val n‖) ∧
    HasSum (traceTerm z.val) (-Complex.log (Matrix.det (1 - z.val • adjacency))) ∧
    traceSum z = -Complex.log (Matrix.det (1 - z.val • adjacency)) ∧
    dynamicalZeta z = continuation z.val) ∧
  AnalyticOnNhd ℂ (fun z => -Complex.log (Matrix.det (1 - z • adjacency))) localDomain ∧
  Complex.log (Matrix.det (1 - (0 : ℂ) • adjacency)) = 0

private theorem det_vieta (M : Matrix (Fin 2) (Fin 2) ℂ) (a b z : ℂ)
    (ht : Matrix.trace M = a + b) (hd : Matrix.det M = a * b) :
    Matrix.det (1 - z • M) = (1 - a * z) * (1 - b * z) := by
  have ht' := ht
  have hd' := hd
  simp only [Matrix.trace_fin_two] at ht'
  simp only [Matrix.det_fin_two] at hd'
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  norm_num
  linear_combination -z * ht' + z ^ 2 * hd'

/-- The logarithm terms are absolutely summable inside the unit disk. -/
theorem summable_norm_log_terms (w : ℂ) (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => ‖w ^ (n + 1) / (n + 1 : ℂ)‖) := by
  have h := (summable_geometric_of_norm_lt_one hw).norm
  have hs := (summable_nat_add_iff 1).2 h
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro n
  simp only [norm_div, norm_pow]
  apply div_le_self (pow_nonneg (norm_nonneg w) _)
  rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
  exact_mod_cast Nat.le_add_left 1 n

private theorem log_pair (u v : ℂ) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    (1 - u) ≠ 0 ∧ (1 - v) ≠ 0 ∧
    Complex.log ((1 - u) * (1 - v)) = Complex.log (1 - u) + Complex.log (1 - v) := by
  have hure : 0 < (1 - u).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm u]
  have hvre : 0 < (1 - v).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm v]
  have hun : 1 - u ≠ 0 := by intro h; simp [h] at hure
  have hvn : 1 - v ≠ 0 := by intro h; simp [h] at hvre
  refine ⟨hun, hvn, (Complex.log_mul_eq_add_log_iff hun hvn).2 ?_⟩
  have hau := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hure))
  have hav := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hvre))
  exact ⟨by linarith, by linarith⟩

/-- The two-root producer discharges convergence and the principal product branch. -/
theorem matrix_trace_log (M : Matrix (Fin 2) (Fin 2) ℂ) (a b z : ℂ)
    (ht : Matrix.trace M = a + b) (hd : Matrix.det M = a * b)
    (ha : ‖a * z‖ < 1) (hb : ‖b * z‖ < 1) :
    Matrix.det (1 - z • M) ≠ 0 ∧
    Summable (fun n : ℕ => ‖Matrix.trace (M ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1)‖) ∧
    HasSum (fun n : ℕ => Matrix.trace (M ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1))
      (-Complex.log (Matrix.det (1 - z • M))) ∧
    Complex.exp (∑' n : ℕ, Matrix.trace (M ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1)) =
      (Matrix.det (1 - z • M))⁻¹ := by
  have terms (n : ℕ) : Matrix.trace (M ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1) =
      (a * z) ^ (n + 1) / (n + 1 : ℂ) + (b * z) ^ (n + 1) / (n + 1 : ℂ) := by
    rw [D5.S0.Observation.MatrixTracePowerSum.trace_pow_eq_add_pow M a b ht hd]
    simp only [mul_pow]
    ring
  obtain ⟨han, hbn, hlog⟩ := log_pair (a * z) (b * z) ha hb
  have hn : Matrix.det (1 - z • M) ≠ 0 := by
    rw [det_vieta M a b z ht hd]
    exact mul_ne_zero han hbn
  have hs : HasSum (fun n : ℕ => Matrix.trace (M ^ (n + 1)) / (n + 1 : ℂ) * z ^ (n + 1))
      (-Complex.log (Matrix.det (1 - z • M))) := by
    simp_rw [terms, det_vieta M a b z ht hd, hlog, neg_add]
    exact (Complex.hasSum_taylorSeries_neg_log' ha).add
      (Complex.hasSum_taylorSeries_neg_log' hb)
  refine ⟨hn, ?_, hs, ?_⟩
  · have hc := (summable_norm_log_terms (a * z) ha).add (summable_norm_log_terms (b * z) hb)
    refine hc.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro n
    rw [terms]
    exact norm_add_le _ _
  · rw [hs.tsum_eq, Complex.exp_neg, Complex.exp_log hn]

/-- Exact specialization of the producer, with the principal branch throughout the disk. -/
theorem golden_local : localContract := by
  have hsum : (Real.goldenRatio : ℂ) + (Real.goldenConj : ℂ) = 1 := by
    exact_mod_cast Real.goldenRatio_add_goldenConj
  have hprod : (Real.goldenRatio : ℂ) * (Real.goldenConj : ℂ) = -1 := by
    exact_mod_cast Real.goldenRatio_mul_goldenConj
  have ht : Matrix.trace adjacency = (Real.goldenRatio : ℂ) + (Real.goldenConj : ℂ) := by
    rw [hsum]
    have h := congrArg Complex.ofReal
      D5.S1.Eigenstructure.FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant.1
    simpa [adjacency, Matrix.trace_fin_two] using h
  have hd : Matrix.det adjacency = (Real.goldenRatio : ℂ) * (Real.goldenConj : ℂ) := by
    rw [hprod]
    have h := congrArg Complex.ofReal
      D5.S1.Eigenstructure.FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant.2.1
    simpa [adjacency, Matrix.det_fin_two] using h
  have factor (z : ℂ) :
      (1 - (Real.goldenRatio : ℂ) * z) * (1 - (Real.goldenConj : ℂ) * z) =
        1 - z - z ^ 2 := by
    linear_combination -z * hsum + z ^ 2 * hprod
  have algebra (z : ℂ) : Matrix.det (1 - z • adjacency) = 1 - z - z ^ 2 ∧
      1 - z - z ^ 2 = (1 - (Real.goldenRatio : ℂ) * z) *
        (1 + ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * z) := by
    refine ⟨(det_vieta adjacency _ _ z ht hd).trans (factor z), ?_⟩
    rw [show ((Real.goldenRatio⁻¹ : ℝ) : ℂ) = -(Real.goldenConj : ℂ) by
      exact_mod_cast Real.inv_goldenRatio]
    simpa only [neg_mul, sub_eq_add_neg] using (factor z).symm
  have hr : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : Real.goldenRatio⁻¹ < 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.neg_one_lt_goldenConj]
  have hquad : Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹) ^ 2 = 1 := by
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have right (z : ℂ) (hz : z ∈ localDomain) :
      0 < (Matrix.det (1 - z • adjacency)).re := by
    rw [(algebra z).1]
    have hz' : ‖z‖ < Real.goldenRatio⁻¹ := hz
    have hsq : ‖z‖ ^ 2 < (Real.goldenRatio⁻¹) ^ 2 := by
      nlinarith [norm_nonneg z]
    have hz2 := Complex.re_le_norm (z ^ 2)
    rw [norm_pow] at hz2
    simp only [Complex.sub_re, Complex.one_re]
    nlinarith [Complex.re_le_norm z]
  refine ⟨algebra, ?_, ?_, ?_, by simp⟩
  · exact D5.S0.Observation.MatrixTracePowerSum.trace_pow_eq_add_pow adjacency _ _ ht hd
  · intro z
    have hz : ‖z.val‖ < Real.goldenRatio⁻¹ := z.property
    have ha : ‖(Real.goldenRatio : ℂ) * z.val‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.goldenRatio_pos.le]
      have h := (lt_div_iff₀ Real.goldenRatio_pos).mp (show ‖z.val‖ < 1 / Real.goldenRatio by
        simpa only [one_div] using hz)
      nlinarith
    have hb : ‖(Real.goldenConj : ℂ) * z.val‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonpos Real.goldenConj_neg.le,
        ← Real.inv_goldenRatio]
      nlinarith [norm_nonneg z.val]
    obtain ⟨hn, hs, hh, he⟩ := matrix_trace_log adjacency _ _ z.val ht hd ha hb
    refine ⟨right z.val z.property, hn, hs, hh, hh.tsum_eq, ?_⟩
    simpa only [dynamicalZeta, traceSum, traceTerm, continuation, (algebra z.val).1,
      one_div] using he
  · intro z hz
    have han : AnalyticAt ℂ (fun z : ℂ => 1 - z - z ^ 2) z := by fun_prop
    simp_rw [show ∀ w : ℂ, Matrix.det (1 - w • adjacency) = 1 - w - w ^ 2
      from fun w => (algebra w).1]
    apply AnalyticAt.neg
    apply han.clog
    apply Complex.mem_slitPlane_iff.mpr
    apply Or.inl
    simpa only [(algebra z).1] using right z hz

#print axioms det_vieta
#print axioms summable_norm_log_terms
#print axioms log_pair
#print axioms matrix_trace_log
#print axioms golden_local

end D5.S3.Analytic.Characterizations.GoldenTraceLog
