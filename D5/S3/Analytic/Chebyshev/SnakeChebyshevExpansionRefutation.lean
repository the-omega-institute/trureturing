/- GID: D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.claim; result=D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.result; claim=D5/S3/Analytic/Chebyshev/SnakeChebyshevExpansionRefutation.claim
   digest: An even convex majorant has a degree-six snake with a negative Chebyshev coefficient. -/

/- Source: Kryvonos (ed.), arXiv:2312.07754,
   "Snake polynomials with positive Chebyshev expansions" (G. Nikolov);
   UP24, arXiv:2504.04845, Conjecture 7.1.
   admission_basis: open-problem-resolution (#15634; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Reuse: convexOn_norm, convexOn_const, ConvexOn.smul, ConvexOn.add_const,
     ConvexOn.sup, Continuous.max, continuous_abs,
     Fin.strictAnti_iff_succ_lt, Chebyshev.T_add_two, Chebyshev.T_zero,
     Chebyshev.T_one, Chebyshev.T_two, Polynomial.coeff_C_mul,
     Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X.
   Definitions:
     IsSnake: proof_shape definition; consumers=claim, P_snake
     claim: proof_shape definition; consumer=result
     μ: proof_shape definition; consumers=μ_continuous, μ_nonneg, μ_even,
       μ_convex, P_bound_nonneg, P_bound, P_snake, result
     P: proof_shape definition; consumers=P_eval, P_even, P_degree,
       P_bound_small, P_bound_large, P_bound_nonneg, P_bound, P_snake,
       constant_coefficient_negative, result
   Per-declaration proof_shape and live consumers:
     μ_continuous: bind-only; consumer=result
     μ_nonneg: bind-only; consumer=result
     μ_even: bind-only; consumers=P_bound, result
     μ_convex: bind-only; consumer=result
     P_eval: bind-only; consumers=P_even, P_bound_small, P_bound_large, P_snake
     P_even: bind-only; consumer=P_bound
     P_degree: bind-only; consumer=P_snake
     P_bound_small: content; consumer=P_bound_nonneg
     P_bound_large: content; consumer=P_bound_nonneg
     P_bound_nonneg: content; consumer=P_bound
     P_bound: content; consumer=P_snake
     P_snake: content; consumer=result
     constant_coefficient_negative: bind-only; consumer=result
     result: content; designated refutation conclusion
   The two interval certificates bound the snake by the majorant. Its seven
   ordered contact points alternate in sign. Comparing the even power
   coefficients forces the constant Chebyshev coefficient to be -459/274. -/

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace D5.S3.Analytic.Chebyshev.SnakeChebyshevExpansionRefutation
open Polynomial

/-- `ω` is an `n`-th snake polynomial of the majorant `μ` on `[-1, 1]`. -/
def IsSnake (μ : ℝ → ℝ) (n : ℕ) (ω : ℝ[X]) : Prop :=
  ω.natDegree ≤ n ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |ω.eval x| ≤ μ x) ∧
    ∃ τ : Fin (n + 1) → ℝ, StrictAnti τ ∧ τ 0 ≤ 1 ∧ -1 ≤ τ (Fin.last n) ∧
      ∀ i : Fin (n + 1), ω.eval (τ i) = (-1) ^ (i : ℕ) * μ (τ i)

def claim : Prop :=
  ∀ μ : ℝ → ℝ, ContinuousOn μ (Set.Icc (-1) 1) → (∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ μ x) →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, μ (-x) = μ x) → ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) μ →
    ∀ (n : ℕ) (ω : ℝ[X]), IsSnake μ n ω →
      ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧
        ω = ∑ k ∈ Finset.range (n + 1), C (a k) * Chebyshev.T ℝ (k : ℤ)

private def μ (x : ℝ) : ℝ := max 1 ((4860 * |x| - 1078) / 137)

private def P : ℝ[X] :=
  C (1 / 137) * (38656 * X ^ 6 - 41568 * X ^ 4 + 6831 * X ^ 2 - 137)

private lemma μ_continuous : Continuous μ := by
  unfold μ
  exact continuous_const.max
    (((continuous_const.mul continuous_abs).sub continuous_const).div_const 137)

private lemma μ_nonneg (x : ℝ) : 0 ≤ μ x :=
  le_trans (by norm_num) (le_max_left _ _)

private lemma μ_even (x : ℝ) : μ (-x) = μ x := by
  simp [μ]

private lemma μ_convex : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) μ := by
  have habs : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun x : ℝ => |x|) := by
    simpa only [Real.norm_eq_abs] using! (convexOn_norm (convex_Icc (-1 : ℝ) 1))
  have hlin := (habs.smul (show (0 : ℝ) ≤ 4860 / 137 by norm_num)).add_const
    (-(1078 / 137 : ℝ))
  have hmax := (convexOn_const (1 : ℝ) (convex_Icc (-1 : ℝ) 1)).sup hlin
  convert! hmax using 1
  funext x
  simp only [μ, Pi.sup_apply, Pi.add_apply, smul_eq_mul]
  congr 1
  ring

private lemma P_eval (x : ℝ) :
    P.eval x = (38656 * x ^ 6 - 41568 * x ^ 4 + 6831 * x ^ 2 - 137) / 137 := by
  simp [P]
  ring

private lemma P_even (x : ℝ) : P.eval (-x) = P.eval x := by
  rw [P_eval, P_eval]
  ring

private lemma P_degree : P.natDegree ≤ 6 := by
  unfold P
  compute_degree

private lemma P_bound_small (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 4) :
    |P.eval x| ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
  have hA : 0 ≤ 2416 * x ^ 4 - 2447 * x ^ 2 + 274 := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hB : 0 ≤ 38656 * x ^ 4 - 41568 * x ^ 2 + 6831 := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hm := mul_nonneg (mul_nonneg (show 0 ≤ 1 - 4 * x by linarith)
    (show 0 ≤ 1 + 4 * x by linarith)) hA
  have hp := mul_nonneg (sq_nonneg x) hB
  have em : 137 * (1 - P.eval x) =
      (1 - 4 * x) * (1 + 4 * x) * (2416 * x ^ 4 - 2447 * x ^ 2 + 274) := by
    rw [P_eval]
    ring
  have ep : 137 * (1 + P.eval x) =
      x ^ 2 * (38656 * x ^ 4 - 41568 * x ^ 2 + 6831) := by
    rw [P_eval]
    ring
  exact abs_le.mpr ⟨by nlinarith [ep], by nlinarith [em]⟩

private lemma P_bound_large (x : ℝ) (hx : 1 / 4 ≤ x) (hx' : x ≤ 1) :
    |P.eval x| ≤ (4860 * x - 1078) / 137 := by
  have hx0 : 0 ≤ x := by linarith
  have hA : 0 ≤ 9664 * x ^ 4 + 12080 * x ^ 3 + 2292 * x ^ 2 - 155 * x + 941 := by
    have h4 : 0 ≤ x ^ 4 := by positivity
    have h3 : 0 ≤ x ^ 3 := by positivity
    nlinarith [sq_nonneg x]
  have hshift : 0 ≤ (x - 1 / 4) *
      (2416 * x ^ 3 + 4228 * x ^ 2 + 2536 * x + 814) := by
    apply mul_nonneg (by linarith)
    positivity
  have eshift : (x - 1 / 4) *
      (2416 * x ^ 3 + 4228 * x ^ 2 + 2536 * x + 814) =
      (2416 * x ^ 4 + 3624 * x ^ 3 + 1479 * x ^ 2 + 180 * x - 135) - 137 / 2 := by
    ring
  have hB : 0 ≤ 2416 * x ^ 4 + 3624 * x ^ 3 + 1479 * x ^ 2 + 180 * x - 135 := by
    linarith
  have hm := mul_nonneg (mul_nonneg (show 0 ≤ 1 - x by linarith)
    (show 0 ≤ 4 * x - 1 by linarith)) hA
  have hp := mul_nonneg (sq_nonneg (4 * x - 3)) hB
  have em : 137 * ((4860 * x - 1078) / 137 - P.eval x) =
      (1 - x) * (4 * x - 1) *
        (9664 * x ^ 4 + 12080 * x ^ 3 + 2292 * x ^ 2 - 155 * x + 941) := by
    rw [P_eval]
    ring
  have ep : 137 * ((4860 * x - 1078) / 137 + P.eval x) =
      (4 * x - 3) ^ 2 *
        (2416 * x ^ 4 + 3624 * x ^ 3 + 1479 * x ^ 2 + 180 * x - 135) := by
    rw [P_eval]
    ring
  exact abs_le.mpr ⟨by nlinarith [ep], by nlinarith [em]⟩

private lemma P_bound_nonneg (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    |P.eval x| ≤ μ x := by
  by_cases hs : x ≤ 1 / 4
  · exact (P_bound_small x hx hs).trans (le_max_left _ _)
  · exact (P_bound_large x (le_of_not_ge hs) hx').trans
      (by simpa only [μ, abs_of_nonneg hx] using
        le_max_right (1 : ℝ) ((4860 * x - 1078) / 137))

private lemma P_bound (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |P.eval x| ≤ μ x := by
  by_cases h : 0 ≤ x
  · exact P_bound_nonneg x h hx.2
  · have h' := P_bound_nonneg (-x) (by linarith) (by linarith [hx.1])
    simpa only [P_even, μ_even] using h'

private lemma P_snake : IsSnake μ 6 P := by
  refine ⟨P_degree, P_bound, ![1, 3 / 4, 1 / 4, 0, -1 / 4, -3 / 4, -1], ?_, ?_, ?_, ?_⟩
  · apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · norm_num
  · norm_num [Fin.last]
  · intro i
    fin_cases i <;> norm_num [P_eval, μ]

private lemma constant_coefficient_negative (a : ℕ → ℝ)
    (h : P = ∑ k ∈ Finset.range 7, C (a k) * Chebyshev.T ℝ (k : ℤ)) :
    a 0 = -459 / 274 := by
  have t3 : Chebyshev.T ℝ 3 = 4 * X ^ 3 - 3 * X := by
    have ht := Chebyshev.T_add_two ℝ 1
    norm_num only at ht
    rw [ht, Chebyshev.T_two, Chebyshev.T_one]
    ring
  have t4 : Chebyshev.T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
    have ht := Chebyshev.T_add_two ℝ 2
    norm_num only at ht
    rw [ht, t3, Chebyshev.T_two]
    ring
  have t5 : Chebyshev.T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
    have ht := Chebyshev.T_add_two ℝ 3
    norm_num only at ht
    rw [ht, t4, t3]
    ring
  have t6 : Chebyshev.T ℝ 6 = 32 * X ^ 6 - 48 * X ^ 4 + 18 * X ^ 2 - 1 := by
    have ht := Chebyshev.T_add_two ℝ 4
    norm_num only at ht
    rw [ht, t5, t4]
    ring
  have h0 := congrArg (fun q : ℝ[X] => q.coeff 0) h
  have h2 := congrArg (fun q : ℝ[X] => q.coeff 2) h
  have h4 := congrArg (fun q : ℝ[X] => q.coeff 4) h
  have h6 := congrArg (fun q : ℝ[X] => q.coeff 6) h
  norm_num [Finset.sum_range_succ, P, t3, t4, t5, t6, Chebyshev.T_two, coeff_one, coeff_X] at h0 h2 h4 h6
  linarith

/-- Nikolov's nonnegative Chebyshev expansion claim fails for an even convex majorant. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨a, ha, he⟩ := hc μ μ_continuous.continuousOn (fun x _ => μ_nonneg x)
    (fun x _ => μ_even x) μ_convex 6 P P_snake
  have hneg := constant_coefficient_negative a he
  have hnonneg := ha 0
  linarith

end D5.S3.Analytic.Chebyshev.SnakeChebyshevExpansionRefutation
