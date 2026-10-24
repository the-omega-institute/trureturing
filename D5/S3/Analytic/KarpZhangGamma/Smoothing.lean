/- GID: D5/S3/Analytic/KarpZhangGamma/Smoothing
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Smoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic, mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Algebra.BigOperators.Field]
   utility: none
   digest: Exponential smoothing preserves balanced minors in every finite coefficient degree. -/

import D5.S3.Analytic.KarpZhangGamma.Weighting
import D5.S3.Analytic.KarpZhangReciprocal.Result
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

/-!
admission_basis: escape-witness
content theorem: smoothing_minor, through binomial_minor.
escape_witness: simultaneous induction in the coefficient degree for every
pair of derivative indices. Pascal's identity expresses the next minor as
the sum of two current minors. At the adjacent-index boundary the first
minor vanishes by commutativity. The degree-zero invariant is supplied by
the existing Result.balanced_step, via balanced_product.
The recurrence replaces the finite Cauchy--Binet expansion with an entirely
finite induction proving the same coefficientwise inequality.
bind-only helpers and consumers: balanced_product -> binomial_minor;
binomialProduct_succ -> binomial_minor, Kernel.reciprocalGamma_sum;
binomialProduct_comm -> binomial_minor; productCoeff_eq -> smoothing_minor,
Kernel.reciprocalGamma_sum.
The content helper binomial_minor is consumed by smoothing_minor;
smoothed_weighting consumes smoothing_minor and Weighting.coefficientwise_weighting.
Direct frozen D5 dependencies: KarpZhangReciprocal.Result.IsLogConcave,
KarpZhangReciprocal.Result.balanced_step. General finite identities and
inequalities only; none of the four computational-content kinds applies.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Analytic.KarpZhangGamma.Smoothing

open D5.S3.Analytic.KarpZhangReciprocal.Result
open Weighting

/-- The factorial-scaled Cauchy coefficient of two exponential generating series. -/
def binomialProduct (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ r ∈ range (N + 1), (N.choose r : ℝ) * f r * g (N - r)

/-- The ordinary coefficient of the product of two exponential generating series. -/
def productCoeff (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ r ∈ range (N + 1), f r * g (N - r) /
    ((r.factorial : ℝ) * ((N - r).factorial : ℝ))

/-- General balancing, with both interior indices allowed on either side of the centre. -/
theorem balanced_product {y : ℕ → ℝ} (hy : IsLogConcave y)
    {L R u v : ℕ} (hLu : L ≤ u) (hLv : L ≤ v)
    (huR : u ≤ R) (hvR : v ≤ R) (hsum : u + v = L + R) :
    y L * y R ≤ y u * y v := by
  let m := L + R
  let j := min u v
  have hjL : L ≤ j := le_min hLu hLv
  have hjhalf : j ≤ m / 2 := by dsimp [j, m]; omega
  have hincr : ∀ d : ℕ, L + d ≤ m / 2 →
      y L * y (m - L) ≤ y (L + d) * y (m - (L + d)) := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.add_zero, le_refl]
    | succ d ih =>
      intro hd
      have hp := ih (by omega)
      have hstep := balanced_step hy m (L + d) (by omega)
      have hidx : L + (d + 1) = L + d + 1 := by omega
      rw [hidx]
      exact hp.trans hstep
  have hidx : L + (j - L) = j := by omega
  have h := hincr (j - L) (by omega)
  rw [hidx, show m - L = R by dsimp [m]; omega] at h
  have heq : y j * y (m - j) = y u * y v := by
    dsimp [j, m]
    by_cases huv : u ≤ v
    · rw [min_eq_left huv, show L + R - u = v by omega]
    · rw [min_eq_right (by omega : v ≤ u), show L + R - v = u by omega,
        mul_comm]
  rwa [heq] at h

/-- Pascal's identity as a finite Leibniz rule. -/
theorem binomialProduct_succ (f g : ℕ → ℝ) (N : ℕ) :
    binomialProduct f g (N + 1) =
      binomialProduct (fun r => f (r + 1)) g N +
        binomialProduct f (fun r => g (r + 1)) N := by
  let T : ℝ := ∑ r ∈ range N,
    (N.choose (r + 1) : ℝ) * f (r + 1) * g (N - (r + 1) + 1)
  have htail : (∑ r ∈ range (N + 1),
      (N.choose (r + 1) : ℝ) * f (r + 1) * g (N - r)) = T := by
    rw [sum_range_succ]
    simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N), Nat.cast_zero,
      zero_mul, add_zero]
    apply sum_congr rfl
    intro r hr
    rw [show N - r = N - (r + 1) + 1 by have := mem_range.mp hr; omega]
  have hleft : binomialProduct f g (N + 1) =
      binomialProduct (fun r => f (r + 1)) g N + T + f 0 * g (N + 1) := by
    unfold binomialProduct
    rw [sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    have hs : (∑ r ∈ range (N + 1),
        ((N + 1).choose (r + 1) : ℝ) * f (r + 1) * g (N + 1 - (r + 1))) =
        (∑ r ∈ range (N + 1), (N.choose r : ℝ) * f (r + 1) * g (N - r)) +
          ∑ r ∈ range (N + 1),
            (N.choose (r + 1) : ℝ) * f (r + 1) * g (N - r) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      rw [Nat.choose_succ_succ', Nat.cast_add,
        show N + 1 - (r + 1) = N - r by omega]
      ring
    rw [hs, htail]
  have hright : binomialProduct f (fun r => g (r + 1)) N = T + f 0 * g (N + 1) := by
    unfold binomialProduct
    rw [sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    rfl
  rw [hleft, hright]
  ring

private theorem binomialProduct_comm (f g : ℕ → ℝ) (N : ℕ) :
    binomialProduct f g N = binomialProduct g f N := by
  unfold binomialProduct
  rw [← sum_range_reflect (fun r => (N.choose r : ℝ) * f r * g (N - r)) (N + 1)]
  apply sum_congr rfl
  intro r hr
  have hr' : r ≤ N := Nat.le_of_lt_succ (mem_range.mp hr)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hr', show N - (N - r) = r by omega]
  ring

/-- Factorials convert the binomial coefficient to the usual Cauchy coefficient. -/
theorem productCoeff_eq (f g : ℕ → ℝ) (N : ℕ) :
    productCoeff f g N = binomialProduct f g N / (N.factorial : ℝ) := by
  unfold productCoeff binomialProduct
  rw [sum_div]
  apply sum_congr rfl
  intro r hr
  have hr' : r ≤ N := Nat.le_of_lt_succ (mem_range.mp hr)
  have hc : (N.choose r : ℝ) * (r.factorial : ℝ) * ((N - r).factorial : ℝ) =
      (N.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hr'
  have hf : (N.factorial : ℝ) ≠ 0 := by positivity
  have hrz : (r.factorial : ℝ) ≠ 0 := by positivity
  have hnr : ((N - r).factorial : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff (mul_ne_zero hrz hnr) hf).2
  rw [← hc]
  ring

private theorem binomial_minor {y : ℕ → ℝ} (hy : IsLogConcave y) (N : ℕ) :
    ∀ p q : ℕ, p ≤ q + 1 →
      binomialProduct (fun r => y (p + r)) (fun r => y (q + 2 + r)) N ≤
        binomialProduct (fun r => y (p + 1 + r)) (fun r => y (q + 1 + r)) N := by
  induction N with
  | zero =>
    intro p q hpq
    simp only [binomialProduct, sum_range_one, Nat.choose_self, Nat.cast_one,
      Nat.add_zero, Nat.sub_zero, one_mul]
    by_cases heq : p = q + 1
    · subst p
      simpa only [show q + 1 + 1 = q + 2 by omega] using
        (le_of_eq (mul_comm (y (q + 1)) (y (q + 2))))
    · exact balanced_product hy (L := p) (R := q + 2) (u := p + 1) (v := q + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  | succ N ih =>
    intro p q hpq
    by_cases heq : p = q + 1
    · subst p
      simpa only [show q + 1 + 1 = q + 2 by omega] using
        (le_of_eq (binomialProduct_comm (fun r => y (q + 1 + r))
          (fun r => y (q + 2 + r)) (N + 1)))
    · have h1 := ih (p + 1) q (by omega)
      have h2 := ih p (q + 1) (by omega)
      simp only [binomialProduct_succ]
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h1 h2 ⊢
      linarith

/-- Lemma 3 in finite coefficient form: the degree-N coefficient of
P(p+1)P(q+1)-P(p)P(q+2) is nonnegative whenever p <= q+1. -/
theorem smoothing_minor {y : ℕ → ℝ} (hy : IsLogConcave y)
    (p q N : ℕ) (hpq : p ≤ q + 1) :
    productCoeff (fun r => y (p + r)) (fun r => y (q + 2 + r)) N ≤
      productCoeff (fun r => y (p + 1 + r)) (fun r => y (q + 1 + r)) N := by
  rw [productCoeff_eq, productCoeff_eq]
  exact div_le_div_of_nonneg_right (binomial_minor hy N p q hpq) (by positivity)

/-- The weights P(2k)P(2(m-k)) used by the transformed kernel are increasing.
This theorem combines Lemmas 1 and 3 and leaves only scalar kernel hypotheses. -/
theorem smoothed_weighting {y : ℕ → ℝ} (hy : IsLogConcave y)
    (A : ℕ → ℝ) (m : ℕ)
    (hsign : ∀ i ≤ m / 2, ∀ j ≤ m / 2, i < j → 0 < A i → 0 ≤ A j)
    (htotal : 0 ≤ ∑ i ∈ range (m / 2 + 1), A i) :
    ∀ N, 0 ≤ ∑ k ∈ range (m / 2 + 1), A k *
      productCoeff (fun r => y (2 * k + r)) (fun r => y (2 * (m - k) + r)) N := by
  apply coefficientwise_weighting A
    (fun k N => productCoeff (fun r => y (2 * k + r))
      (fun r => y (2 * (m - k) + r)) N) (m / 2) hsign htotal
  · intro N k _
    apply sum_nonneg
    intro r _
    exact div_nonneg (mul_nonneg (hy.1 _) (hy.1 _)) (by positivity)
  · intro N i hi j hj hij
    have hstep : ∀ k, k < m / 2 →
        productCoeff (fun r => y (2 * k + r)) (fun r => y (2 * (m - k) + r)) N ≤
          productCoeff (fun r => y (2 * (k + 1) + r))
            (fun r => y (2 * (m - (k + 1)) + r)) N := by
      intro k hk
      let q := 2 * (m - k) - 2
      have hq : q + 2 = 2 * (m - k) := by dsimp [q]; omega
      have hq' : q = 2 * (m - (k + 1)) := by dsimp [q]; omega
      have hfirst := smoothing_minor hy (2 * k) q N (by dsimp [q]; omega)
      have hsecond := smoothing_minor hy (2 * k + 1) (q - 1) N
        (by dsimp [q]; omega)
      have hqm : q - 1 + 2 = q + 1 := by dsimp [q]; omega
      have hqm' : q - 1 + 1 = q := by dsimp [q]; omega
      rw [hqm, hqm'] at hsecond
      rw [hq] at hfirst
      have h := hfirst.trans hsecond
      rw [hq', show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at h
      exact h
    have hiter : ∀ d, i + d ≤ m / 2 →
        productCoeff (fun r => y (2 * i + r)) (fun r => y (2 * (m - i) + r)) N ≤
          productCoeff (fun r => y (2 * (i + d) + r))
            (fun r => y (2 * (m - (i + d)) + r)) N := by
      intro d
      induction d with
      | zero => intro _; simp only [Nat.add_zero, le_refl]
      | succ d ihd =>
        intro hd
        have h := (ihd (by omega)).trans (hstep (i + d) (by omega))
        simpa only [Nat.add_assoc] using h
    have h := hiter (j - i) (by omega)
    simpa only [show i + (j - i) = j by omega] using h

end D5.S3.Analytic.KarpZhangGamma.Smoothing
