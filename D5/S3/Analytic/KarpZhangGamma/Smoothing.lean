/- GID: D5/S3/Analytic/KarpZhangGamma/Smoothing
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Smoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential smoothing preserves balanced minors in every finite coefficient degree. -/

import D5.S3.Analytic.KarpZhangGamma.Weighting
import D5.S3.Analytic.KarpZhangReciprocal.Result

/-!
admission_basis: escape-witness
content theorem: smoothing_minor, through binomial_minor.
escape_witness: Simultaneous induction in coefficient degree for all derivative indices
preserves the balanced minor inequality. Pascal recurrence gives two
current minors; the adjacent-index boundary vanishes by commutativity.
The degree-zero step uses balanced_product and the same-delivery
KarpZhangReciprocal.Result.balanced_step. smoothed_weighting combines these
minors with Weighting.coefficientwise_weighting.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* binomialProduct: proof_shape: bind-only (definition); escape_witness: none;
  consumers: KarpZhangGamma.Kernel.binomialGamma_sum, KarpZhangGamma.Kernel.reciprocalGamma_sum, KarpZhangGamma.Result.two_variable_nonneg, binomialProduct_comm, binomialProduct_succ, binomial_minor, productCoeff_eq, smoothing_minor.
* productCoeff: proof_shape: bind-only (definition); escape_witness: none;
  consumers: KarpZhangGamma.Kernel.reciprocalGamma_sum, KarpZhangGamma.Result.transformDelta, KarpZhangGamma.Result.two_variable_nonneg, KarpZhangGamma.Series.transformed_delta, KarpZhangGamma.Series.transformed_product, productCoeff_eq, smoothed_weighting, smoothing_minor.
* balanced_product: proof_shape: content; escape_witness: KarpZhangReciprocal.Result.ratio_bound;
  consumers: binomial_minor.
* binomialProduct_succ: proof_shape: bind-only; escape_witness: none;
  consumers: binomial_minor.
* binomialProduct_comm: proof_shape: bind-only; escape_witness: none;
  consumers: KarpZhangGamma.Result.two_variable_nonneg, binomial_minor.
* productCoeff_eq: proof_shape: bind-only; escape_witness: none;
  consumers: KarpZhangGamma.Kernel.reciprocalGamma_sum, KarpZhangGamma.Result.two_variable_nonneg, smoothing_minor.
* binomial_minor: proof_shape: content; escape_witness: binomial_minor;
  consumers: smoothing_minor.
* smoothing_minor: proof_shape: content; escape_witness: binomial_minor;
  consumers: smoothed_weighting.
* smoothed_weighting: proof_shape: content; escape_witness: binomial_minor;
  consumers: KarpZhangGamma.Result.two_variable_nonneg.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
none.
All KarpZhang dependencies are same-delivery declarations.
Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
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
      have hidx : L + (d + 1) = L + d + 1 := (Nat.add_assoc L d 1).symm
      rw [hidx]
      exact hp.trans hstep
  have hidx : L + (j - L) = j := Nat.add_sub_of_le hjL
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
  have h := Finset.sum_choose_succ_mul (fun i j => f i * g j) N
  have hshift : (∑ r ∈ range (N + 1), (N.choose r : ℝ) * (f r * g (N + 1 - r))) =
      binomialProduct f (fun r => g (r + 1)) N := by
    unfold binomialProduct
    apply sum_congr rfl
    intro r hr
    rw [show N + 1 - r = N - r + 1 by have := mem_range.mp hr; omega]
    exact (mul_assoc _ _ _).symm
  rw [hshift] at h
  simpa only [binomialProduct, mul_assoc] using h.trans (add_comm _ _)

theorem binomialProduct_comm (f g : ℕ → ℝ) (N : ℕ) :
    binomialProduct f g N = binomialProduct g f N := by
  unfold binomialProduct
  rw [← sum_range_reflect (fun r => (N.choose r : ℝ) * f r * g (N - r)) (N + 1)]
  apply sum_congr rfl
  intro r hr
  have hr' : r ≤ N := Finset.mem_range_succ_iff.mp hr
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
  have hr' : r ≤ N := Finset.mem_range_succ_iff.mp hr
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
    simp only [binomialProduct, Nat.zero_add, sum_range_one, Nat.choose_self, Nat.cast_one,
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

/-- `smoothing_minor` in finite coefficient form: the degree-N coefficient of
P(p+1)P(q+1)-P(p)P(q+2) is nonnegative whenever p <= q+1. -/
theorem smoothing_minor {y : ℕ → ℝ} (hy : IsLogConcave y)
    (p q N : ℕ) (hpq : p ≤ q + 1) :
    productCoeff (fun r => y (p + r)) (fun r => y (q + 2 + r)) N ≤
      productCoeff (fun r => y (p + 1 + r)) (fun r => y (q + 1 + r)) N := by
  rw [productCoeff_eq, productCoeff_eq]
  exact div_le_div_of_nonneg_right (binomial_minor hy N p q hpq) (by positivity)

/-- The weights P(2k)P(2(m-k)) used by the transformed kernel are increasing.
This theorem combines `coefficientwise_weighting` and `smoothing_minor` and leaves only scalar kernel hypotheses. -/
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
      have hqm' : q - 1 + 1 = q := Nat.add_right_cancel (show (q - 1 + 1) + 1 = q + 1 by
        simpa only [Nat.add_assoc] using hqm)
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
