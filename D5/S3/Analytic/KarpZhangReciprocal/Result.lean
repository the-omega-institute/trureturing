/- GID: D5/S3/Analytic/KarpZhangReciprocal/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangReciprocal/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abel reduction proves the reciprocal-Pochhammer half for every log-concave sequence. -/

import D5.S3.Analytic.KarpZhangReciprocal.IntervalConvolution

/-!
admission_basis: escape-witness
content theorem: reciprocal_half, through ratio_bound and IntervalConvolution.shift_tail.
escape_witness: The interval-support condition gives positivity between endpoints. The
ratio_bound induction then propagates adjacent log-concavity to distant
successive ratios and balanced_step. Finite Abel summation expresses delta
as a nonnegative combination of symmetric tails. The source nontriviality
and exact zero-support convention are retained.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* IsLogConcave: proof_shape: bind-only (definition); escape_witness: none;
  consumers: KarpZhangConjecture.Result.claim, KarpZhangConjecture.Result.result, KarpZhangGamma.Result.two_variable_nonneg, KarpZhangGamma.Series.gamma_half, KarpZhangGamma.Smoothing.balanced_product, KarpZhangGamma.Smoothing.binomial_minor, KarpZhangGamma.Smoothing.smoothed_weighting, KarpZhangGamma.Smoothing.smoothing_minor, balanced_step, positive_between, ratio_bound, reciprocal_half.
* delta: proof_shape: bind-only (definition); escape_witness: none;
  consumers: KarpZhangConjecture.Result.claim, KarpZhangConjecture.Result.result, abel_reduction, reciprocal_half.
* increment: proof_shape: bind-only (definition); escape_witness: none;
  consumers: abel_layers, abel_reduction, layers, telescope.
* positive_between: proof_shape: bind-only; escape_witness: none;
  consumers: balanced_step, ratio_bound.
* ratio_bound: proof_shape: content; escape_witness: ratio_bound;
  consumers: balanced_step.
* balanced_step: proof_shape: content; escape_witness: ratio_bound;
  consumers: KarpZhangGamma.Smoothing.balanced_product, reciprocal_half.
* telescope: proof_shape: bind-only; escape_witness: none;
  consumers: layers.
* layers: proof_shape: bind-only; escape_witness: none;
  consumers: abel_layers.
* tail_sum: proof_shape: bind-only; escape_witness: none;
  consumers: abel_layers.
* abel_layers: proof_shape: bind-only; escape_witness: none;
  consumers: abel_reduction.
* abel_reduction: proof_shape: bind-only; escape_witness: none;
  consumers: reciprocal_half.
* reciprocal_half: proof_shape: content; escape_witness: KarpZhangReciprocal.IntervalConvolution.score_variance_bound;
  consumers: KarpZhangConjecture.Result.result.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
* F1: GID D5/S3/Analytic/KummerRatio/Defs.kummerCoeff;
  declaration statement_id:
  sha256:2ada6e56e131a4bdb7cccbc60aec3a351bc0b05a8b9544c75077cb676503abe7.
* F2: GID D5/S3/Analytic/KummerRatio/Series.coeff_succ;
  declaration statement_id:
  sha256:65529d42eed8f7a2af577c9bed21aaa15e926d5c89a7a18bc06b6b51c9936da9.
Per-declaration live-path dependencies (F labels above; omitted declarations: none):
* KarpZhangReciprocal.Result.reciprocal_half: F1, F2.
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

namespace D5.S3.Analytic.KarpZhangReciprocal.Result

open Coeff IntervalConvolution

/-- Definition 1.1 of Karp--Zhang, with its precise zero-support convention. -/
def IsLogConcave (y : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ y k) ∧
  (∃ k, y k ≠ 0) ∧
  (∀ k, 1 ≤ k → y (k - 1) * y (k + 1) ≤ y k ^ 2) ∧
  (∀ N, y N = 0 → (∀ i, y (N + i) = 0) ∨ (∀ i ≤ N, y (N - i) = 0))

/-- The degree-`m` coefficient of the difference of the two formal Cauchy products.
This finite definition needs no convergence or growth hypothesis on `y`. -/
def delta (y : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), y k * y (m - k) *
    (c k (μ + α) * c (m - k) (μ + β) - c k μ * c (m - k) (μ + α + β))

def increment (W : ℕ → ℝ) (q : ℕ) : ℝ :=
  if q = 0 then W 0 else W q - W (q - 1)

private theorem positive_between {y : ℕ → ℝ} (hy : IsLogConcave y)
    {a b i : ℕ} (ha : 0 < y a) (hb : 0 < y b) (hai : a ≤ i) (hib : i ≤ b) :
    0 < y i := by
  by_contra h
  have hz : y i = 0 := le_antisymm (le_of_not_gt h) (hy.1 i)
  rcases hy.2.2.2 i hz with hright | hleft
  · have he := hright (b - i)
    rw [show i + (b - i) = b by omega] at he
    exact (ne_of_gt hb) he
  · have he := hleft (i - a) (Nat.sub_le i a)
    have hidx : i - (i - a) = a := Nat.sub_sub_self hai
    rw [hidx] at he
    exact (ne_of_gt ha) he

private theorem ratio_bound {y : ℕ → ℝ} (hy : IsLogConcave y)
    (a n : ℕ) (ha : 0 < y a) (hb : 0 < y (a + n + 1)) :
    y (a + n + 1) / y (a + n) ≤ y (a + 1) / y a := by
  revert hb
  induction n with
  | zero => intro hb; simp only [Nat.add_zero, le_refl]
  | succ n ih =>
    intro hb
    have hmid : 0 < y (a + n + 1) :=
      positive_between hy ha hb (by omega) (by omega)
    have hprev : 0 < y (a + n) :=
      positive_between hy ha hb (by omega) (by omega)
    have hlocal := hy.2.2.1 (a + n + 1) (by omega)
    have hpred : a + n + 1 - 1 = a + n := Nat.add_succ_sub_one (a + n) 0
    have hsucc : a + n + 1 + 1 = a + (n + 1) + 1 := Nat.add_right_comm (a + n) 1 1
    rw [hpred, hsucc] at hlocal
    have hstep : y (a + (n + 1) + 1) / y (a + (n + 1)) ≤
        y (a + n + 1) / y (a + n) := by
      apply (div_le_div_iff₀ (by simpa only [Nat.add_assoc] using hmid) hprev).2
      calc
        y (a + (n + 1) + 1) * y (a + n) =
            y (a + n) * y (a + (n + 1) + 1) := mul_comm _ _
        _ ≤ y (a + n + 1) ^ 2 := hlocal
        _ = y (a + n + 1) * y (a + (n + 1)) := by
          rw [← Nat.add_assoc a n 1, pow_two]
    exact hstep.trans (ih hmid)

theorem balanced_step {y : ℕ → ℝ} (hy : IsLogConcave y)
    (m k : ℕ) (hk : k < m / 2) :
    y k * y (m - k) ≤ y (k + 1) * y (m - (k + 1)) := by
  have hnonneg := mul_nonneg (hy.1 k) (hy.1 (m - k))
  by_cases hz : y k * y (m - k) = 0
  · rw [hz]
    exact mul_nonneg (hy.1 _) (hy.1 _)
  · have hw : 0 < y k * y (m - k) := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have ha : 0 < y k := pos_of_mul_pos_left hw (hy.1 _)
    have hb : 0 < y (m - k) := (pos_iff_pos_of_mul_pos hw).mp ha
    let n := m - k - 1 - k
    have h1 : k + n = m - (k + 1) := by dsimp [n]; omega
    have h2 : k + n + 1 = m - k := by dsimp [n]; omega
    have hrat := ratio_bound hy k n ha (by simpa only [h2] using hb)
    rw [h2, h1] at hrat
    have hc : 0 < y (m - (k + 1)) :=
      positive_between hy ha hb (by omega) (by omega)
    have hcross := (div_le_div_iff₀ hc ha).mp hrat
    nlinarith

private theorem telescope (W : ℕ → ℝ) (j : ℕ) :
    ∑ q ∈ range (j + 1), increment W q = W j := by
  simpa only [increment] using (Finset.eq_sum_range_sub' W j).symm

private theorem layers (y : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    y k * y (m - k) =
      ∑ q ∈ range (m / 2 + 1),
        if q ≤ k ∧ q ≤ m - k then increment (fun i => y i * y (m - i)) q else 0 := by
  let j := min k (m - k)
  have hj : j ≤ m / 2 := by dsimp [j]; omega
  have hfilter : (range (m / 2 + 1)).filter (fun q => q ≤ k ∧ q ≤ m - k) =
      range (j + 1) := by
    ext q
    simp only [mem_filter, mem_range]
    dsimp [j] at *
    omega
  rw [← sum_filter, hfilter, telescope]
  dsimp [j]
  by_cases h : k ≤ m - k
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega : m - k ≤ k),
      show m - (m - k) = k by omega, mul_comm]

theorem tail_sum (K : ℕ → ℝ) (m q : ℕ) (hq : 2 * q ≤ m) :
    (∑ k ∈ range (m + 1), if q ≤ k ∧ q ≤ m - k then K k else 0) =
      ∑ i ∈ range (m - q - q + 1), K (q + i) := by
  rw [← sum_filter]
  apply sum_bij (fun k _ => k - q)
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    omega
  · intro k hk l hl hkl
    simp only [mem_filter, mem_range] at hk hl
    omega
  · intro i hi
    have hi' := mem_range.mp hi
    refine ⟨q + i, ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      omega
    · omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    congr 1
    omega

theorem abel_layers (y K : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m + 1), y k * y (m - k) * K k) =
      ∑ q ∈ range (m / 2 + 1), increment (fun i => y i * y (m - i)) q *
        (∑ i ∈ range (m - q - q + 1), K (q + i)) := by
  calc
    _ = ∑ k ∈ range (m + 1), ∑ q ∈ range (m / 2 + 1),
        if q ≤ k ∧ q ≤ m - k then
          increment (fun i => y i * y (m - i)) q * K k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [layers y m k (Nat.le_of_lt_succ (mem_range.mp hk)), sum_mul]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp only [zero_mul]
    _ = ∑ q ∈ range (m / 2 + 1), ∑ k ∈ range (m + 1),
        if q ≤ k ∧ q ≤ m - k then
          increment (fun i => y i * y (m - i)) q * K k else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      have hq' : 2 * q ≤ m := by have := mem_range.mp hq; omega
      rw [← tail_sum K m q hq', mul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp only [mul_zero]

/-- Finite Abel summation in terms of symmetric convolution tails. No sequence
hypotheses are needed for this identity, and the central index is counted once. -/
theorem abel_reduction (y : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) :
    delta y μ α β m =
      y 0 * y m * (F m 0 m (μ + α) (μ + β) - F m 0 m μ (μ + α + β)) +
      ∑ q ∈ range (m / 2),
        (y (q + 1) * y (m - (q + 1)) - y q * y (m - q)) *
          (F m (q + 1) (m - (q + 1)) (μ + α) (μ + β) -
            F m (q + 1) (m - (q + 1)) μ (μ + α + β)) := by
  let K := fun k => c k (μ + α) * c (m - k) (μ + β) -
    c k μ * c (m - k) (μ + α + β)
  have htail (q : ℕ) : (∑ i ∈ range (m - q - q + 1), K (q + i)) =
      F m q (m - q) (μ + α) (μ + β) - F m q (m - q) μ (μ + α + β) := by
    simp only [K, F, sum_sub_distrib]
  change (∑ k ∈ range (m + 1), y k * y (m - k) * K k) = _
  rw [abel_layers]
  simp_rw [htail]
  rw [sum_range_succ']
  simp only [increment, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel, ite_true, Nat.sub_zero]
  ring

/-- The reciprocal-Pochhammer half of Karp--Zhang Conjecture 5.2, for arbitrary
real nonnegative shifts and every coefficient of the formal power series. -/
theorem reciprocal_half (y : ℕ → ℝ) (hy : IsLogConcave y)
    (μ : ℝ) (hμ : 0 < μ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ delta y μ α β m := by
  rw [abel_reduction]
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (hy.1 0) (hy.1 m))
      (sub_nonneg.mpr (shift_tail m 0 (by omega) hμ hα hβ))
  · apply sum_nonneg
    intro q hq
    have hq' := mem_range.mp hq
    exact mul_nonneg (sub_nonneg.mpr (balanced_step hy m q hq'))
      (sub_nonneg.mpr (shift_tail m (q + 1) (by omega) hμ hα hβ))

end D5.S3.Analytic.KarpZhangReciprocal.Result
