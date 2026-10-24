/- GID: D5/S3/Analytic/KarpZhangCatalanPower/Interval
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangCatalanPower/Interval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Analytic/KarpZhangCatalanPower/Coeff, mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Reflected interval cancellation and positivity of Catalan-power convolution tails. -/

import D5.S3.Analytic.KarpZhangCatalanPower.Coeff
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Finite interval cancellation for the Catalan-power coefficients.

Search-before-prove covered D5 and pinned Mathlib for reflected intervals,
constant-sum convolution slices, balancing and convolution-tail positivity.
No theorem for these coefficient tails occurs in that searched scope.
The finite sums use Finset.sum_bij, Finset.sum_sigma' and
Finset.sum_sdiff_sub_sum_sdiff; the passage from the positive derivative
to strict monotonicity uses strictMonoOn_of_deriv_pos.

The boundary set R is the nonnegative-integer realization of
[max(0,q-j), min(q-1,m-q-j)], with the upper endpoint interpreted in the
integers. The filter keeps the interval empty when that endpoint is negative.

admission_basis: escape-witness; witness: slice_strictMonoOn.
utility none: the results quantify over arbitrary degrees, interval cutoffs
and real parameters. No finite numerical certificate or enumerator is used.
-/

noncomputable section
open Finset
open D5.S3.Analytic.KarpZhangCatalanPower.Coeff
open D5.S3.Analytic.KarpZhangCatalanPower.Index
namespace D5.S3.Analytic.KarpZhangCatalanPower.Interval

/- proof_shape: bind-only definition; escape_witness: none;
consumer: derivative_difference, left_derivative_reindex, left_reindex, mem_left,
reflected_interval. -/
private def leftWindow (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i + j ∧ i + j ≤ m - q

/- proof_shape: bind-only definition; escape_witness: none;
consumer: derivative_difference, mem_right, reflected_interval, right_derivative_reindex,
right_reindex. -/
private def rightWindow (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i ∧ i ≤ m - q

/- proof_shape: bind-only definition; escape_witness: none;
consumer: R_lt, R_one, derivative_difference, mem_R, reflected_interval, sliceDerivative,
sliceDerivative_pos. -/
/-- The left-only part of a pair of reflected truncated intervals. -/
def R (m q j : ℕ) : Finset ℕ :=
  (range (m - j + 1)).filter fun i => q ≤ i + j ∧ i + j ≤ m - q ∧ i < q

/- proof_shape: bind-only; escape_witness: none;
consumer: left_reindex, reflected_interval. -/
private lemma mem_left {m q j i : ℕ} : i ∈ leftWindow m q j ↔
    i ≤ m - j ∧ q ≤ i + j ∧ i + j ≤ m - q := by
  simp only [leftWindow, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none;
consumer: reflected_interval, right_reindex. -/
private lemma mem_right {m q j i : ℕ} : i ∈ rightWindow m q j ↔
    i ≤ m - j ∧ q ≤ i ∧ i ≤ m - q := by
  simp only [rightWindow, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none;
consumer: R_lt, R_one, derivative_difference, reflected_interval. -/
private lemma mem_R {m q j i : ℕ} : i ∈ R m q j ↔
    i ≤ m - j ∧ q ≤ i + j ∧ i + j ≤ m - q ∧ i < q := by
  simp only [R, mem_filter, mem_range, Nat.lt_succ_iff]

/- proof_shape: bind-only; escape_witness: none;
consumer: sliceDerivative_pos. -/
private lemma R_lt {m q j i : ℕ} (hmq : 2 * q ≤ m) (hj : j ≤ m)
    (hi : i ∈ R m q j) : i < m - j - i := by
  rw [mem_R] at hi
  omega

/- proof_shape: bind-only; escape_witness: none;
consumer: derivative_difference. -/
lemma reflected_interval {m q j : ℕ} (hmq : 2 * q ≤ m) (hj : j ≤ m)
    (w : ℕ → ℝ) :
    (∑ i ∈ (range (m - j + 1)).filter (fun i => q ≤ i + j ∧ i + j ≤ m - q), w i) -
      (∑ i ∈ (range (m - j + 1)).filter (fun i => q ≤ i ∧ i ≤ m - q), w i) =
      ∑ i ∈ R m q j, (w i - w (m - j - i)) := by
  change (∑ i ∈ leftWindow m q j, w i) - (∑ i ∈ rightWindow m q j, w i) = _
  have hl : leftWindow m q j \ rightWindow m q j = R m q j := by
    ext i
    simp only [mem_sdiff, mem_left, mem_right, mem_R]
    omega
  have hr : ∑ i ∈ rightWindow m q j \ leftWindow m q j, w i =
      ∑ i ∈ R m q j, w (m - j - i) := by
    apply sum_bij (fun i _ => m - j - i)
    · intro i hi
      simp only [mem_sdiff, mem_right, mem_left] at hi
      rw [mem_R]
      omega
    · intro i hi k hk hik
      simp only [mem_sdiff, mem_right, mem_left] at hi hk
      omega
    · intro i hi
      rw [mem_R] at hi
      refine ⟨m - j - i, ?_, ?_⟩
      · simp only [mem_sdiff, mem_right, mem_left]
        omega
      · omega
    · intro i hi
      simp only [mem_sdiff, mem_right, mem_left] at hi
      congr 1
      omega
  rw [sum_sub_distrib, ← hr, ← hl]
  exact (sum_sdiff_sub_sum_sdiff).symm

/- proof_shape: bind-only; escape_witness: none;
consumer: left_derivative_reindex. -/
private lemma left_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 k, F j (k - j)) =
      ∑ j ∈ Icc 1 m, ∑ i ∈ leftWindow m q j, F j i := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => (⟨p.2, p.1 - p.2⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [mem_sigma, mem_Icc] at hp
    simp only [mem_sigma, mem_Icc, mem_left]
    omega
  · intro p hp r hr hpr
    simp only [mem_sigma, mem_Icc] at hp hr
    have h1 := congrArg Sigma.fst hpr
    have h2 := congrArg Sigma.snd hpr
    dsimp only at h1 h2
    exact Sigma.ext (by omega) (by simpa only [heq_eq_eq] using h1)
  · intro p hp
    simp only [mem_sigma, mem_Icc, mem_left] at hp
    refine ⟨⟨p.2 + p.1,p.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc]
      omega
    · simp
  · intro p hp
    rfl

/- proof_shape: bind-only; escape_witness: none;
consumer: right_derivative_reindex. -/
private lemma right_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 (m - k), F j k) =
      ∑ j ∈ Icc 1 m, ∑ i ∈ rightWindow m q j, F j i := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => (⟨p.2,p.1⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [mem_sigma, mem_Icc] at hp
    simp only [mem_sigma, mem_Icc, mem_right]
    omega
  · intro p hp r hr hpr
    have h1 := congrArg Sigma.fst hpr
    have h2 := congrArg Sigma.snd hpr
    dsimp only at h1 h2
    exact Sigma.ext h2 (by simpa only [heq_eq_eq] using h1)
  · intro p hp
    simp only [mem_sigma, mem_Icc, mem_right] at hp
    refine ⟨⟨p.2,p.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_Icc]
      omega
    · rfl
  · intro p hp
    rfl

/- proof_shape: bind-only definition; escape_witness: none;
consumer: Z_symm, balancing, hasDerivAt_slice, slice_strictMonoOn. -/
/-- The central convolution interval. -/
def Z (m q : ℕ) (u v : ℝ) : ℝ := ∑ k ∈ Icc q (m - q), a k u * a (m - k) v

/- proof_shape: bind-only definition; escape_witness: none;
consumer: derivative_difference, hasDerivAt_slice, sliceDerivative_pos, slice_strictMonoOn. -/
/-- The reflected determinant expression for a constant-sum derivative. -/
def sliceDerivative (m q : ℕ) (u v : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 m, b j * ∑ i ∈ R m q j,
    (a i u * a (m - j - i) v - a (m - j - i) u * a i v)

/- proof_shape: bind-only; escape_witness: none;
consumer: derivative_difference. -/
private lemma left_derivative_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), (∑ j ∈ Icc 1 k, b j * a (k - j) u) * a (m - k) v) =
      ∑ j ∈ Icc 1 m, b j * ∑ i ∈ leftWindow m q j, a i u * a (m - j - i) v := by
  calc
    _ = ∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 k,
          b j * (a (k - j) u * a (m - j - (k - j)) v) := by
      apply sum_congr rfl
      intro k hk
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      simp only [mem_Icc] at hk hj
      rw [show m - j - (k - j) = m - k by omega]
      ring
    _ = _ := by
      rw [left_reindex hmq (fun j i => b j * (a i u * a (m - j - i) v))]
      simp only [mul_sum]

/- proof_shape: bind-only; escape_witness: none;
consumer: derivative_difference. -/
private lemma right_derivative_reindex {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), a k u * (∑ j ∈ Icc 1 (m - k), b j * a (m - k - j) v)) =
      ∑ j ∈ Icc 1 m, b j * ∑ i ∈ rightWindow m q j, a i u * a (m - j - i) v := by
  calc
    _ = ∑ k ∈ Icc q (m - q), ∑ j ∈ Icc 1 (m - k),
          b j * (a k u * a (m - j - k) v) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [show m - k - j = m - j - k by omega]
      ring
    _ = _ := by
      rw [right_reindex hmq]
      simp only [mul_sum]

/- proof_shape: bind-only; escape_witness: none;
consumer: hasDerivAt_slice. -/
private lemma derivative_difference {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) :
    (∑ k ∈ Icc q (m - q), (∑ j ∈ Icc 1 k, b j * a (k - j) u) * a (m - k) v) -
    (∑ k ∈ Icc q (m - q), a k u * (∑ j ∈ Icc 1 (m - k), b j * a (m - k - j) v)) =
      sliceDerivative m q u v := by
  rw [left_derivative_reindex hmq, right_derivative_reindex hmq]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp only [mem_Icc] at hj
  rw [← mul_sub]
  unfold leftWindow rightWindow
  rw [reflected_interval hmq hj.2]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi0 := (mem_R.mp hi).1
  rw [show m - j - (m - j - i) = i by omega]

/- proof_shape: bind-only; escape_witness: none;
consumer: slice_strictMonoOn. -/
lemma hasDerivAt_slice
    {m q : ℕ} (hmq : 2 * q ≤ m) {S r : ℝ} (hr : 0 < r) (hv : 0 < S - r) :
    HasDerivAt (fun r => Z m q r (S - r)) (sliceDerivative m q r (S - r)) r := by
  have H := HasDerivAt.fun_sum (u := Icc q (m - q)) (fun k _ =>
    (hasDerivAt_a k hr.le).mul ((hasDerivAt_a (m - k) hv.le).comp r
      ((hasDerivAt_const r S).sub (hasDerivAt_id r))))
  change HasDerivAt (fun r => Z m q r (S - r)) _ r at H
  convert H using 1
  simp only [Function.comp_apply, mul_neg_one, zero_sub]
  rw [← derivative_difference hmq]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: sliceDerivative_pos. -/
private lemma R_one {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) :
    q - 1 ∈ R m q 1 := by
  rw [mem_R]
  omega

/- proof_shape: content; escape_witness: Coeff.tp2;
consumer: slice_strictMonoOn. -/
private lemma sliceDerivative_pos
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < sliceDerivative m q u v := by
  apply sum_pos'
  · intro j hj
    simp only [mem_Icc] at hj
    apply mul_nonneg (b_pos j (by omega)).le
    apply sum_nonneg
    intro i hi
    exact sub_nonneg.mpr (tp2_le hu huv.le (R_lt hmq hj.2 hi))
  · refine ⟨1, by simp only [mem_Icc]; omega, ?_⟩
    apply mul_pos (b_pos 1 (by omega))
    apply sum_pos'
    · intro i hi
      exact (sub_pos.mpr (tp2 hu huv (R_lt hmq (by omega) hi))).le
    · exact ⟨q - 1,R_one hq hmq,
        sub_pos.mpr (tp2 hu huv (R_lt hmq (by omega) (R_one hq hmq)))⟩

/- proof_shape: bind-only; escape_witness: none;
consumer: balancing. -/
lemma Z_symm {m q : ℕ} (hmq : 2 * q ≤ m) (u v : ℝ) : Z m q u v = Z m q v u := by
  unfold Z
  simp only [← Finset.Ico_succ_right_eq_Icc, Nat.succ_eq_succ, Nat.succ_eq_add_one]
  have h := Finset.sum_Ico_reflect (fun k => a k v * a (m - k) u) q
    (m := m - q + 1) (n := m) (by omega)
  have hlo : m + 1 - (m - q + 1) = q := by omega
  have hhi : m + 1 - q = m - q + 1 := by omega
  rw [hlo, hhi] at h
  rw [h.symm]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_Ico.mp hk
  rw [Nat.sub_sub_self (by omega : k ≤ m)]
  exact mul_comm _ _


/- proof_shape: content; escape_witness: sliceDerivative_pos;
consumer: balancing. -/
lemma slice_strictMonoOn
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {S : ℝ} (hS : 0 < S) :
    StrictMonoOn (fun r => Z m q r (S - r)) (Set.Ioc 0 (S / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (S / 2))
  · intro r hr
    have hv : 0 < S - r := by linarith [hr.2]
    exact (hasDerivAt_slice hmq hr.1 hv).continuousAt.continuousWithinAt
  · intro r hr
    simp only [interior_Ioc, Set.mem_Ioo] at hr
    have hv : 0 < S - r := by linarith [hr.2]
    rw [(hasDerivAt_slice hmq hr.1 hv).deriv]
    exact sliceDerivative_pos hq hmq hr.1 (by linarith [hr.2])

/- proof_shape: content; escape_witness: slice_strictMonoOn;
consumer: tail_nonneg. -/
private lemma balancing
    {m q : ℕ} (hq : 1 ≤ q) (hmq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Z m q μ (μ + α + β) ≤ Z m q (μ + α) (μ + β) := by
  let S := 2 * μ + α + β
  have hS : 0 < S := by dsimp [S]; linarith
  have hmono := (slice_strictMonoOn hq hmq hS).monotoneOn
  by_cases hab : α ≤ β
  · have h := hmono (show μ∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith)
      (show μ + α∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith) (by linarith : μ ≤ μ + α)
    simpa only [show S - μ = μ + α + β by dsimp [S]; ring,
      show S - (μ + α) = μ + β by dsimp [S]; ring] using h
  · have h := hmono (show μ∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith)
      (show μ + β∈Set.Ioc 0 (S / 2) by dsimp [S]; constructor <;> linarith) (by linarith : μ ≤ μ + β)
    dsimp only at h
    rw [show S - μ = μ + α + β by dsimp [S]; ring,
      show S - (μ + β) = μ + α by dsimp [S]; ring] at h
    exact h.trans_eq (Z_symm hmq (μ + β) (μ + α))

/- proof_shape: content; escape_witness: balancing;
consumer: later Abel reduction. -/
lemma tail_nonneg
    {m q : ℕ} (hmq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ ∑ k ∈ Icc q (m - q),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)) := by
  by_cases hq0 : q = 0
  · subst q
    rw [Nat.sub_zero, ← Nat.range_succ_eq_Icc_zero, sum_sub_distrib,
      index_law (μ + α) (μ + β) m (by linarith) (by linarith),
      index_law μ (μ + α + β) m hμ (by linarith)]
    have he : μ + α + (μ + β) = μ + (μ + α + β) := by ring
    simp only [he, sub_self, le_refl]
  · have hq : 1 ≤ q := by omega
    rcases hμ.eq_or_lt with rfl | hμ
    · apply sum_nonneg
      intro k hk
      simp only [mem_Icc] at hk
      rw [a_zero_parameter (by omega)]
      simp only [zero_add, zero_mul, sub_zero]
      exact mul_nonneg (a_nonneg k hα) (a_nonneg (m - k) hβ)
    · rw [sum_sub_distrib]
      exact sub_nonneg.mpr (balancing hq hmq hμ hα hβ)

end D5.S3.Analytic.KarpZhangCatalanPower.Interval
