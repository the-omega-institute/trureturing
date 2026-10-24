/- GID: D5/S3/Analytic/KarpZhangCatalanPower/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangCatalanPower/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both coefficientwise assertions of Karp--Zhang Conjecture 4.2. -/

import D5.S3.Analytic.KarpZhangCatalanPower.Interval
import D5.S3.Analytic.KarpZhangReciprocal.Result

/-!
admission_basis: open-problem-resolution (#21083; Proved)
Per-declaration proof_shape:
* IsLogConvex: bind-only definition; escape_witness: none;
  consumers: zero_tail, positive_all, convex_ratio, convex_step, claim, result.
* delta: bind-only definition; escape_witness: none; consumers: abel, claim.
* zero_tail: content; escape_witness: zero_tail; consumers: convex_step.
* positive_all: content; escape_witness: positive_all; consumers: convex_ratio, convex_step.
* convex_ratio: content; escape_witness: convex_ratio; consumers: convex_step.
* convex_step: content; escape_witness: convex_ratio; consumers: result.
* abel: bind-only; escape_witness: none; consumers: result.
* tail: content; escape_witness: Interval.slice_strictMonoOn; consumers: result.
* full_tail: bind-only; escape_witness: none; consumers: result.
* claim: bind-only definition; escape_witness: none; consumers: result.
* result: content; escape_witness: Interval.slice_strictMonoOn;
  consumers: external Conjecture 4.2 settlement.
Supporting-module witnesses: Coeff.tp2 in Coeff;
Interval.slice_strictMonoOn in Interval. KarpZhangReciprocal.Result supplies
balanced_step and the generic increment, tail_sum and abel_layers unchanged.
Direct frozen dependencies and consumers are reported from compiled terms.
Search of D5 (including private declarations) and pinned Mathlib finds the
existing log-concave balancing and Abel identities, reused here, but no
log-convex balanced-product theorem in the searched scope. External search
is not performed in this offline implementation seat.
Utility none: all assertions are uniform finite-sum identities or inequalities,
not numerical certificates, enumerators, checkers or numerical reductions.
-/

noncomputable section
open Finset
namespace D5.S3.Analytic.KarpZhangCatalanPower.Result

open Coeff Index

/-- Definition 1.1: a nonnegative nontrivial sequence with the reversed
adjacent inequalities, with indices in ℕ = {1,2,…}. No support condition. -/
def IsLogConvex (h : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ h k) ∧ (∃ k, h k ≠ 0) ∧
    (∀ k, 1 ≤ k → h k ^ 2 ≤ h (k - 1) * h (k + 1))

/-- Degree-m coefficient of the Turanian of the formal series (15). -/
def delta (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), h k * h (m - k) *
    (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))

private lemma zero_tail {h : ℕ → ℝ} (hh : IsLogConvex h) (hz : h 1 = 0)
    (n : ℕ) : h (n + 1) = 0 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    have he := hh.2.2 (n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega, ih, zero_mul] at he
    have hn := hh.1 (n + 2)
    have : h (n + 2) = 0 := by nlinarith only [he, hn, sq_nonneg (h (n + 2))]
    simpa only [Nat.add_assoc] using this

private lemma positive_all {h : ℕ → ℝ} (hh : IsLogConvex h) (h1 : 0 < h 1)
    (n : ℕ) : 0 < h n := by
  have h0 : 0 < h 0 := by
    have he := hh.2.2 1 (by omega)
    norm_num only [Nat.sub_self] at he
    by_contra hn
    have hz : h 0 = 0 := le_antisymm (le_of_not_gt hn) (hh.1 0)
    rw [hz, zero_mul] at he
    nlinarith only [he, h1]
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih ih1 =>
    have he := hh.2.2 (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at he
    by_contra hn
    have hz : h (n + 2) = 0 := le_antisymm (le_of_not_gt hn) (hh.1 _)
    rw [show n + 1 + 1 = n + 2 by omega, hz, mul_zero] at he
    nlinarith only [he, ih1]

private lemma convex_ratio {h : ℕ → ℝ} (hh : IsLogConvex h) (h1 : 0 < h 1)
    (a n : ℕ) : h (a + 1) / h a ≤ h (a + n + 1) / h (a + n) := by
  induction n with
  | zero => simp only [Nat.add_zero, le_refl]
  | succ n ih =>
    apply ih.trans
    have he := hh.2.2 (a + n + 1) (by omega)
    rw [show a + n + 1 - 1 = a + n by omega] at he
    apply (div_le_div_iff₀ (positive_all hh h1 _) (positive_all hh h1 _)).2
    simp only [← Nat.add_assoc] at *
    nlinarith only [he]

private lemma convex_step {h : ℕ → ℝ} (hh : IsLogConvex h)
    (m k : ℕ) (hk : k < m / 2) :
    h (k + 1) * h (m - (k + 1)) ≤ h k * h (m - k) := by
  by_cases hz : h 1 = 0
  · rw [zero_tail hh hz k, zero_mul]
    exact mul_nonneg (hh.1 _) (hh.1 _)
  · have h1 : 0 < h 1 := lt_of_le_of_ne (hh.1 1) (Ne.symm hz)
    have he := convex_ratio hh h1 k (m - k - 1 - k)
    rw [show k + (m - k - 1 - k) + 1 = m - k by omega,
      show k + (m - k - 1 - k) = m - (k + 1) by omega] at he
    have hc := (div_le_div_iff₀ (positive_all hh h1 _) (positive_all hh h1 _)).mp he
    nlinarith only [hc]

private lemma abel (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) :
    delta h μ α β m =
      ∑ q ∈ range (m / 2 + 1),
        KarpZhangReciprocal.Result.increment (fun i => h i * h (m - i)) q *
        (∑ k ∈ Icc q (m - q),
          (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))) := by
  rw [delta, KarpZhangReciprocal.Result.abel_layers]
  apply sum_congr rfl
  intro q hq
  congr 1
  let K := fun k => a k (μ + α) * a (m - k) (μ + β) -
    a k μ * a (m - k) (μ + α + β)
  rw [← KarpZhangReciprocal.Result.tail_sum K m q (by have := mem_range.mp hq; omega)]
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Icc]
  omega

private lemma tail {m q : ℕ} (hq : q ∈ range (m / 2 + 1))
    {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ ∑ k ∈ Icc q (m - q),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β)) :=
  Interval.tail_nonneg (by have := mem_range.mp hq; omega) hμ hα hβ

private lemma full_tail (m : ℕ) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (∑ k ∈ Icc 0 (m - 0),
      (a k (μ + α) * a (m - k) (μ + β) - a k μ * a (m - k) (μ + α + β))) = 0 := by
  rw [Nat.sub_zero, ← Nat.range_succ_eq_Icc_zero, sum_sub_distrib,
    index_law (μ + α) (μ + β) m (by linarith) (by linarith),
    index_law μ (μ + α + β) m hμ (by linarith)]
  rw [show μ + α + (μ + β) = μ + (μ + α + β) by ring, sub_self]

/-- Conjecture 4.2, including the nonnegative base-parameter boundary. -/
def claim : Prop :=
  ∀ (h : ℕ → ℝ) (μ α β : ℝ) (m : ℕ), 0 ≤ μ → 0 ≤ α → 0 ≤ β →
    (KarpZhangReciprocal.Result.IsLogConcave h → 0 ≤ delta h μ α β m) ∧
    (IsLogConvex h → delta h μ α β m ≤ 0)

/-- Both coefficient signs for all nonnegative real shifts and every degree. -/
theorem result : claim := by
  intro h μ α β m hμ hα hβ
  constructor
  · intro hh
    rw [abel]
    apply sum_nonneg
    intro q hq
    apply mul_nonneg
    · unfold KarpZhangReciprocal.Result.increment
      split_ifs with hz
      · exact mul_nonneg (hh.1 _) (hh.1 _)
      · have he := KarpZhangReciprocal.Result.balanced_step hh m (q - 1)
          (by have := mem_range.mp hq; omega)
        rw [show q - 1 + 1 = q by omega] at he
        exact sub_nonneg.mpr he
    · exact tail hq hμ hα hβ
  · intro hh
    rw [abel]
    apply sum_nonpos
    intro q hq
    by_cases hz : q = 0
    · subst q
      rw [full_tail m hμ hα hβ, mul_zero]
    · apply mul_nonpos_of_nonpos_of_nonneg
      · unfold KarpZhangReciprocal.Result.increment
        rw [ite_eq_right hz]
        have he := convex_step hh m (q - 1) (by have := mem_range.mp hq; omega)
        rw [show q - 1 + 1 = q by omega] at he
        exact sub_nonpos.mpr he
      · exact tail hq hμ hα hβ

end D5.S3.Analytic.KarpZhangCatalanPower.Result
