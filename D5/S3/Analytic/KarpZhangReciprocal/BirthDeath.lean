/- GID: D5/S3/Analytic/KarpZhangReciprocal/BirthDeath
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangReciprocal/BirthDeath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset, mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Finite reversible birth-and-death chains satisfy a curvature-weighted variance bound. -/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
admission_basis: escape-witness
content theorem: variance_bound, through mean_zero_flux.
escape_witness: The cumulative centered masses construct an edge flux solving the finite
divergence equation. Detailed balance, coercivity and weighted Cauchy--Schwarz
then prove the variance estimate. Vertices are 0,...,n, with both endpoint
rates zero; the singleton case is included.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* kappa: proof_shape: bind-only (definition); escape_witness: none;
  consumers: coercivity, variance_bound, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_variance_bound.
* variance: proof_shape: bind-only (definition); escape_witness: none;
  consumers: variance_bound, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.slice_concave, KarpZhangReciprocal.IntervalConvolution.variance_expand.
* left_sum: proof_shape: bind-only; escape_witness: none;
  consumers: coercivity, integration_by_parts.
* right_sum: proof_shape: bind-only; escape_witness: none;
  consumers: coercivity, integration_by_parts.
* mean_zero_flux: proof_shape: content; escape_witness: mean_zero_flux;
  consumers: variance_bound.
* integration_by_parts: proof_shape: bind-only; escape_witness: none;
  consumers: variance_bound.
* coercivity: proof_shape: bind-only; escape_witness: none;
  consumers: variance_bound.
* variance_bound: proof_shape: content; escape_witness: mean_zero_flux;
  consumers: KarpZhangReciprocal.IntervalConvolution.score_variance_bound.

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

namespace D5.S3.Analytic.KarpZhangReciprocal.BirthDeath

/-- The curvature on the edge from `i` to `i+1`. -/
def kappa (p r : ℕ → ℝ) (i : ℕ) : ℝ := p i - p (i + 1) + r (i + 1) - r i

/-- Variance for a probability vector on the vertices `0,...,n`. -/
def variance (n : ℕ) (π h : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), π i * (h i - ∑ j ∈ range (n + 1), π j * h j) ^ 2

private theorem left_sum (n : ℕ) (π p r f : ℕ → ℝ) (hr : r 0 = 0)
    (hb : ∀ i < n, π i * p i = π (i + 1) * r (i + 1)) :
    (∑ i ∈ range (n + 1), π i * r i * f i) =
      ∑ i ∈ range n, π i * p i * f (i + 1) := by
  rw [sum_range_succ']
  simp only [hr, mul_zero, zero_mul, add_zero]
  apply sum_congr rfl
  intro i hi
  rw [← hb i (mem_range.mp hi)]

private theorem right_sum (n : ℕ) (π p f : ℕ → ℝ) (hp : p n = 0) :
    (∑ i ∈ range (n + 1), π i * p i * f i) =
      ∑ i ∈ range n, π i * p i * f i := by
  rw [sum_range_succ]
  simp only [hp, mul_zero, zero_mul, add_zero]

/-- Explicit edge flux, obtained by accumulating the centered vertex masses. -/
private theorem mean_zero_flux (n : ℕ) (π p r h : ℕ → ℝ)
    (hπ : ∀ i ≤ n, 0 < π i) (hp : p n = 0) (hr : r 0 = 0)
    (hpp : ∀ i < n, 0 < p i)
    (hb : ∀ i < n, π i * p i = π (i + 1) * r (i + 1))
    (hm : ∑ i ∈ range (n + 1), π i * h i = 0) :
    ∃ z : ℕ → ℝ, ∀ i ≤ n, h i = r i * z i - p i * z (i + 1) := by
  let z : ℕ → ℝ := fun i =>
    -(∑ j ∈ range i, π j * h j) / (π (i - 1) * p (i - 1))
  have hout (i : ℕ) (hi : i ≤ n) :
      π i * p i * z (i + 1) = -(∑ j ∈ range (i + 1), π j * h j) := by
    by_cases hin : i = n
    · subst i
      simp only [hp, mul_zero, zero_mul, hm, neg_zero]
    · have hit : i < n := lt_of_le_of_ne hi hin
      change π i * p i *
        (-(∑ j ∈ range (i + 1), π j * h j) / (π i * p i)) =
          -(∑ j ∈ range (i + 1), π j * h j)
      field_simp [ne_of_gt (hπ i hi), ne_of_gt (hpp i hit)]
      <;> ring
  have hin (i : ℕ) (hi : i ≤ n) :
      π i * r i * z i = -(∑ j ∈ range i, π j * h j) := by
    cases i with
    | zero => simp [hr]
    | succ i =>
      rw [← hb i (Nat.lt_of_succ_le hi)]
      exact hout i (Nat.le_of_succ_le hi)
  refine ⟨z, fun i hi => ?_⟩
  apply mul_left_cancel₀ (ne_of_gt (hπ i hi))
  calc
    π i * h i = -(∑ j ∈ range i, π j * h j) +
        ∑ j ∈ range (i + 1), π j * h j := by rw [sum_range_succ]; ring
    _ = π i * r i * z i - π i * p i * z (i + 1) := by
      linarith [hin i hi, hout i hi]
    _ = π i * (r i * z i - p i * z (i + 1)) := by ring

private theorem integration_by_parts (n : ℕ) (π p r h z : ℕ → ℝ)
    (hp : p n = 0) (hr : r 0 = 0)
    (hb : ∀ i < n, π i * p i = π (i + 1) * r (i + 1))
    (hz : ∀ i ≤ n, h i = r i * z i - p i * z (i + 1)) :
    (∑ i ∈ range (n + 1), π i * h i ^ 2) =
      ∑ i ∈ range n, π i * p i * ((h (i + 1) - h i) * z (i + 1)) := by
  calc
    _ = (∑ i ∈ range (n + 1), π i * r i * (h i * z i)) -
        ∑ i ∈ range (n + 1), π i * p i * (h i * z (i + 1)) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      calc
        π i * h i ^ 2 = π i * h i * h i := by ring
        _ = π i * h i * (r i * z i - p i * z (i + 1)) := by
          rw [← hz i (Nat.le_of_lt_succ (mem_range.mp hi))]
        _ = _ := by ring
    _ = _ := by
      rw [left_sum n π p r (fun i => h i * z i) hr hb,
        right_sum n π p (fun i => h i * z (i + 1)) hp, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring

/-- Discrete coercivity from detailed balance and a pointwise square inequality. -/
private theorem coercivity (n : ℕ) (π p r z : ℕ → ℝ)
    (hπ : ∀ i ≤ n, 0 ≤ π i) (hp : p n = 0) (hr : r 0 = 0)
    (hpp : ∀ i ≤ n, 0 ≤ p i) (hrr : ∀ i ≤ n, 0 ≤ r i)
    (hb : ∀ i < n, π i * p i = π (i + 1) * r (i + 1)) :
    (∑ i ∈ range n, π i * p i * kappa p r i * z (i + 1) ^ 2) ≤
      ∑ i ∈ range (n + 1), π i * (r i * z i - p i * z (i + 1)) ^ 2 := by
  have hpoint :
      (∑ i ∈ range (n + 1),
        (π i * r i * ((r i - p i) * z i ^ 2) +
        π i * p i * ((p i - r i) * z (i + 1) ^ 2))) ≤
      ∑ i ∈ range (n + 1), π i * (r i * z i - p i * z (i + 1)) ^ 2 := by
    apply sum_le_sum
    intro i hi
    have hi' := Finset.mem_range_succ_iff.mp hi
    have hs := mul_nonneg
      (mul_nonneg (mul_nonneg (hπ i hi') (hpp i hi')) (hrr i hi'))
      (sq_nonneg (z i - z (i + 1)))
    nlinarith
  calc
    _ = ∑ i ∈ range (n + 1),
        (π i * r i * ((r i - p i) * z i ^ 2) +
        π i * p i * ((p i - r i) * z (i + 1) ^ 2)) := by
      rw [sum_add_distrib,
        left_sum n π p r (fun i => (r i - p i) * z i ^ 2) hr hb,
        right_sum n π p (fun i => (p i - r i) * z (i + 1) ^ 2) hp,
        ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      unfold kappa
      ring
    _ ≤ _ := hpoint

/-- The finite birth-and-death variance inequality. A finite interval is indexed from zero;
the rates at both endpoints are zero, and the curvature is required only on existing edges. -/
theorem variance_bound (n : ℕ) (π p r h : ℕ → ℝ)
    (hπ : ∀ i ≤ n, 0 < π i)
    (hprob : ∑ i ∈ range (n + 1), π i = 1)
    (hp : p n = 0) (hr : r 0 = 0)
    (hpp : ∀ i < n, 0 < p i)
    (hrr : ∀ i, 0 < i → i ≤ n → 0 < r i)
    (hb : ∀ i < n, π i * p i = π (i + 1) * r (i + 1))
    (hk : ∀ i < n, 0 < kappa p r i) :
    variance n π h ≤
      ∑ i ∈ range n, π i * p i / kappa p r i * (h (i + 1) - h i) ^ 2 := by
  let a : ℝ := ∑ i ∈ range (n + 1), π i * h i
  let g : ℕ → ℝ := fun i => h i - a
  have hm : ∑ i ∈ range (n + 1), π i * g i = 0 := by
    simp only [g, mul_sub, sum_sub_distrib, ← sum_mul, hprob, one_mul]
    exact sub_self a
  obtain ⟨z, hz⟩ := mean_zero_flux n π p r g hπ hp hr hpp hb hm
  have hpp' (i : ℕ) (hi : i ≤ n) : 0 ≤ p i := by
    by_cases he : i = n
    · simpa [he, hp]
    · exact (hpp i (lt_of_le_of_ne hi he)).le
  have hrr' (i : ℕ) (hi : i ≤ n) : 0 ≤ r i := by
    by_cases he : i = 0
    · simpa [he, hr]
    · exact (hrr i (Nat.pos_of_ne_zero he) hi).le
  let V : ℝ := ∑ i ∈ range (n + 1), π i * g i ^ 2
  let A : ℝ := ∑ i ∈ range n,
    π i * p i / kappa p r i * (g (i + 1) - g i) ^ 2
  let E : ℝ := ∑ i ∈ range n, π i * p i * kappa p r i * z (i + 1) ^ 2
  have hV : V = ∑ i ∈ range n,
      π i * p i * ((g (i + 1) - g i) * z (i + 1)) :=
    integration_by_parts n π p r g z hp hr hb hz
  have hE : E ≤ V := by
    calc
      E ≤ ∑ i ∈ range (n + 1), π i * (r i * z i - p i * z (i + 1)) ^ 2 :=
        coercivity n π p r z (fun i hi => (hπ i hi).le) hp hr hpp' hrr' hb
      _ = V := sum_congr rfl (fun i hi => by rw [← hz i (Nat.le_of_lt_succ (mem_range.mp hi))])
  have hA : 0 ≤ A := by
    apply sum_nonneg
    intro i hi
    have hit := mem_range.mp hi
    exact mul_nonneg (div_nonneg (mul_nonneg (hπ i (Nat.le_of_lt hit)).le
      (hpp i hit).le) (hk i hit).le) (sq_nonneg _)
  have hcs : V ^ 2 ≤ A * E := by
    rw [hV]
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul (range n)
    · intro i hi
      have hit := mem_range.mp hi
      exact mul_nonneg (div_nonneg (mul_nonneg (hπ i (Nat.le_of_lt hit)).le
        (hpp i hit).le) (hk i hit).le) (sq_nonneg _)
    · intro i hi
      have hit := mem_range.mp hi
      exact mul_nonneg (mul_nonneg (mul_nonneg (hπ i (Nat.le_of_lt hit)).le
        (hpp i hit).le) (hk i hit).le) (sq_nonneg _)
    · intro i hi
      have hit := mem_range.mp hi
      have hkn := ne_of_gt (hk i hit)
      apply le_of_eq
      field_simp [hkn]
      <;> ring
  have hV0 : 0 ≤ V := sum_nonneg (fun i hi =>
    mul_nonneg (hπ i (Nat.le_of_lt_succ (mem_range.mp hi))).le (sq_nonneg _))
  have hVA : V ≤ A := by
    have hAV := mul_le_mul_of_nonneg_left hE hA
    by_cases hv : V = 0
    · rw [hv]
      exact hA
    · have hvp : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hv)
      apply (mul_le_mul_iff_left₀ hvp).mp
      calc
        V * V = V ^ 2 := by ring
        _ ≤ A * E := hcs
        _ ≤ A * V := hAV
  have hg (i : ℕ) : g (i + 1) - g i = h (i + 1) - h i := sub_sub_sub_cancel_right (h (i + 1)) (h i) a
  simpa only [V, A, variance, hg, g, a] using hVA

end D5.S3.Analytic.KarpZhangReciprocal.BirthDeath
