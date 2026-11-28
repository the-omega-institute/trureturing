module

public import OmegaMath.InformationTheory.PottsFusion.Channel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

This file records the raw, common-hidden-input formulation of finite
chi-square fusion.  It deliberately has no permutation action on either
output alphabet.  `calibratedCapacity` and `calibratedFusion` use likelihood
ratios relative to the actual output margins; the `raw_*` lemmas below show
that these expressions are exactly the ordinary channel capacities, including
zero columns.  The centered remainder identities are the algebraic core for
the uniform bilinear estimate.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace Omega.InformationTheory.PottsFusion

variable {I Y Z : Type*} [Fintype I] [Nonempty I] [Fintype Y] [Fintype Z]

/-- The uniform input average of a finite real function. -/
def inputMean (f : I → ℝ) : ℝ :=
  (1 / (Fintype.card I : ℝ)) * ∑ i, f i

/-- Likelihood ratios relative to a channel's actual output margin. -/
def rawLikelihood (P : I → Y → ℝ) (y : Y) (i : I) : ℝ :=
  (Fintype.card I : ℝ) * channelPosterior P y i

/-- Capacity of a calibrated likelihood mixture. -/
def calibratedCapacity (w : Y → ℝ) (x : Y → I → ℝ) : ℝ :=
  ∑ y, w y * (inputMean (fun i => (x y i) ^ 2) - 1)

/-- Fusion of two calibrated likelihood mixtures using the same hidden input.
The real quotient convention keeps zero overlaps at zero. -/
def calibratedFusion (w : Y → ℝ) (x : Y → I → ℝ)
    (v : Z → ℝ) (r : Z → I → ℝ) : ℝ :=
  (∑ yz : Y × Z,
    w yz.1 * v yz.2 *
      (inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
        inputMean (fun i => x yz.1 i * r yz.2 i))) - 1

/-- The actual same-input product table. -/
def rawProduct (P : I → Y → ℝ) (Q : I → Z → ℝ) : I → (Y × Z) → ℝ :=
  fun i yz => P i yz.1 * Q i yz.2

/-- A calibrated product term is uniformly bounded by the square of the input
cardinality.  This is the singular-overlap estimate used on the bad-overlap
part of a bilinear argument. -/
theorem calibratedFusion_le_card_sq
    (w : Y → ℝ) (x : Y → I → ℝ) (v : Z → ℝ) (r : Z → I → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∑ z, v z = 1)
    (hx0 : ∀ y i, 0 ≤ x y i)
    (hxN : ∀ y i, x y i ≤ (Fintype.card I : ℝ))
    (hr0 : ∀ z i, 0 ≤ r z i)
    (hrN : ∀ z i, r z i ≤ (Fintype.card I : ℝ)) :
    calibratedFusion w x v r ≤ (Fintype.card I : ℝ) ^ 2 := by
  classical
  let n : ℝ := Fintype.card I
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hterm (yz : Y × Z) :
      inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
          inputMean (fun i => x yz.1 i * r yz.2 i) ≤ n ^ 2 := by
    let f : I → ℝ := fun i => x yz.1 i * r yz.2 i
    have hf0 (i : I) : 0 ≤ f i := mul_nonneg (hx0 yz.1 i) (hr0 yz.2 i)
    have hxf (i : I) : x yz.1 i ^ 2 ≤ n * x yz.1 i := by
      have := mul_le_mul_of_nonneg_left (hxN yz.1 i) (hx0 yz.1 i)
      nlinarith
    have hrf (i : I) : r yz.2 i ^ 2 ≤ n * r yz.2 i := by
      have := mul_le_mul_of_nonneg_left (hrN yz.2 i) (hr0 yz.2 i)
      nlinarith
    have hpoint (i : I) :
        x yz.1 i ^ 2 * r yz.2 i ^ 2 ≤ n ^ 2 * f i := by
      dsimp [f]
      calc
        x yz.1 i ^ 2 * r yz.2 i ^ 2 ≤
            (n * x yz.1 i) * (n * r yz.2 i) := by
              exact mul_le_mul hxf hrf (by positivity) (by positivity)
        _ = n ^ 2 * (x yz.1 i * r yz.2 i) := by ring
    have hmean := Finset.expect_le_expect (s := Finset.univ)
      (fun i _ => hpoint i)
    have hden : 0 ≤ inputMean f := Finset.expect_nonneg (fun i _ => hf0 i)
    by_cases hz : inputMean f = 0
    · have hnum : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) = 0 := by
        have hle : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) ≤
            n ^ 2 * inputMean f := by
          simpa only [← Finset.mul_expect, f] using hmean
        simp [hz] at hle ⊢
        exact le_antisymm hle (by positivity)
      simp [hz, hnum]
    · apply (div_le_iff₀ (lt_of_le_of_ne hden (Ne.symm hz))).2
      have hle : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) ≤
          n ^ 2 * inputMean f := by
        simpa only [← Finset.mul_expect, f] using hmean
      exact hle
  unfold calibratedFusion
  have hsum :
      (∑ yz : Y × Z, w yz.1 * v yz.2) = 1 := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hw1, hv1, one_mul]
  have hweighted := Finset.sum_le_sum (s := Finset.univ) (fun yz _ =>
    mul_le_mul_of_nonneg_left (hterm yz)
      (mul_nonneg (hw0 yz.1) (hv0 yz.2)))
  have hscale :
      (∑ yz : Y × Z, w yz.1 * v yz.2 * n ^ 2) = n ^ 2 := by
    rw [← Finset.sum_mul, hsum, mul_one]
  dsimp [n] at hweighted hscale ⊢
  nlinarith [hweighted, hscale]

private lemma input_card_pos : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

private lemma input_card_ne : (Fintype.card I : ℝ) ≠ 0 :=
  ne_of_gt input_card_pos

private lemma raw_margin_sum_one
    (P : I → Y → ℝ) (hP1 : ∀ i, ∑ y, P i y = 1) :
    ∑ y, channelMargin P y = 1 := by
  unfold channelMargin
  rw [← Finset.sum_div, ← Finset.sum_comm]
  simp only [hP1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp [input_card_ne]

private lemma raw_sum_column_nonneg
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) :
    0 ≤ ∑ i, P i y :=
  Finset.sum_nonneg (fun i _ => hP0 i y)

private lemma raw_margin_nonneg
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) :
    0 ≤ channelMargin P y := by
  unfold channelMargin
  exact div_nonneg (raw_sum_column_nonneg P hP0 y) input_card_pos.le

private lemma raw_posterior_nonnegative
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) (i : I) :
    0 ≤ channelPosterior P y i := by
  unfold channelPosterior
  by_cases hy : channelMargin P y = 0
  · simp [hy, input_card_pos.le]
  · exact div_nonneg (hP0 i y)
      (mul_nonneg input_card_pos.le (raw_margin_nonneg P hP0 y))

private lemma raw_posterior_sum_one
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) :
    ∑ i, channelPosterior P y i = 1 := by
  unfold channelPosterior
  by_cases hy : channelMargin P y = 0
  · simp [hy, input_card_ne]
  · simp only [hy, ↓reduceIte]
    rw [← Finset.sum_div]
    have hm : (∑ i, P i y) =
        (Fintype.card I : ℝ) * channelMargin P y := by
      unfold channelMargin
      field_simp
    rw [hm]
    field_simp [hy, input_card_ne]

private lemma raw_likelihood_nonnegative
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) (i : I) :
    0 ≤ rawLikelihood P y i := by
  unfold rawLikelihood
  exact mul_nonneg input_card_pos.le (raw_posterior_nonnegative P hP0 y i)

private lemma raw_likelihood_upper
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) (i : I) :
    rawLikelihood P y i ≤ (Fintype.card I : ℝ) := by
  have hle : rawLikelihood P y i ≤ ∑ j, rawLikelihood P y j :=
    Finset.single_le_sum (fun j _ => raw_likelihood_nonnegative P hP0 y j)
      (Finset.mem_univ i)
  have hsum : (∑ j, rawLikelihood P y j) = (Fintype.card I : ℝ) := by
    have hpost := raw_posterior_sum_one P hP0 y
    unfold rawLikelihood
    rw [← Finset.mul_sum, hpost]
    field_simp [input_card_ne]
  linarith

private lemma raw_zero_column_entry
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y)
    (hy : channelMargin P y = 0) (i : I) : P i y = 0 := by
  have hsum : (∑ j, P j y) = 0 := by
    unfold channelMargin at hy
    exact (div_eq_zero_iff.mp hy).resolve_right input_card_ne
  have hle : P i y ≤ ∑ j, P j y :=
    Finset.single_le_sum (fun j _ => hP0 j y) (Finset.mem_univ i)
  exact le_antisymm (by linarith [hle, hsum]) (hP0 i y)

private lemma raw_capacity_term
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y) (y : Y) :
    channelMargin P y *
        (inputMean (fun i => (rawLikelihood P y i) ^ 2) - 1) =
      (1 / (Fintype.card I : ℝ)) *
          ((∑ i, (P i y) ^ 2) / channelMargin P y) - channelMargin P y := by
  by_cases hy : channelMargin P y = 0
  · have hzero (i : I) := raw_zero_column_entry P hP0 y hy i
    simp only [hy, div_zero, mul_zero, sub_zero]
    simp [hzero]
  · unfold inputMean rawLikelihood channelPosterior
    simp only [hy, ↓reduceIte]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    field_simp [hy, input_card_ne] <;> ring

/-- Exact ordinary capacity equals the calibrated likelihood capacity. -/
theorem raw_capacity_eq_calibratedCapacity
    (P : I → Y → ℝ) (hP0 : ∀ i y, 0 ≤ P i y)
    (hP1 : ∀ i, ∑ y, P i y = 1) :
    channelCapacity P =
      calibratedCapacity (channelMargin P) (rawLikelihood P) := by
  unfold channelCapacity calibratedCapacity
  simp_rw [raw_capacity_term P hP0]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, raw_margin_sum_one P hP1]

private lemma raw_product_margin
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hQ0 : ∀ i z, 0 ≤ Q i z)
    (y : Y) (z : Z) :
    channelMargin (rawProduct P Q) (y, z) =
      channelMargin P y * channelMargin Q z *
        inputMean (fun i => rawLikelihood P y i * rawLikelihood Q z i) := by
  unfold channelMargin rawProduct rawLikelihood channelPosterior
  by_cases hy : channelMargin P y = 0
  · have hp (i : I) := raw_zero_column_entry P hP0 y hy i
    simp [hy, hp]
  · by_cases hz : channelMargin Q z = 0
    · have hq (i : I) := raw_zero_column_entry Q hQ0 z hz i
      simp [hz, hq]
    · simp only [hy, hz, ↓reduceIte]
      simp_rw [div_mul_div_comm]
      rw [← Finset.sum_div]
      field_simp [input_card_ne, hy, hz] <;> ring

private lemma raw_product_term
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hQ0 : ∀ i z, 0 ≤ Q i z)
    (y : Y) (z : Z) :
    (1 / (Fintype.card I : ℝ)) *
        ((∑ i, (rawProduct P Q i (y, z)) ^ 2) /
          channelMargin (rawProduct P Q) (y, z)) =
      channelMargin P y * channelMargin Q z *
        (inputMean (fun i => rawLikelihood P y i ^ 2 *
          rawLikelihood Q z i ^ 2) /
          inputMean (fun i => rawLikelihood P y i * rawLikelihood Q z i)) := by
  by_cases hy : channelMargin P y = 0
  · have hp (i : I) := raw_zero_column_entry P hP0 y hy i
    simp [hy, hp]
  · by_cases hz : channelMargin Q z = 0
    · have hq (i : I) := raw_zero_column_entry Q hQ0 z hz i
      simp [hz, hq]
    · rw [raw_product_margin P Q hP0 hQ0 y z]
      unfold rawProduct rawLikelihood channelPosterior inputMean
      simp only [hy, hz, ↓reduceIte]
      simp_rw [div_mul_div_comm, div_pow]
      rw [← Finset.sum_div]
      by_cases hraw : (∑ i, P i y * Q i z) = 0
      · have hprod (i : I) : P i y * Q i z = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => mul_nonneg (hP0 j y) (hQ0 j z))).mp hraw i
            (Finset.mem_univ i)
        simp [hraw, hprod]
      · field_simp [hraw, input_card_ne, hy, hz] <;> ring

/-- Exact correspondence for the actual same-input product, with no symmetry
assumption and with singular output overlaps retained. -/
theorem raw_product_capacity_eq_calibratedFusion
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hQ0 : ∀ i z, 0 ≤ Q i z)
    :
    channelCapacity (rawProduct P Q) =
      calibratedFusion (channelMargin P) (rawLikelihood P)
        (channelMargin Q) (rawLikelihood Q) := by
  unfold channelCapacity calibratedFusion
  rw [Finset.mul_sum]
  simp_rw [raw_product_term P Q hP0 hQ0]
  rfl

/-- The raw product capacity retains the cardinality bound even when output
overlaps vanish.  This is the global estimate used to charge the bad-overlap
region in the bilinear proof. -/
theorem raw_product_capacity_le_card_sq
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hQ0 : ∀ i z, 0 ≤ Q i z)
    (hP1 : ∀ i, ∑ y, P i y = 1) (hQ1 : ∀ i, ∑ z, Q i z = 1) :
    channelCapacity (rawProduct P Q) ≤ (Fintype.card I : ℝ) ^ 2 := by
  rw [raw_product_capacity_eq_calibratedFusion P Q hP0 hQ0]
  apply calibratedFusion_le_card_sq
  · intro y
    exact raw_margin_nonneg P hP0 y
  · exact raw_margin_sum_one P hP1
  · intro z
    exact raw_margin_nonneg Q hQ0 z
  · exact raw_margin_sum_one Q hQ1
  · intro y i
    exact raw_likelihood_nonnegative P hP0 y i
  · intro y i
    exact raw_likelihood_upper P hP0 y i
  · intro z i
    exact raw_likelihood_nonnegative Q hQ0 z i
  · intro z i
    exact raw_likelihood_upper Q hQ0 z i

end Omega.InformationTheory.PottsFusion
