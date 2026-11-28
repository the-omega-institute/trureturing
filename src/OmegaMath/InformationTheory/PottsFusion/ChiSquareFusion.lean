module

public import OmegaMath.InformationTheory.PottsFusion.Channel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

This file records the calibrated common-hidden-input core of finite
chi-square fusion.  It deliberately has no permutation action on either
output alphabet.  The calibrated expressions use likelihood ratios relative
to actual output margins; singular denominators retain the real `0 / 0 = 0`
convention.  The cardinality estimate is the global bound used for the
bad-overlap branch of the intended bilinear argument.
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

private lemma input_card_pos : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

private lemma input_card_ne : (Fintype.card I : ℝ) ≠ 0 :=
  ne_of_gt input_card_pos

private lemma inputMean_eq_expect (f : I → ℝ) :
    inputMean f = (𝔼 i, f i) := by
  unfold inputMean
  rw [Fintype.expect_eq_sum_div_card]
  field_simp [input_card_ne]

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
              exact mul_le_mul (hxf i) (hrf i) (sq_nonneg _)
                (mul_nonneg hn (hx0 yz.1 i))
        _ = n ^ 2 * (x yz.1 i * r yz.2 i) := by ring
    have hmean := Finset.expect_le_expect (s := Finset.univ)
      (fun i _ => hpoint i)
    have hden : 0 ≤ inputMean f := by
      rw [inputMean_eq_expect]
      exact Finset.expect_nonneg (fun i _ => hf0 i)
    by_cases hz : inputMean f = 0
    · have hnum : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) = 0 := by
        have hle : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) ≤
            n ^ 2 * inputMean f := by
          rw [inputMean_eq_expect, inputMean_eq_expect]
          simpa only [← Finset.mul_expect, f] using hmean
        have hle0 : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) ≤ 0 := by
          simpa [hz] using hle
        have hnum0 : 0 ≤ inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) := by
          rw [inputMean_eq_expect]
          exact Finset.expect_nonneg (fun i _ => mul_nonneg
            (sq_nonneg _) (sq_nonneg _))
        exact le_antisymm hle0 hnum0
      simpa [hz, hnum] using (sq_nonneg n)
    · apply (div_le_iff₀ (lt_of_le_of_ne hden (Ne.symm hz))).2
      have hle : inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) ≤
          n ^ 2 * inputMean f := by
        rw [inputMean_eq_expect, inputMean_eq_expect]
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
    rw [← Finset.sum_mul, hsum, one_mul]
  dsimp [n] at hweighted hscale ⊢
  nlinarith [hweighted, hscale]


end Omega.InformationTheory.PottsFusion
