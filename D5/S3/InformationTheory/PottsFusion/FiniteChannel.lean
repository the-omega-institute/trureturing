/- GID: D5/S3/InformationTheory/PottsFusion/FiniteChannel
   generality: G
   mirror-B: none(waiver:covered-by-chi-square-bilinear-fusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite real channel tables, their uniform-input margins, and calibrated likelihood averages. -/

module

public import OmegaBuild.Commands
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Omega original.

Finite real channel tables, their uniform-input margins, and calibrated
likelihood averages.  Real division retains zero output columns and zero
overlaps.  The elementary ratio estimates also apply at zero denominators.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace Omega.InformationTheory.PottsFusion

variable {I : Type*} [Fintype I]

def inputMean (f : I → ℝ) : ℝ :=
  (1 / (Fintype.card I : ℝ)) * ∑ i, f i

theorem inputMean_eq_expect (f : I → ℝ) : inputMean f = (𝔼 i, f i) := by
  unfold inputMean
  rw [Fintype.expect_eq_sum_div_card]
  ring

theorem card_real_pos [Nonempty I] : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem card_real_one_le [Nonempty I] : 1 ≤ (Fintype.card I : ℝ) := by
  have h : 1 ≤ Fintype.card I := Fintype.card_pos
  exact_mod_cast h

theorem inputMean_const [Nonempty I] (a : ℝ) : inputMean (fun _ : I => a) = a := by
  rw [inputMean_eq_expect]
  simp

theorem inputMean_add (f g : I → ℝ) :
    inputMean (fun i => f i + g i) = inputMean f + inputMean g := by
  unfold inputMean
  rw [Finset.sum_add_distrib, mul_add]

theorem inputMean_sub (f g : I → ℝ) :
    inputMean (fun i => f i - g i) = inputMean f - inputMean g := by
  unfold inputMean
  rw [Finset.sum_sub_distrib, mul_sub]

theorem inputMean_const_mul (a : ℝ) (f : I → ℝ) :
    inputMean (fun i => a * f i) = a * inputMean f := by
  unfold inputMean
  rw [← Finset.mul_sum]
  ring

theorem inputMean_mul_const (f : I → ℝ) (a : ℝ) :
    inputMean (fun i => f i * a) = inputMean f * a := by
  unfold inputMean
  rw [← Finset.sum_mul]
  ring

theorem inputMean_nonneg (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ inputMean f := by
  unfold inputMean
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ => hf i))

theorem inputMean_mono (f g : I → ℝ) (h : ∀ i, f i ≤ g i) :
    inputMean f ≤ inputMean g := by
  unfold inputMean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h i))
    (one_div_nonneg.mpr (Nat.cast_nonneg _))

theorem inputMean_abs_le (f : I → ℝ) : |inputMean f| ≤ inputMean (fun i => |f i|) := by
  simp only [inputMean_eq_expect]
  exact Finset.abs_expect_le Finset.univ f

theorem inputMean_mul_sq_le (f g : I → ℝ) :
    inputMean (fun i => f i * g i) ^ 2 ≤
      inputMean (fun i => f i ^ 2) * inputMean (fun i => g i ^ 2) := by
  simp only [inputMean_eq_expect]
  exact Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem inputMean_sum {J : Type*} [Fintype J] (f : J → I → ℝ) :
    inputMean (fun i => ∑ j, f j i) = ∑ j, inputMean (f j) := by
  unfold inputMean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem weighted_sum_inputMean {J : Type*} [Fintype J]
    (w : J → ℝ) (f : J → I → ℝ) :
    (∑ j, w j * inputMean (f j)) = inputMean (fun i => ∑ j, w j * f j i) := by
  rw [inputMean_sum]
  simp only [inputMean_const_mul]

theorem weighted_inner_inputMean {J K : Type*} [Fintype J] [Fintype K]
    (w : J → ℝ) (v : K → ℝ) (f : J → I → ℝ) (g : K → I → ℝ) :
    (∑ jk : J × K, w jk.1 * v jk.2 *
      inputMean (fun i => f jk.1 i * g jk.2 i)) =
    inputMean (fun i => (∑ j, w j * f j i) * (∑ k, v k * g k i)) := by
  rw [weighted_sum_inputMean]
  congr 1
  funext i
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sum_eq_card_mul_inputMean (f : I → ℝ) :
    (∑ i, f i) = (Fintype.card I : ℝ) * inputMean f := by
  rw [inputMean_eq_expect]
  simpa only [Finset.card_univ, nsmul_eq_mul] using
    (Finset.card_smul_expect Finset.univ f).symm

theorem inputMean_upper_of_normalized (f : I → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : inputMean f = 1) (i : I) :
    f i ≤ (Fintype.card I : ℝ) := by
  have hle : f i ≤ ∑ j, f j :=
    Finset.single_le_sum (fun j _ => hf0 j) (Finset.mem_univ i)
  rw [sum_eq_card_mul_inputMean, hf1, mul_one] at hle
  exact hle

theorem square_ratio_le_sum (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 2) / (∑ i, a i) ≤ ∑ i, a i := by
  have hs0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  have hs2 : (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha i)
  by_cases hs : (∑ i, a i) = 0
  · simp [hs]
  · apply (div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm hs))).2
    nlinarith

theorem inputMean_ratio_le_card_mul
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    inputMean (fun i => a i ^ 2) / inputMean a ≤
      (Fintype.card I : ℝ) * inputMean a := by
  by_cases hn : (Fintype.card I : ℝ) = 0
  · simp [inputMean, hn]
  have hratio : inputMean (fun i => a i ^ 2) / inputMean a =
      (∑ i, a i ^ 2) / (∑ i, a i) := by
    unfold inputMean
    by_cases hs : (∑ i, a i) = 0
    · simp [hs]
    · field_simp [hs, hn]
  rw [hratio, ← sum_eq_card_mul_inputMean]
  exact square_ratio_le_sum a ha

def channelMargin {Y : Type*} (P : I → Y → ℝ) (y : Y) : ℝ :=
  (∑ i, P i y) / (Fintype.card I : ℝ)

def channelCapacity {Y : Type*} [Fintype Y] (P : I → Y → ℝ) : ℝ :=
  (1 / (Fintype.card I : ℝ)) *
      (∑ y, (∑ i, (P i y) ^ 2) / channelMargin P y) - 1

def calibratedCapacity {Y : Type*} [Fintype Y] (w : Y → ℝ) (x : Y → I → ℝ) : ℝ :=
  ∑ y, w y * (inputMean (fun i => (x y i) ^ 2) - 1)

def calibratedFusion {Y Z : Type*} [Fintype Y] [Fintype Z]
    (w : Y → ℝ) (x : Y → I → ℝ) (v : Z → ℝ) (r : Z → I → ℝ) : ℝ :=
  (∑ yz : Y × Z, w yz.1 * v yz.2 *
    (inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
      inputMean (fun i => x yz.1 i * r yz.2 i))) - 1

def rawProduct {Y Z : Type*} (P : I → Y → ℝ) (Q : I → Z → ℝ) : I → (Y × Z) → ℝ :=
  fun i yz => P i yz.1 * Q i yz.2

end Omega.InformationTheory.PottsFusion
