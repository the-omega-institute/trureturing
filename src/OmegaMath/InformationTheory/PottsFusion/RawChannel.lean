module

public import OmegaMath.InformationTheory.PottsFusion.FiniteChannel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Omega original.

Likelihood coordinates for finite nonnegative channel tables.  A zero output
column has likelihood one and weight zero.  Reconstruction identities retain
zero columns and zero overlaps in the exact common-input product capacity.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace Omega.InformationTheory.PottsFusion

variable {I Y Z : Type*} [Fintype I]

theorem channelMargin_eq_inputMean (P : I → Y → ℝ) (y : Y) :
    channelMargin P y = inputMean (fun i => P i y) := by
  unfold channelMargin inputMean
  ring

theorem raw_margin_nonneg (P : I → Y → ℝ) (hP : ∀ i y, 0 ≤ P i y) (y : Y) :
    0 ≤ channelMargin P y := by
  rw [channelMargin_eq_inputMean]
  exact inputMean_nonneg _ (fun i => hP i y)

theorem raw_margin_sum_one [Nonempty I] [Fintype Y]
    (P : I → Y → ℝ) (hP : ∀ i, ∑ y, P i y = 1) :
    ∑ y, channelMargin P y = 1 := by
  simp_rw [channelMargin_eq_inputMean]
  rw [← inputMean_sum]
  simp only [hP, inputMean_const]

theorem raw_zero_column_entry (P : I → Y → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (y : Y) (hy : channelMargin P y = 0) (i : I) :
    P i y = 0 := by
  let : Nonempty I := ⟨i⟩
  have hsum : (∑ j, P j y) = 0 := by
    unfold channelMargin at hy
    exact (div_eq_zero_iff.mp hy).resolve_right (ne_of_gt (card_real_pos (I := I)))
  have hle : P i y ≤ ∑ j, P j y :=
    Finset.single_le_sum (fun j _ => hP j y) (Finset.mem_univ i)
  exact le_antisymm (by linarith only [hle, hsum]) (hP i y)

/-- A likelihood coordinate on every output column, including zero columns. -/
def rawDensity (P : I → Y → ℝ) (y : Y) (i : I) : ℝ :=
  if channelMargin P y = 0 then 1 else P i y / channelMargin P y

theorem raw_density_reconstruct (P : I → Y → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (y : Y) (i : I) :
    channelMargin P y * rawDensity P y i = P i y := by
  by_cases hm : channelMargin P y = 0
  · simp [rawDensity, hm, raw_zero_column_entry P hP y hm i]
  · simpa only [rawDensity, hm, ↓reduceIte] using
      mul_div_cancel₀ (P i y) hm

theorem raw_density_nonneg (P : I → Y → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (y : Y) (i : I) :
    0 ≤ rawDensity P y i := by
  unfold rawDensity
  split_ifs
  · norm_num
  · exact div_nonneg (hP i y) (raw_margin_nonneg P hP y)

theorem raw_density_mean_one [Nonempty I] (P : I → Y → ℝ) (y : Y) :
    inputMean (rawDensity P y) = 1 := by
  by_cases hm : channelMargin P y = 0
  · have hfun : rawDensity P y = (fun _ : I => (1 : ℝ)) := by
      funext i
      simp only [rawDensity, hm, ↓reduceIte]
    rw [hfun, inputMean_const]
  · have hmean : inputMean (fun i => P i y) = channelMargin P y :=
      (channelMargin_eq_inputMean P y).symm
    have hid : inputMean (rawDensity P y) =
        inputMean (fun i => P i y) / channelMargin P y := by
      unfold rawDensity
      simp only [hm, ↓reduceIte]
      unfold inputMean
      rw [← Finset.sum_div]
      ring
    rw [hid, hmean, div_self hm]

theorem raw_density_calibrated [Fintype Y] (P : I → Y → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hP1 : ∀ i, ∑ y, P i y = 1) (i : I) :
    (∑ y, channelMargin P y * rawDensity P y i) = 1 := by
  simp_rw [raw_density_reconstruct P hP0]
  exact hP1 i

theorem channelCapacity_eq_mean [Fintype Y] (P : I → Y → ℝ) :
    channelCapacity P = (∑ y, inputMean (fun i => P i y ^ 2) /
      channelMargin P y) - 1 := by
  unfold channelCapacity inputMean
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem raw_square_mean (P : I → Y → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (y : Y) :
    inputMean (fun i => P i y ^ 2) = channelMargin P y ^ 2 *
      inputMean (fun i => rawDensity P y i ^ 2) := by
  rw [← inputMean_const_mul]
  congr 1
  funext i
  rw [← mul_pow, raw_density_reconstruct P hP y i]

theorem square_scale_div (m a : ℝ) : (m ^ 2 * a) / m = m * a := by
  by_cases hm : m = 0
  · simp [hm]
  · field_simp [hm]

theorem raw_capacity_eq_calibratedCapacity [Nonempty I] [Fintype Y] (P : I → Y → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hP1 : ∀ i, ∑ y, P i y = 1) :
    channelCapacity P = calibratedCapacity (channelMargin P) (rawDensity P) := by
  rw [channelCapacity_eq_mean]
  simp_rw [raw_square_mean P hP0, square_scale_div]
  unfold calibratedCapacity
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, raw_margin_sum_one P hP1]

theorem raw_product_reconstruct (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (hQ : ∀ i z, 0 ≤ Q i z)
    (y : Y) (z : Z) (i : I) :
    rawProduct P Q i (y, z) = (channelMargin P y * channelMargin Q z) *
      (rawDensity P y i * rawDensity Q z i) := by
  calc
    rawProduct P Q i (y, z) =
        (channelMargin P y * rawDensity P y i) *
          (channelMargin Q z * rawDensity Q z i) := by
      rw [raw_density_reconstruct P hP, raw_density_reconstruct Q hQ]
      rfl
    _ = _ := by ring

theorem raw_product_margin (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (hQ : ∀ i z, 0 ≤ Q i z) (y : Y) (z : Z) :
    channelMargin (rawProduct P Q) (y, z) =
      (channelMargin P y * channelMargin Q z) *
        inputMean (fun i => rawDensity P y i * rawDensity Q z i) := by
  rw [channelMargin_eq_inputMean, ← inputMean_const_mul]
  congr 1
  funext i
  exact raw_product_reconstruct P Q hP hQ y z i

theorem raw_product_square_mean (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (hQ : ∀ i z, 0 ≤ Q i z) (y : Y) (z : Z) :
    inputMean (fun i => rawProduct P Q i (y, z) ^ 2) =
      (channelMargin P y * channelMargin Q z) ^ 2 *
        inputMean (fun i => rawDensity P y i ^ 2 * rawDensity Q z i ^ 2) := by
  rw [← inputMean_const_mul]
  congr 1
  funext i
  rw [raw_product_reconstruct P Q hP hQ y z i]
  ring

theorem square_scale_ratio (w a b : ℝ) :
    (w ^ 2 * a) / (w * b) = w * (a / b) := by
  by_cases hw : w = 0
  · simp [hw]
  · by_cases hb : b = 0
    · simp [hb]
    · field_simp [hw, hb]

/-- The output pair uses the same hidden input in both factors. -/
theorem raw_product_capacity_eq_calibratedFusion [Fintype Y] [Fintype Z]
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP : ∀ i y, 0 ≤ P i y) (hQ : ∀ i z, 0 ≤ Q i z) :
    channelCapacity (rawProduct P Q) =
      calibratedFusion (channelMargin P) (rawDensity P) (channelMargin Q) (rawDensity Q) := by
  rw [channelCapacity_eq_mean]
  unfold calibratedFusion
  congr 1
  apply Finset.sum_congr rfl
  intro yz _
  rcases yz with ⟨y, z⟩
  rw [raw_product_square_mean P Q hP hQ, raw_product_margin P Q hP hQ]
  exact square_scale_ratio _ _ _

end Omega.InformationTheory.PottsFusion
