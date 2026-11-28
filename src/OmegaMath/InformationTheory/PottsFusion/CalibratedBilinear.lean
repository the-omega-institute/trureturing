module

public import OmegaMath.InformationTheory.PottsFusion.FiniteChannel
public import OmegaMath.InformationTheory.PottsFusion.BilinearRemainder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Omega original.

A bilinear bound for calibrated finite likelihood families. Centered moments
separate the scalar ratio estimate from the cancellation supplied by coordinate
calibration. Real division includes pairs with zero overlap.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace Omega.InformationTheory.PottsFusion

variable {I : Type*} [Fintype I] [Nonempty I]

private theorem centered_energy (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx : inputMean x = 1) :
    inputMean (fun i => x i - 1) = 0 ∧
    inputMean (fun i => (x i - 1) ^ 2) = inputMean (fun i => x i ^ 2) - 1 ∧
    0 ≤ inputMean (fun i => (x i - 1) ^ 2) ∧
    inputMean (fun i => (x i - 1) ^ 2) ≤ (Fintype.card I : ℝ) - 1 ∧
    (∀ i, |x i - 1| ≤ (Fintype.card I : ℝ)) := by
  have hn := card_real_one_le (I := I)
  have hxn : ∀ i, x i ≤ (Fintype.card I : ℝ) :=
    inputMean_upper_of_normalized x hx0 hx
  have hm : inputMean (fun i => x i - 1) = 0 := by
    rw [inputMean_sub, hx, inputMean_const]
    ring
  have he : inputMean (fun i => (x i - 1) ^ 2) =
      inputMean (fun i => x i ^ 2) - 1 := by
    have hp : (fun i => (x i - 1) ^ 2) = (fun i => x i ^ 2 - 2 * x i + 1) := by
      funext i
      ring
    rw [hp, inputMean_add, inputMean_sub, inputMean_const_mul, hx, inputMean_const]
    ring
  have hq : inputMean (fun i => x i ^ 2) ≤ (Fintype.card I : ℝ) := by
    calc
      inputMean (fun i => x i ^ 2) ≤ inputMean (fun i => (Fintype.card I : ℝ) * x i) := by
        apply inputMean_mono
        intro i
        have h := mul_le_mul_of_nonneg_right (hxn i) (hx0 i)
        nlinarith only [h]
      _ = (Fintype.card I : ℝ) := by rw [inputMean_const_mul, hx, mul_one]
  refine ⟨hm, he, inputMean_nonneg _ (fun i => sq_nonneg _), ?_, ?_⟩
  · linarith only [he, hq]
  · intro i
    rw [abs_le]
    constructor <;> linarith only [hx0 i, hxn i, hn]

private theorem centered_pair_bound (a b : I → ℝ)
    (ha : inputMean a = 0) (hb : inputMean b = 0)
    (han : ∀ i, |a i| ≤ (Fintype.card I : ℝ))
    (hbn : ∀ i, |b i| ≤ (Fintype.card I : ℝ))
    (hA : inputMean (fun i => a i ^ 2) ≤ (Fintype.card I : ℝ) - 1)
    (hB : inputMean (fun i => b i ^ 2) ≤ (Fintype.card I : ℝ) - 1)
    (hab : ∀ i, 0 ≤ (a i + 1) * (b i + 1)) :
    inputMean (fun i => (a i + 1) ^ 2 * (b i + 1) ^ 2) /
        inputMean (fun i => (a i + 1) * (b i + 1)) - 1 ≤
      inputMean (fun i => a i ^ 2) + inputMean (fun i => b i ^ 2) +
      ((3 - inputMean (fun i => a i ^ 2) - inputMean (fun i => b i ^ 2)) *
          inputMean (fun i => a i * b i) +
        2 * inputMean (fun i => a i ^ 2 * b i) +
        2 * inputMean (fun i => a i * b i ^ 2)) +
      14 * (Fintype.card I : ℝ) * inputMean (fun i => a i ^ 2) *
        inputMean (fun i => b i ^ 2) := by
  classical
  let n : ℝ := Fintype.card I
  let A := inputMean (fun i => a i ^ 2)
  let B := inputMean (fun i => b i ^ 2)
  let c := inputMean (fun i => a i * b i)
  let d := inputMean (fun i => a i ^ 2 * b i)
  let e := inputMean (fun i => a i * b i ^ 2)
  let f := inputMean (fun i => a i ^ 2 * b i ^ 2)
  let t := inputMean (fun i => |a i * b i|)
  let H := inputMean (fun i => (a i + 1) ^ 2 * (b i + 1) ^ 2) /
    inputMean (fun i => (a i + 1) * (b i + 1)) - 1
  have hA0 : 0 ≤ A := inputMean_nonneg _ (fun i => sq_nonneg _)
  have hB0 : 0 ≤ B := inputMean_nonneg _ (fun i => sq_nonneg _)
  have hc : |c| ≤ t := inputMean_abs_le _
  have ht : t ^ 2 ≤ A * B := by
    have hh := inputMean_mul_sq_le (fun i => |a i|) (fun i => |b i|)
    simpa only [← abs_mul, sq_abs] using hh
  have hd : |d| ≤ n * t := by
    calc
      |d| ≤ inputMean (fun i => |a i ^ 2 * b i|) := inputMean_abs_le _
      _ ≤ inputMean (fun i => n * |a i * b i|) := by
        apply inputMean_mono
        intro i
        calc
          |a i ^ 2 * b i| = |a i| * |a i * b i| := by rw [← abs_mul]; congr 1; ring
          _ ≤ n * |a i * b i| := mul_le_mul_of_nonneg_right (han i) (abs_nonneg _)
      _ = n * t := inputMean_const_mul _ _
  have he : |e| ≤ n * t := by
    calc
      |e| ≤ inputMean (fun i => |a i * b i ^ 2|) := inputMean_abs_le _
      _ ≤ inputMean (fun i => n * |a i * b i|) := by
        apply inputMean_mono
        intro i
        calc
          |a i * b i ^ 2| = |b i| * |a i * b i| := by rw [← abs_mul]; congr 1; ring
          _ ≤ n * |a i * b i| := mul_le_mul_of_nonneg_right (hbn i) (abs_nonneg _)
      _ = n * t := inputMean_const_mul _ _
  have hf : f ≤ n * (A * B) := by
    have hbpoint (i : I) : b i ^ 2 ≤ n * B := by
      calc
        b i ^ 2 ≤ ∑ j, b j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
        _ = n * B := sum_eq_card_mul_inputMean _
    calc
      f ≤ inputMean (fun i => a i ^ 2 * (n * B)) := by
        apply inputMean_mono
        intro i
        exact mul_le_mul_of_nonneg_left (hbpoint i) (sq_nonneg _)
      _ = A * (n * B) := inputMean_mul_const _ _
      _ = n * (A * B) := by ring
  have hden : inputMean (fun i => (a i + 1) * (b i + 1)) = 1 + c := by
    have hp : (fun i => (a i + 1) * (b i + 1)) =
        (fun i => a i * b i + a i + b i + 1) := by funext i; ring
    rw [hp, inputMean_add, inputMean_add, inputMean_add, ha, hb, inputMean_const]
    dsimp only [c]
    ring
  have hpoly : inputMean (fun i => (a i + 1) ^ 2 * (b i + 1) ^ 2) =
      1 + (A + B) + 4 * c + 2 * d + 2 * e + f := by
    have hp : (fun i => (a i + 1) ^ 2 * (b i + 1) ^ 2) =
        (fun i => 1 + 2 * a i + 2 * b i + a i ^ 2 + b i ^ 2 +
          4 * (a i * b i) + 2 * (a i ^ 2 * b i) + 2 * (a i * b i ^ 2) +
          a i ^ 2 * b i ^ 2) := by funext i; ring
    rw [hp]
    simp only [inputMean_add, inputMean_const_mul, inputMean_const, ha, hb]
    dsimp only [A, B, c, d, e, f]
    ring
  have hnum : 1 / 2 ≤ 1 + c →
      (H + 1) * (1 + c) = 1 + (A + B) + 4 * c + 2 * d + 2 * e + f := by
    intro hh
    have hz : 1 + c ≠ 0 := by linarith only [hh]
    dsimp only [H]
    rw [hden, sub_add_cancel, div_mul_cancel₀ _ hz, hpoly]
  have hglobal : H ≤ n * (1 + c) - 1 := by
    have hg := inputMean_ratio_le_card_mul (fun i => (a i + 1) * (b i + 1)) hab
    have hp : (fun i => ((a i + 1) * (b i + 1)) ^ 2) =
        (fun i => (a i + 1) ^ 2 * (b i + 1) ^ 2) := by funext i; ring
    rw [hp, hden] at hg
    dsimp only [H]
    rw [hden]
    linarith only [hg]
  have hh := corrected_ratio_bilinear_bound n (A + B) (A * B) c d e f t H
    (card_real_one_le (I := I)) (add_nonneg hA0 hB0)
    (by dsimp only [n, A, B]; linarith only [hA, hB]) hc ht hd he hf hnum hglobal
  dsimp only [n, A, B, c, d, e, H] at hh
  convert hh using 1; ring

private theorem weighted_centered_correction
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (w : Y → ℝ) (v : Z → ℝ) (a : Y → I → ℝ) (b : Z → I → ℝ)
    (A : Y → ℝ) (B : Z → ℝ)
    (ha : ∀ i, ∑ y, w y * a y i = 0)
    (hb : ∀ i, ∑ z, v z * b z i = 0) :
    (∑ yz : Y × Z, w yz.1 * v yz.2 *
      ((3 - A yz.1 - B yz.2) * inputMean (fun i => a yz.1 i * b yz.2 i) +
        2 * inputMean (fun i => a yz.1 i ^ 2 * b yz.2 i) +
        2 * inputMean (fun i => a yz.1 i * b yz.2 i ^ 2))) = 0 := by
  have hr (g : Y → I → ℝ) :
      (∑ yz : Y × Z, w yz.1 * v yz.2 *
        inputMean (fun i => g yz.1 i * b yz.2 i)) = 0 := by
    rw [weighted_inner_inputMean]
    simp only [hb, mul_zero]
    exact inputMean_const 0
  have hl (g : Z → I → ℝ) :
      (∑ yz : Y × Z, w yz.1 * v yz.2 *
        inputMean (fun i => a yz.1 i * g yz.2 i)) = 0 := by
    rw [weighted_inner_inputMean]
    simp only [ha, zero_mul]
    exact inputMean_const 0
  have hc := hr a
  have hd := hr (fun y i => a y i ^ 2)
  have he := hl (fun z i => b z i ^ 2)
  have hAc : (∑ yz : Y × Z, w yz.1 * v yz.2 *
      (A yz.1 * inputMean (fun i => a yz.1 i * b yz.2 i))) = 0 := by
    have hh := hr (fun y i => A y * a y i)
    simpa only [mul_assoc, inputMean_const_mul] using hh
  have hBc : (∑ yz : Y × Z, w yz.1 * v yz.2 *
      (inputMean (fun i => a yz.1 i * b yz.2 i) * B yz.2)) = 0 := by
    have hh := hl (fun z i => b z i * B z)
    simpa only [← mul_assoc, inputMean_mul_const] using hh
  calc
    _ = 3 * (∑ yz : Y × Z, w yz.1 * v yz.2 *
          inputMean (fun i => a yz.1 i * b yz.2 i)) -
        (∑ yz : Y × Z, w yz.1 * v yz.2 *
          (A yz.1 * inputMean (fun i => a yz.1 i * b yz.2 i))) -
        (∑ yz : Y × Z, w yz.1 * v yz.2 *
          (inputMean (fun i => a yz.1 i * b yz.2 i) * B yz.2)) +
        2 * (∑ yz : Y × Z, w yz.1 * v yz.2 *
          inputMean (fun i => a yz.1 i ^ 2 * b yz.2 i)) +
        2 * (∑ yz : Y × Z, w yz.1 * v yz.2 *
          inputMean (fun i => a yz.1 i * b yz.2 i ^ 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro yz _
      ring
    _ = 0 := by rw [hc, hd, he, hAc, hBc]; ring

omit [Nonempty I] in
private theorem weighted_pair_average
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (w : Y → ℝ) (v : Z → ℝ) (A : Y → ℝ) (B : Z → ℝ)
    (hw : ∑ y, w y = 1) (hv : ∑ z, v z = 1) :
    (∑ yz : Y × Z, w yz.1 * v yz.2 *
      (A yz.1 + B yz.2 + 14 * (Fintype.card I : ℝ) * A yz.1 * B yz.2)) =
      (∑ y, w y * A y) + (∑ z, v z * B z) +
      14 * (Fintype.card I : ℝ) * (∑ y, w y * A y) * (∑ z, v z * B z) := by
  rw [Fintype.sum_prod_type]
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ y, ∑ z, w y * v z * A y) = ∑ y, w y * A y := by
    apply Finset.sum_congr rfl
    intro y _
    calc
      _ = (w y * A y) * ∑ z, v z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = w y * A y := by rw [hv, mul_one]
  have h2 : (∑ y, ∑ z, w y * v z * B z) = ∑ z, v z * B z := by
    calc
      _ = (∑ y, w y) * (∑ z, v z * B z) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = ∑ z, v z * B z := by rw [hw, one_mul]
  have h3 : (∑ y, ∑ z, w y * v z * (14 * (Fintype.card I : ℝ) * A y * B z)) =
      14 * (Fintype.card I : ℝ) * (∑ y, w y * A y) * (∑ z, v z * B z) := by
    calc
      _ = 14 * (Fintype.card I : ℝ) *
          ((∑ y, w y * A y) * (∑ z, v z * B z)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by ring
  rw [h1, h2, h3]

/-- Calibrated likelihood fusion has a remainder bilinear in the two capacities. -/
theorem calibratedFusion_bilinear_bound
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (w : Y → ℝ) (x : Y → I → ℝ) (v : Z → ℝ) (r : Z → I → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hv0 : ∀ z, 0 ≤ v z)
    (hx0 : ∀ y i, 0 ≤ x y i) (hr0 : ∀ z i, 0 ≤ r z i)
    (hxm : ∀ y, inputMean (x y) = 1) (hrm : ∀ z, inputMean (r z) = 1)
    (hxc : ∀ i, ∑ y, w y * x y i = 1)
    (hrc : ∀ i, ∑ z, v z * r z i = 1) :
    calibratedFusion w x v r ≤ calibratedCapacity w x + calibratedCapacity v r +
      (14 * (Fintype.card I : ℝ)) * calibratedCapacity w x * calibratedCapacity v r := by
  have hw : ∑ y, w y = 1 := by
    simpa only [hxm, mul_one, hxc, inputMean_const] using weighted_sum_inputMean w x
  have hv : ∑ z, v z = 1 := by
    simpa only [hrm, mul_one, hrc, inputMean_const] using weighted_sum_inputMean v r
  let a : Y → I → ℝ := fun y i => x y i - 1
  let b : Z → I → ℝ := fun z i => r z i - 1
  let A : Y → ℝ := fun y => inputMean (fun i => a y i ^ 2)
  let B : Z → ℝ := fun z => inputMean (fun i => b z i ^ 2)
  let C : Y × Z → ℝ := fun yz =>
    (3 - A yz.1 - B yz.2) * inputMean (fun i => a yz.1 i * b yz.2 i) +
      2 * inputMean (fun i => a yz.1 i ^ 2 * b yz.2 i) +
      2 * inputMean (fun i => a yz.1 i * b yz.2 i ^ 2)
  have hxa (y : Y) := centered_energy (x y) (hx0 y) (hxm y)
  have hrb (z : Z) := centered_energy (r z) (hr0 z) (hrm z)
  have hac (i : I) : ∑ y, w y * a y i = 0 := by
    dsimp only [a]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hxc i, hw, sub_self]
  have hbc (i : I) : ∑ z, v z * b z i = 0 := by
    dsimp only [b]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hrc i, hv, sub_self]
  have hC : (∑ yz : Y × Z, w yz.1 * v yz.2 * C yz) = 0 :=
    weighted_centered_correction w v a b A B hac hbc
  have hcapA : (∑ y, w y * A y) = calibratedCapacity w x := by
    unfold calibratedCapacity
    apply Finset.sum_congr rfl
    intro y _
    rw [show A y = inputMean (fun i => x y i ^ 2) - 1 from (hxa y).2.1]
  have hcapB : (∑ z, v z * B z) = calibratedCapacity v r := by
    unfold calibratedCapacity
    apply Finset.sum_congr rfl
    intro z _
    rw [show B z = inputMean (fun i => r z i ^ 2) - 1 from (hrb z).2.1]
  have hp (yz : Y × Z) :
      inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
        inputMean (fun i => x yz.1 i * r yz.2 i) - 1 ≤
        A yz.1 + B yz.2 + C yz + 14 * (Fintype.card I : ℝ) * A yz.1 * B yz.2 := by
    have hh := centered_pair_bound (a yz.1) (b yz.2)
      (hxa yz.1).1 (hrb yz.2).1 (hxa yz.1).2.2.2.2 (hrb yz.2).2.2.2.2
      (hxa yz.1).2.2.2.1 (hrb yz.2).2.2.2.1
      (fun i => by
        dsimp only [a, b]
        simp only [sub_add_cancel]
        exact mul_nonneg (hx0 _ _) (hr0 _ _))
    simpa only [a, b, sub_add_cancel, A, B, C] using hh
  have hs : (∑ yz : Y × Z, w yz.1 * v yz.2 *
      (inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
        inputMean (fun i => x yz.1 i * r yz.2 i) - 1)) ≤
      ∑ yz : Y × Z, w yz.1 * v yz.2 *
        (A yz.1 + B yz.2 + C yz + 14 * (Fintype.card I : ℝ) * A yz.1 * B yz.2) := by
    apply Finset.sum_le_sum
    intro yz _
    exact mul_le_mul_of_nonneg_left (hp yz) (mul_nonneg (hw0 _) (hv0 _))
  have hweights : (∑ yz : Y × Z, w yz.1 * v yz.2) = 1 := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hw, hv, mul_one]
  have hleft : (∑ yz : Y × Z, w yz.1 * v yz.2 *
      (inputMean (fun i => x yz.1 i ^ 2 * r yz.2 i ^ 2) /
        inputMean (fun i => x yz.1 i * r yz.2 i) - 1)) = calibratedFusion w x v r := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hweights]
    rfl
  have hright : (∑ yz : Y × Z, w yz.1 * v yz.2 *
        (A yz.1 + B yz.2 + C yz + 14 * (Fintype.card I : ℝ) * A yz.1 * B yz.2)) =
      calibratedCapacity w x + calibratedCapacity v r +
        (14 * (Fintype.card I : ℝ)) * calibratedCapacity w x * calibratedCapacity v r := by
    calc
      _ = (∑ yz : Y × Z, w yz.1 * v yz.2 *
          (A yz.1 + B yz.2 + 14 * (Fintype.card I : ℝ) * A yz.1 * B yz.2)) +
          ∑ yz : Y × Z, w yz.1 * v yz.2 * C yz := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro yz _
        ring
      _ = _ := by rw [weighted_pair_average w v A B hw hv, hC, add_zero, hcapA, hcapB]
  rw [hleft, hright] at hs
  exact hs

end Omega.InformationTheory.PottsFusion
