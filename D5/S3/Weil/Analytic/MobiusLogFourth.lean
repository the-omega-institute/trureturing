/- GID: D5/S3/Weil/Analytic/MobiusLogFourth
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/MobiusLogFourth
   mirror-E: none(waiver:mobius-log-fourth)
   anchors: []
   utility: none
   digest: The centered recurrence gives unconditional fourth-logarithmic decay for Möbius prefixes. -/

import D5.S3.Weil.Analytic.MertensLogFourthContraction
import D5.S3.Weil.Analytic.MobiusCenteredHyperbola
import D5.S3.Weil.Analytic.MobiusDiscreteAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination

/-! A logarithmic Mertens bound from the centered Mangoldt recurrence. -/

set_option autoImplicit false

noncomputable section

open Finset Filter
open scoped Topology

namespace MobiusLogFourth

open MobiusCenteredHyperbola
open MertensLogFourthContraction

private def abelCorrection (N : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 N, mobiusPrefix (m : ℝ) *
    (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))

private theorem abs_abelCorrection_le {x y R U : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hR : 0 ≤ R) (hU : 0 < U) {N : ℕ} (hN : (N : ℝ) ≤ x)
    (hbound : ∀ t : ℝ, x / y ≤ t → t ≤ x → |mobiusPrefix t| ≤ R * t / U) :
    |abelCorrection N| ≤ x / y + x * (R / U) := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hxy : 0 ≤ x / y := div_nonneg hx₀ hy₀.le
  have hRU : 0 ≤ R / U := div_nonneg hR hU.le
  let small : Finset ℕ := (Ioc 0 N).filter (fun m : ℕ => (m : ℝ) ≤ x / y)
  have hsmall : small ⊆ Ioc 0 ⌊x / y⌋₊ := by
    intro m hm
    obtain ⟨hmN, hmx⟩ := mem_filter.mp hm
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hmN).1, Nat.le_floor hmx⟩
  have hcount : (small.card : ℝ) ≤ x / y := by
    have hc := Finset.card_le_card hsmall
    rw [Nat.card_Ioc, Nat.sub_zero] at hc
    exact (by exact_mod_cast hc : (small.card : ℝ) ≤ (⌊x / y⌋₊ : ℝ)).trans
      (Nat.floor_le hxy)
  have hterm (m : ℕ) (hm : m ∈ Ioc 0 N) :
      |mobiusPrefix (m : ℝ) *
          (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))| ≤
        (if (m : ℝ) ≤ x / y then (1 : ℝ) else 0) + R / U := by
    have hm₀ : 0 < m := (mem_Ioc.mp hm).1
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm₀
    have hmX : (m : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hm).2).trans hN
    have hinc₀ : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hmR (by exact_mod_cast Nat.le_succ m))
    rw [abs_mul, abs_of_nonneg hinc₀]
    refine (mul_le_mul_of_nonneg_left (MobiusDiscreteAbel.log_increment_le_reciprocal hm₀)
      (abs_nonneg _)).trans ?_
    by_cases hmxy : (m : ℝ) ≤ x / y
    · rw [if_pos hmxy]
      calc
        _ ≤ (m : ℝ) * (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_mobiusPrefix_le hmR.le) (inv_nonneg.mpr hmR.le)
        _ = 1 := mul_inv_cancel₀ hmR.ne'
        _ ≤ _ := by linarith
    · rw [if_neg hmxy, zero_add]
      calc
        _ ≤ (R * (m : ℝ) / U) * (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hbound _ (le_of_not_ge hmxy) hmX)
            (inv_nonneg.mpr hmR.le)
        _ = R / U := by field_simp
  unfold abelCorrection
  calc
    _ ≤ ∑ m ∈ Ioc 0 N, ((if (m : ℝ) ≤ x / y then (1 : ℝ) else 0) + R / U) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (small.card : ℝ) + (N : ℝ) * (R / U) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [small, nsmul_eq_mul]
    _ ≤ _ := add_le_add hcount (mul_le_mul_of_nonneg_right hN hRU)

private theorem weighted_prefix_bound {x y R U : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hyx : y ≤ x) (hR : 0 ≤ R) (hU : 0 < U)
    (hbound : ∀ t : ℝ, x / y ≤ t → t ≤ x → |mobiusPrefix t| ≤ R * t / U) :
    Real.log x * |mobiusPrefix x| ≤
      |head x y| + |tail x y| + x / y + x * (R / U) + 2 := by
  let n := ⌊x⌋₊
  have hn₁ : 1 ≤ n := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have hsucc : n - 1 + 1 = n := by omega
  have hab := MobiusDiscreteAbel.log_weight_eq_prefix_sub (n - 1)
  rw [hsucc] at hab
  change (∑ m ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius m : ℝ) * Real.log (m : ℝ)) = _ at hab
  rw [sum_log_weighted_moebius x y hx hyx] at hab
  have hcorr :
      (∑ m ∈ Ioc 0 (n - 1), (∑ j ∈ Ioc 0 m, (ArithmeticFunction.moebius j : ℝ)) *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))) = abelCorrection (n - 1) := by
    simp [abelCorrection, mobiusPrefix]
  rw [hcorr] at hab
  change -1 - head x y - tail x y =
    mobiusPrefix x * Real.log (⌊x⌋₊ : ℝ) - abelCorrection (n - 1) at hab
  let gap := mobiusPrefix x * (Real.log x - Real.log (⌊x⌋₊ : ℝ))
  have hgap : |gap| ≤ 1 := abs_mobiusPrefix_mul_log_floor_gap hx
  have hEq : Real.log x * mobiusPrefix x =
      -1 - head x y - tail x y + abelCorrection (n - 1) + gap := by
    dsimp [gap]
    linear_combination -hab
  have hN : ((n - 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (zero_le_one.trans hx))
  have hAb := abs_abelCorrection_le hx hy hR hU hN hbound
  rw [← abs_of_nonneg (Real.log_nonneg hx), ← abs_mul, hEq]
  have hTri := abs_add_le (-1 - head x y - tail x y + abelCorrection (n - 1)) gap
  have hQ := abs_add_le (-1 - head x y - tail x y) (abelCorrection (n - 1))
  have hT := abs_sub (-1 - head x y) (tail x y)
  have hH := abs_sub (-1 : ℝ) (head x y)
  rw [abs_neg, abs_one] at hH
  linarith only [hTri, hQ, hT, hH, hAb, hgap]

/-- The unconditional centered recurrence gives fourth-logarithmic-power
decay for ordinary Möbius prefixes. -/
theorem mobiusPrefix_fourth_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x > (1 : ℝ), |mobiusPrefix x| ≤ K * x / Real.log x ^ 4 := by
  obtain ⟨D, hD, htail⟩ := abs_tail_eighth_root_le 3
  have hpowSmall := (isLittleO_log_rpow_rpow_atTop (s := 1 / 8) 3
    (by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (htail.and (hpowSmall.and (eventually_gt_atTop (1 : ℝ))))
  apply fourth_log_bound_of_recurrence mobiusPrefix
    (C := Real.log 4 + 5) (D := D + 3) (X₀ := max T 2)
    (by positivity) (by positivity) (by exact le_max_of_le_right (by norm_num))
    (fun x hx => abs_mobiusPrefix_le (zero_le_one.trans hx))
  intro x hx R hR henv
  obtain ⟨htailX, hlogPow, hx₁⟩ := hT x ((le_max_left _ _).trans hx)
  let y := cutoff x
  let U := Real.log (x / y) ^ 4
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hy₁ : 1 ≤ y := cutoff_ge_one hx₁.le
  have hyx : y ≤ x := cutoff_le hx₁.le
  have hlog : 0 < Real.log x := Real.log_pos hx₁
  have hU : 0 < U := by
    dsimp [U, y]
    rw [log_div_cutoff hx₀]
    positivity
  have hbound (t : ℝ) (ht : x / y ≤ t) (htx : t ≤ x) :
      |mobiusPrefix t| ≤ R * t / U :=
    bound_on_cutoff_interval hx₁ ht (henv t ⟨ht, htx⟩)
  have hcost : Real.log x ^ 3 ≤ y := by
    dsimp [y, cutoff]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx₀.le _),
      abs_of_nonneg (Real.rpow_nonneg hlog.le _), abs_of_nonneg (pow_nonneg hlog.le _),
      one_mul, Real.rpow_ofNat] using hlogPow
  have hsmall : x / y + 2 ≤ 3 * x / Real.log x ^ 3 := by
    have hsingle := div_le_div_of_nonneg_left hx₀.le (pow_pos hlog _) hcost
    have hone : 1 ≤ x / Real.log x ^ 3 := (le_div_iff₀ (pow_pos hlog _)).mpr
      (by simpa using hcost.trans hyx)
    rw [mul_div_assoc]
    linarith only [hsingle, hone]
  have hhead := abs_head_le hx₁.le hy₁ hR hU hbound
  have hmain := weighted_prefix_bound hx₁.le hy₁ hyx hR hU hbound
  change |tail x y| ≤ D * x / Real.log x ^ 3 at htailX
  calc
    _ ≤ |head x y| + |tail x y| + x / y + x * (R / U) + 2 := hmain
    _ ≤ (x / U) * (R * (2 * Real.log y + (Real.log 4 + 5))) +
      D * x / Real.log x ^ 3 + x * (R / U) + 3 * x / Real.log x ^ 3 := by
        linarith only [hhead, htailX, hsmall]
    _ = _ := by ring

end MobiusLogFourth
