/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDesubstitution
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDesubstitution
   mirror-E: none(waiver:characteristic-majority-index-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Nth, mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Majority ranks reconstruct the characteristic word by two mechanical blocks. -/

import Mathlib.Data.Nat.Nth
import Mathlib.Data.List.OfFn
import D5.S1.Words.BalancedThreshold.BalancedThresholdPalettes
import D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Inverting the floor crossings identifies every majority occurrence. Induction then
reconstructs the entire word from the one- and two-letter blocks of the ratio rotation. -/
theorem mechanical_majority_desubstitution {alpha : ℝ}
    (h0 : 0 < alpha) (hhalf : alpha < 1 / 2) :
    let theta := alpha / (1 - alpha)
    let u := lowerMechanicalWord alpha alpha
    let v := lowerMechanicalWord theta theta
    let pos := Nat.nth (fun n => u n = false)
    ∀ k : ℕ,
      pos k = k + (⌊((k + 1 : ℕ) : ℝ) * theta⌋).toNat ∧
      List.ofFn (wordFactor u (pos k) 0) =
        (List.range k).flatMap (fun r => if v r then [false, true] else [false]) := by
  classical
  let theta := alpha / (1 - alpha)
  let u := lowerMechanicalWord alpha alpha
  let v := lowerMechanicalWord theta theta
  let pos := Nat.nth (fun n => u n = false)
  let q := fun k : ℕ => ⌊((k + 1 : ℕ) : ℝ) * theta⌋
  let f := fun k : ℕ => k + (q k).toNat
  have h1 : alpha < 1 := by linarith
  have hb : 0 < 1 - alpha := by linarith
  have ht0 : 0 < theta := div_pos h0 hb
  have ht1 : theta < 1 := by
    dsimp [theta]
    rw [div_lt_one hb]
    linarith
  have htheta : theta * (1 - alpha) = alpha := by
    dsimp [theta]
    exact div_mul_cancel₀ _ hb.ne'
  have qnonneg : ∀ k, 0 ≤ q k := by
    intro k
    dsimp [q]
    exact Int.floor_nonneg.mpr (by positivity)
  have qcast : ∀ k, ((q k).toNat : ℝ) = q k := by
    intro k
    exact_mod_cast Int.toNat_of_nonneg (qnonneg k)
  have floors : ∀ k,
      ⌊alpha + (f k : ℝ) * alpha⌋ = q k ∧
      ⌊alpha + ((f k + 1 : ℕ) : ℝ) * alpha⌋ = q k := by
    intro k
    have hlo := Int.floor_le (((k + 1 : ℕ) : ℝ) * theta)
    have hhi := Int.lt_floor_add_one (((k + 1 : ℕ) : ℝ) * theta)
    change (q k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * theta at hlo
    change ((k + 1 : ℕ) : ℝ) * theta < (q k : ℝ) + 1 at hhi
    have hlow := mul_le_mul_of_nonneg_right hlo hb.le
    have hhigh := mul_lt_mul_of_pos_right hhi hb
    rw [mul_assoc, htheta] at hlow hhigh
    have hid : (f k : ℝ) = (k : ℝ) + q k := by
      simp only [f, Nat.cast_add, qcast]
    push_cast at hlow hhigh
    rw [hid]
    constructor
    · apply Int.floor_eq_iff.mpr
      constructor <;> nlinarith only [hlow, hhigh, h0, h1]
    · apply Int.floor_eq_iff.mpr
      push_cast
      rw [hid]
      constructor <;> nlinarith only [hlow, hhigh, h0, h1]
  have false_at : ∀ k, u (f k) = false := by
    intro k
    simp only [u, lowerMechanicalWord, lowerMechanicalLetter, (floors k).1,
      (floors k).2, sub_self]
    norm_num
  have rank : ∀ k, Nat.count (fun n => u n = false) (f k) = k := by
    intro k
    have hc := lowerMechanicalWindowTrueCount_eq_floor (rho := alpha) h0.le h1 0 (f k)
    simp only [zero_add, Nat.cast_zero, zero_mul, add_zero,
      Int.floor_eq_zero_iff.mpr ⟨h0.le, h1⟩, sub_zero, (floors k).1] at hc
    have htrue : Nat.count (fun n => u n = true) (f k) = (q k).toNat := by
      have he : lowerMechanicalWindowTrueCount alpha alpha 0 (f k) =
          (q k).toNat := by omega
      simpa only [Nat.count_eq_card_filter_range, lowerMechanicalWindowTrueCount,
        Nat.zero_add, u] using he
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.range (f k)) (p := fun n => u n = true)
    have hsum' : Nat.count (fun n => u n = true) (f k) +
        Nat.count (fun n => u n = false) (f k) = f k := by
      simpa only [Nat.count_eq_card_filter_range, Bool.not_eq_true,
        Finset.card_range] using hsum
    rw [htrue] at hsum'
    change (q k).toNat + Nat.count (fun n => u n = false) (f k) =
      k + (q k).toNat at hsum'
    omega
  have position : ∀ k, pos k = f k := by
    intro k
    simpa only [rank k] using Nat.nth_count (p := fun n => u n = false) (false_at k)
  have step : ∀ k, f (k + 1) = f k + if v k then 2 else 1 := by
    intro k
    have hz := lowerMechanicalLetter_eq_zero_or_one (rho := theta) ht0.le ht1 k
    have hid : lowerMechanicalLetter theta theta k = q (k + 1) - q k := by
      unfold lowerMechanicalLetter q
      congr 1 <;> congr 1 <;> push_cast <;> ring
    have hqk := qnonneg k
    have hqk1 := qnonneg (k + 1)
    rcases hz with hz | hz
    · have hv : v k = false := by simp [v, lowerMechanicalWord, hz]
      simp only [hv, Bool.false_eq_true, if_false]
      rw [hid] at hz
      dsimp [f]
      omega
    · have hv : v k = true := by simp [v, lowerMechanicalWord, hz]
      simp only [hv, if_true]
      rw [hid] at hz
      dsimp [f]
      omega
  have gap_true : ∀ k, v k = true → u (f k + 1) = true := by
    intro k hk
    have hs : f (k + 1) = f k + 2 := by simpa [hk] using step k
    have hq : q (k + 1) = q k + 1 := by
      dsimp [f] at hs
      have := qnonneg k
      have := qnonneg (k + 1)
      omega
    have hnext := (floors (k + 1)).1
    rw [hs, hq] at hnext
    apply (lowerMechanicalWord_eq_true_iff alpha alpha (f k + 1)).mpr
    unfold lowerMechanicalLetter
    rw [show f k + 1 + 1 = f k + 2 by omega, hnext, (floors k).2]
    simp
  have reconstructed : ∀ k,
      List.ofFn (wordFactor u (f k) 0) =
        (List.range k).flatMap (fun r => if v r then [false, true] else [false]) := by
    intro k
    induction k with
    | zero =>
      have hf : f 0 = 0 := by
        simp [f, q, Int.floor_eq_zero_iff.mpr ⟨ht0.le, ht1⟩]
      simp [hf]
    | succ k ih =>
      have he : wordFactor u (f k) 0 = (fun r : Fin (f k) => u r) := by
        funext r
        simp [wordFactor]
      rw [he] at ih
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      cases hv : v k with
      | false =>
        have hs : f (k + 1) = f k + 1 := by simpa [hv] using step k
        rw [hs, List.ofFn_succ']
        simp only [List.concat_eq_append, wordFactor, Nat.zero_add, Fin.val_castSucc,
          Fin.val_last]
        rw [ih, false_at]
        simp
      | true =>
        have hs : f (k + 1) = f k + 2 := by simpa [hv] using step k
        rw [hs, show f k + 2 = (f k + 1) + 1 by omega,
          List.ofFn_succ', List.ofFn_succ']
        simp only [List.concat_eq_append, wordFactor, Nat.zero_add, Fin.val_castSucc,
          Fin.val_last]
        rw [ih, false_at, gap_true k hv]
        simp [List.append_assoc]
  change ∀ k, pos k = f k ∧ List.ofFn (wordFactor u (pos k) 0) =
    (List.range k).flatMap (fun r => if v r then [false, true] else [false])
  intro k
  refine ⟨position k, ?_⟩
  rw [position k]
  exact reconstructed k

end D5.S1.Words.BalancedThreshold
