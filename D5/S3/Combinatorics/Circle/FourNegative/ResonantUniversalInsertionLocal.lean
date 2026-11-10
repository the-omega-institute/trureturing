/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionLocal
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic parity split for a low resonant row above the boundary. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic

theorem resonant_low_row_parity {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell < k)
    (i : Fin k) (hi : i.val < ell) :
    let a := (m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i
    let p := (w : ℤ) * (2 : ℤ) ^ i.val
    (0 ≤ a ∧ 0 ≤ 2 * a - charge k w i) ∨
      (a ≤ 0 ∧ p - a ≤ resonantTargetH k ell - w) := by
  obtain ⟨_, hk, hwpos, hodd, hroom⟩ :=
    resonant_hypotheses_facts hw hell hm hdiv hlarge (by omega : ell ≤ k)
  let P : ℤ := 2 ^ i.val
  let s : ℤ := 2 ^ (k - 1 - i.val)
  let z : ℤ := (w : ℤ) / s
  let r : ℤ := (w : ℤ) % s
  let c : ℤ := charge k w i
  have hP : 1 ≤ P := by
    dsimp [P]
    exact one_le_pow₀ (by norm_num)
  have hP0 : 0 ≤ P := by omega
  have hm0 : 0 ≤ (m : ℤ) := by omega
  have hs : 2 ≤ s := by
    have he : 1 ≤ k - 1 - i.val := by omega
    simpa [s] using (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he)
  have hPs : P * s = (2 : ℤ) ^ (k - 1) := by
    dsimp [P, s]
    rw [← pow_add]
    congr 1
    omega
  have hpow : (2 : ℤ) ^ k = 2 * P * s := by
    rw [mul_assoc, hPs, ← pow_succ']
    congr 1
    omega
  have hsEven : s % 2 = 0 := by
    have he : k - 1 - i.val = (k - 2 - i.val) + 1 := by omega
    simp [s, he, pow_succ, Int.mul_emod]
  have hwlt : (w : ℤ) < P * s := by
    rw [hPs]
    exact_mod_cast (show w < 2 ^ (k - 1) by omega)
  have hr : 1 ≤ r ∧ r < s := by
    have hr0 := Int.emod_nonneg (w : ℤ) (by omega : s ≠ 0)
    have hrlt := Int.emod_lt_of_pos (w : ℤ) (by omega : 0 < s)
    have hdecomp := Int.emod_add_mul_ediv (w : ℤ) s
    have hoddNat : w % 2 = 1 := by
      rcases hodd with ⟨t, ht⟩
      omega
    have hoddInt : (w : ℤ) % 2 = 1 := by exact_mod_cast hoddNat
    have hoddR : r % 2 = 1 := by
      dsimp [r]
      rw [Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ s from
        Int.dvd_of_emod_eq_zero hsEven)]
      exact hoddInt
    dsimp [r] at *
    omega
  have hr0 : 0 ≤ r := by omega
  have hdecomp : (w : ℤ) = s * z + r := by
    have h := Int.emod_add_mul_ediv (w : ℤ) s
    dsimp [z, r]
    omega
  have hz : 0 ≤ z := Int.ediv_nonneg (by positivity) (by omega)
  have hzP : z < P := by
    have hsmall : (w : ℤ) < P * s := hwlt
    nlinarith
  have hc : c = z / 2 + z % 2 := by
    rfl
  have hc0 : 0 ≤ c := by
    have hmod := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
    have hdiv := Int.ediv_nonneg hz (by norm_num : (0 : ℤ) ≤ 2)
    rw [hc]
    omega
  have hcP : c ≤ P := by
    rw [hc]
    have hmod := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
    omega
  have hf := (digit_data k w hk hroom i).2.1
  change actualSource k w i = P * (w : ℤ) - ((2 : ℤ) ^ k - 1) * c at hf
  have hH : resonantTargetH k ell = (m : ℤ) * P * s - 1 := by
    obtain ⟨B, _, htarget, _⟩ := resonant_target_values hell hm (by omega : ell ≤ k)
    rw [htarget, ← hPs]
    ring
  have hmcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  dsimp only
  change
    (0 ≤ (m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i ∧
      0 ≤ 2 * ((m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i) -
        charge k w i) ∨
      ((m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i ≤ 0 ∧
        (w : ℤ) * (2 : ℤ) ^ i.val -
            ((m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i) ≤
          resonantTargetH k ell - w)
  have hmlarge : 3 * (w : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hlarge
  rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with he | ho
  · have heq : z = 2 * c := by rw [hc]; omega
    have hscaled := congrArg (fun t : ℤ => t * P) hdecomp
    rw [heq] at hscaled
    have ha : (m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i =
        (m : ℤ) * r * P + c := by
      rw [hf, hpow, hmcast]
      nlinarith [hscaled]
    left
    rw [ha]
    constructor
    · have hmr : 0 ≤ (m : ℤ) * r * P :=
        mul_nonneg (mul_nonneg hm0 hr0) hP0
      nlinarith
    · have hmr : 0 ≤ (m : ℤ) * r * P :=
        mul_nonneg (mul_nonneg hm0 hr0) hP0
      nlinarith
  · have heq : z = 2 * c - 1 := by rw [hc]; omega
    have hscaled := congrArg (fun t : ℤ => t * P) hdecomp
    rw [heq] at hscaled
    have ha : (m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i =
        -(m : ℤ) * P * s + (m : ℤ) * r * P + c := by
      rw [hf, hpow, hmcast]
      nlinarith [hscaled]
    have hc1 : 1 ≤ c := by rw [hc]; omega
    have hsr : 1 ≤ s - r := by omega
    have hmsr : (m : ℤ) * P * (s - r) ≥ P := by
      have hm1 : 1 ≤ (m : ℤ) := by omega
      have hmp : 0 ≤ (m : ℤ) * P := mul_nonneg hm0 hP0
      have hprod : 0 ≤ (m : ℤ) * P * (s - r - 1) :=
        mul_nonneg hmp (by omega)
      nlinarith
    have hma : (m : ℤ) * r * P ≥ (w : ℤ) * (P + 1) + 1 := by
      have hmr : (m : ℤ) * P ≤ (m : ℤ) * r * P := by
        have hprod : 0 ≤ (m : ℤ) * P * (r - 1) :=
          mul_nonneg (mul_nonneg hm0 hP0) (by omega)
        nlinarith
      have hml := mul_le_mul_of_nonneg_right hmlarge hP0
      have hterm : 0 ≤ (w : ℤ) * (2 * P - 1) :=
        mul_nonneg (by omega) (by omega)
      have hPterm : 0 ≤ P - 1 := by omega
      nlinarith [hmr, hml, hterm, hPterm]
    right
    rw [ha, hH]
    constructor
    · have hprod : 0 ≤ (m : ℤ) * P * (s - r) - c := by
        nlinarith [hmsr, hcP]
      nlinarith
    · nlinarith [hma, hc0]

theorem resonant_pair_midpoint (H C c w x y a p : ℤ) (b : Bool)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hCc : C + c ≤ w)
    (hp : 0 ≤ p) (hrel : y = 2 * x - C + w * (if b then 1 else 0))
    (hx : 0 ≤ x ∧ x ≤ H ∧ 0 ≤ y ∧ y ≤ 2 * H + 1)
    (hz : 0 ≤ x + a + p ∧ x + a + p ≤ H ∧
      0 ≤ y + 2 * a - c + 2 * p ∧ y + 2 * a - c + 2 * p ≤ 2 * H + 1)
    (hrow : (0 ≤ a ∧ 0 ≤ 2 * a - c) ∨
      (a ≤ 0 ∧ p - a ≤ H - w)) :
    if x + p ≤ corridorUpper H C w b then
      0 ≤ x + p ∧ x + p ≤ H ∧ 0 ≤ y + 2 * p ∧ y + 2 * p ≤ 2 * H + 1
    else
      0 ≤ x + a ∧ x + a ≤ H ∧ 0 ≤ y + 2 * a - c ∧
        y + 2 * a - c ≤ 2 * H + 1 := by
  have hxcor := (corridor_iff H C w x b ⟨hC, by omega⟩).mp (by
    exact ⟨hx.1, hx.2.1, by nlinarith [hrel], by nlinarith [hrel]⟩)
  have hzcor := (corridor_iff H (C + c) w (x + a + p) b
    ⟨by omega, hCc⟩).mp (by
      exact ⟨hz.1, hz.2.1, by nlinarith [hrel], by nlinarith [hrel]⟩)
  split_ifs with hfit
  · have hm := (corridor_iff H C w (x + p) b ⟨hC, by omega⟩).mpr
      ⟨by omega, hfit⟩
    have heq : 2 * (x + p) - C + w * (if b then 1 else 0) = y + 2 * p := by
      rw [hrel]
      ring
    simpa only [heq] using hm
  · rcases hrow with hpos | hneg
    · exact ⟨by omega, by omega, by omega, by omega⟩
    · have hm := negative_pair_corridor H C w c x a p b hC hc hCc
        hxcor hzcor hneg.1 hp hneg.2
      rw [if_neg hfit] at hm
      have hm' := (corridor_iff H (C + c) w (x + a) b
        ⟨by omega, hCc⟩).mpr hm
      have heq : 2 * (x + a) - (C + c) + w * (if b then 1 else 0) =
          y + 2 * a - c := by
        rw [hrel]
        ring
      simpa only [heq] using hm'

theorem resonant_target_double {ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hkl : ell ≤ k) :
    resonantTargetN k ell = 2 * resonantTargetH k ell + 1 := by
  obtain ⟨_, _, hH, hN⟩ := resonant_target_values hell hm hkl
  rw [hH, hN]
  ring

theorem resonant_state_relation {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (l : List (Fin (k + 1))) :
    resonantSecondState k ell w m l =
      2 * resonantFirstState k ell w m l -
        (l.map (resonantCharge k w)).sum +
        (w : ℤ) * (l.map (resonantEar k)).sum := by
  obtain ⟨_, hk, _, _, hroom⟩ := resonant_hypotheses_facts hw hell hm hdiv hlarge hkl
  have h := resonant_prefix_rows (k := k) (seed := w) hk hroom l
  simp only [resonantFirstState, resonantSecondState]
  rw [h.2]
  norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
  ring

def resonantPrefixEar {k : ℕ} (l : List (Fin (k + 1))) : Bool :=
  decide ((l.map (resonantEar k)).sum = 1)

def resonantAdaptiveOrientation (w ell k m : ℕ) (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) : Fin ell → Bool :=
  fun i => decide (¬ (resonantFirstState k ell w m
      (word.take (word.idxOf ⟨i.val, by omega⟩)) +
      (w : ℤ) * (2 : ℤ) ^ i.val ≤
      corridorUpper (resonantTargetH k ell)
        ((word.take (word.idxOf ⟨i.val, by omega⟩)).map
          (resonantCharge k w)).sum
        (w : ℤ)
        (resonantPrefixEar (word.take (word.idxOf ⟨i.val, by omega⟩)))))

theorem resonant_state_append {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (l : List (Fin (k + 1))) (j : Fin (k + 1)) :
    resonantFirstState k ell w m (l ++ [j]) =
        resonantFirstState k ell w m l +
          ((m : ℤ) * resonantFirst k w j - (m - 1 : ℕ) * resonantCharge k w j +
            (w : ℤ) * resonantLowWeight (ell := ell) j) ∧
    resonantSecondState k ell w m (l ++ [j]) =
        resonantSecondState k ell w m l +
          ((m : ℤ) * actualSource (k + 1) (2 * w) j -
            (m - 1 : ℕ) * resonantCharge k w j -
            (w : ℤ) * (m - 1 : ℕ) * resonantEar k j +
            (2 * w : ℤ) * resonantLowWeight (ell := ell) j) := by
  simp only [resonantFirstState, resonantSecondState, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  constructor <;> ring

theorem resonant_adaptive_block_strip {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell < k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word)
    (n : ℕ) (hn : n < word.length) :
    let o := resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
    let l := word.take n
    let j := word[n]
    InStrip (resonantTargetFirst k ell w) (resonantTargetH k ell)
        (resonantFirstState k ell w m l) (resonantBlock o j) ∧
      InStrip (resonantTargetSecond k ell w) (resonantTargetN k ell)
    (resonantSecondState k ell w m l) (resonantBlock o j) := by
  dsimp only
  let o := resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
  let l := word.take n
  let j := word[n]
  obtain ⟨_, hk2, _, _, hroom⟩ :=
    resonant_hypotheses_facts hw hell hm hdiv hlarge (by omega : ell ≤ k)
  have ht : word.take (n + 1) = l ++ [j] := List.take_succ_eq_append_getElem hn
  have hs := resonant_canonical_complete_prefix hw hell hm hdiv hlarge (by omega : ell ≤ k)
    word hsource n
  have hz := resonant_canonical_complete_prefix hw hell hm hdiv hlarge (by omega : ell ≤ k)
    word hsource (n + 1)
  rw [ht] at hz
  have hstep := resonant_state_append hw hell hm hdiv hlarge (by omega : ell ≤ k) l j
  have hdouble := resonant_target_double hell hm (by omega : ell ≤ k)
  rw [hdouble] at hs hz
  change InStrip _ _ _ (resonantBlock o j) ∧ InStrip _ _ _ (resonantBlock o j)
  by_cases hj : j.val < ell
  · let i : Fin k := ⟨j.val, by omega⟩
    have hji : j = i.castSucc := rfl
    have hnew := resonant_target_new_rows (w := w) (ell := ell) (k := k) (m := m)
      hell hm hroom hk2 ⟨j.val, hj⟩
    let x := resonantFirstState k ell w m l
    let y := resonantSecondState k ell w m l
    let C := (l.map (resonantCharge k w)).sum
    let e := (l.map (resonantEar k)).sum
    let c := resonantCharge k w j
    let a := (m : ℤ) * resonantFirst k w j - (m - 1 : ℕ) * c
    let p := (w : ℤ) * (2 : ℤ) ^ j.val
    have hinv := resonant_prefix_inventory (k := k) (seed := w) hk2 hroom word n hsource.1
    have hinv' := resonant_prefix_inventory (k := k) (seed := w) hk2 hroom word (n + 1) hsource.1
    rw [ht] at hinv'
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at hinv'
    have he0 : 0 ≤ e := by
      dsimp [e, l]
      exact hinv.2.1
    have he1 : e ≤ 1 := by
      dsimp [e, l]
      exact hinv.2.2
    have he : e = 0 ∨ e = 1 := by omega
    let b : Bool := resonantPrefixEar l
    have heb : e = if b then 1 else 0 := by
      dsimp [b, resonantPrefixEar]
      change e = if decide (e = 1) = true then 1 else 0
      rcases he with he | he <;> simp [he]
    have hrel : y = 2 * x - C + (w : ℤ) * (if b then 1 else 0) := by
      have h := resonant_state_relation hw hell hm hdiv hlarge (by omega : ell ≤ k) l
      dsimp [x, y, C, e] at *
      rw [← heb]
      exact h
    have hrow := resonant_source_rows (k := k) (seed := w) hk2 hroom j
    have hear : resonantEar k j = 0 := by
      rw [hji]
      simp [resonantEar, show i.val ≠ k by omega]
    have hlow : resonantLowWeight (ell := ell) j = (2 : ℤ) ^ j.val := by
      simp [resonantLowWeight, hj]
    have hsecond : (m : ℤ) * actualSource (k + 1) (2 * w) j -
        (m - 1 : ℕ) * resonantCharge k w j -
        (w : ℤ) * (m - 1 : ℕ) * resonantEar k j = 2 * a - c := by
      rw [hrow.2.2, hear]
      dsimp [a, c]
      norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    have hstepx : resonantFirstState k ell w m (l ++ [j]) = x + a + p := by
      rw [hstep.1, hlow]
      dsimp [x, a, p, c]
      ring
    have hstepy : resonantSecondState k ell w m (l ++ [j]) = y + 2 * a - c + 2 * p := by
      rw [hstep.2, hlow]
      dsimp [y, a, c, p]
      rw [hrow.2.2, hear]
      norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    have hpar := resonant_low_row_parity hw hell hm hdiv hlarge hkl i
      (by exact hj)
    have hpar' : (0 ≤ a ∧ 0 ≤ 2 * a - c) ∨
        (a ≤ 0 ∧ p - a ≤ resonantTargetH k ell - w) := by
      have hfi : resonantFirst k w i.castSucc = actualSource k w i := by
        simp [resonantFirst]
      have hci : resonantCharge k w i.castSucc = charge k w i := by
        simp [resonantCharge]
      simpa [a, c, p, hji, hfi, hci] using hpar
    have hmid := resonant_pair_midpoint (resonantTargetH k ell) C c (w : ℤ)
      x y a p b hinv.1.1 (resonant_source_rows (k := k) (seed := w)
        hk2 hroom j).1 (by exact hinv'.1.2)
      (by dsimp [p]; positivity) hrel
      (by exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩)
      (by rw [← hstepx, ← hstepy]; exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩) hpar'
    have hnd := hsource.1.nodup_iff.mpr (List.nodup_finRange _)
    have ho : o ⟨j.val, by omega⟩ =
        decide (¬ (x + p ≤ corridorUpper (resonantTargetH k ell) C
          (w : ℤ) b)) := by
      unfold o resonantAdaptiveOrientation
      have heq : (⟨j.val, by omega⟩ : Fin (k + 1)) = word[n] := rfl
      rw [heq, hnd.idxOf_getElem n hn]
    have hold := resonant_target_old_rows hell hm hw hdiv hlarge hroom hk2
      (by omega) j
    have hfirst := hold.1
    have hsecond' : resonantTargetSecond k ell w (liftOldLabel j) = 2 * a - c := by
      rw [hold.2, hsecond]
    have hnewx := hnew.1
    have hnewy : resonantTargetSecond k ell w (liftNewLabel ⟨j.val, hj⟩) = 2 * p := by
      rw [hnew.2]
      dsimp [p]
      ring
    unfold resonantBlock
    rw [dif_pos hj]
    change InStrip _ _ _ (if o ⟨j.val, hj⟩ then
        [liftOldLabel j, liftNewLabel ⟨j.val, hj⟩]
      else [liftNewLabel ⟨j.val, hj⟩, liftOldLabel j]) ∧
      InStrip _ _ _ (if o ⟨j.val, hj⟩ then
        [liftOldLabel j, liftNewLabel ⟨j.val, hj⟩]
      else [liftNewLabel ⟨j.val, hj⟩, liftOldLabel j])
    rw [ho]
    by_cases hfit : x + p ≤ corridorUpper (resonantTargetH k ell) C (w : ℤ) b
    · have hdecision : decide (¬ (x + p ≤ corridorUpper (resonantTargetH k ell) C
          (w : ℤ) b)) = false := by simp [hfit]
      rw [if_pos hfit] at hmid
      simp only [hfit, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
        InStrip, hfirst, hsecond', hnewx, hnewy]
      rw [hstepx, hstepy] at hz
      dsimp [x, y, l, a, p, C, c, e, b] at hs hz hmid ⊢
      constructor <;> (repeat' constructor) <;> omega
    · have hdecision : decide (¬ (x + p ≤ corridorUpper (resonantTargetH k ell) C
          (w : ℤ) b)) = true := by simp [hfit]
      rw [if_neg hfit] at hmid
      simp only [hfit, not_false_eq_true, decide_true, if_true,
        InStrip, hfirst, hsecond', hnewx, hnewy]
      rw [hstepx, hstepy] at hz
      dsimp [x, y, l, a, p, C, c, e, b] at hs hz hmid ⊢
      constructor <;> (repeat' constructor) <;> omega
  · have hlow : resonantLowWeight (ell := ell) j = 0 := by
      simp [resonantLowWeight, hj]
    have hold := resonant_target_old_rows hell hm hw hdiv hlarge hroom hk2
      (by omega) j
    simp only [resonantBlock, dif_neg hj, InStrip]
    rw [hold.1, hold.2]
    rw [hlow] at hstep
    simp only [mul_zero, add_zero] at hstep
    rw [← hold.1, ← hold.2] at hstep
    dsimp [l] at hs hz hstep ⊢
    constructor <;> (repeat' constructor) <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
