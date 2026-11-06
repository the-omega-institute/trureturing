import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.TwoNegativeJointLift
import D5.S3.Combinatorics.Circle.DyadicPrefix

/-! Source-only preparation for the lower-half two-bit boundary.
    This file is intentionally uncompiled; the future guarded build owns
    elaboration, kernel and axiom-closure acceptance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.BelowHalfBoundary
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private two_blocks split_perm source_total inserted_perm from
  D5.S3.Combinatorics.Circle.TwoNegativeJointLift

private theorem half_pow_facts (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    let L : ℤ := 2 ^ (a - 1)
    let p : ℤ := 2 ^ (b - 1)
    2 ≤ L ∧ 2 ≤ p ∧ (2 : ℤ) ^ a = 2 * L ∧
      (2 : ℤ) ^ b = 2 * p ∧
      (2 : ℤ) ^ (a - 2) * 2 = L ∧
      (2 : ℤ) ^ (b - 2) * 2 = p := by
  dsimp only
  have hL := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show 1 ≤ a - 1 by omega)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show 1 ≤ b - 1 by omega)
  have haE : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) := congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hbE : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) := congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have ha2 : (2 : ℤ) ^ (a - 2) * 2 = 2 ^ (a - 1) := by
    rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
  have hb2 : (2 : ℤ) ^ (b - 2) * 2 = 2 ^ (b - 1) := by
    rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]
  refine ⟨by simpa using hL, by simpa using hp, haE, hbE, ha2, hb2⟩

set_option maxHeartbeats 10000000 in
private theorem boundary_joint (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ (a + b - 2) + 2 ^ (b - 2)) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 2) + 2 ^ (b - 2)))
        (earWord (a + b) sigma cut) := by
  classical
  let r := a + b
  let L : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let q : ℤ := 2 ^ (r - 2) + 2 ^ (b - 2)
  let H := 2 * p * L - 1
  let N := 4 * p * L - 1
  let B := 2 * p * L - p - 1
  let C := 2 * p * L - L - 1
  let D := 4 * p * L - 2 * p - 1
  let E := 4 * p * L - L - 1
  let f := actualSource r (2 ^ (r - 2) + 2 ^ (b - 2))
  let gn := actualSource (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
  let g := fun i : Fin r => gn i.castSucc
  let one : Fin r := ⟨1, by dsimp [r]; omega⟩
  let atA : Fin r := ⟨a + 1, by dsimp [r]; omega⟩
  let fresh : Fin (r + 1) := Fin.last r
  obtain ⟨hL, hp, haE, hbE, ha2, hb2⟩ := half_pow_facts a b ha hb
  change 2 ≤ L at hL
  change 2 ≤ p at hp
  change (2 : ℤ) ^ a = 2 * L at haE
  change (2 : ℤ) ^ b = 2 * p at hbE
  have hpow : (2 : ℤ) ^ (r - 2) = p * L := by
    have he : r - 2 = (a - 1) + (b - 1) := by dsimp [r]; omega
    dsimp [p, L]
    rw [he, pow_add]
    ring
  have hpowb : (2 : ℤ) ^ (b - 2) = p / 2 := by
    have := hb2
    dsimp [p] at this ⊢
    omega
  have hpHalf : 2 * (p / 2) = p := by
    have hh := hb2
    change (2 : ℤ) ^ (b - 2) * 2 = p at hh
    omega
  have hq : q = p * L + p / 2 := by
    dsimp [q]
    rw [hpow, hpowb]
  have hqv : q = p * L + (2 : ℤ) ^ (b - 2) := by
    rw [hq, hpowb]
  have hqNat : ((2 ^ (r - 2) + 2 ^ (b - 2) : ℕ) : ℤ) = q := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  have hrpow : (2 : ℤ) ^ r = 4 * p * L := by
    dsimp [r]
    rw [pow_add, haE, hbE]
    ring
  have hN : modulus r = 4 * p * L - 1 := by
    dsimp [modulus]
    rw [hrpow]
  have hM : modulus (r + 1) = 8 * p * L - 1 := by
    dsimp [modulus]
    rw [pow_succ, hrpow]
    ring
  have hNposNat : 0 < modulus r :=
    (TwoRunSource.modulus_positive_odd r (by dsimp [r]; omega)).1
  have hMposNat : 0 < modulus (r + 1) :=
    (TwoRunSource.modulus_positive_odd (r + 1) (by dsimp [r]; omega)).1
  have hNpos : (0 : ℤ) < modulus r := by exact_mod_cast hNposNat
  have hMpos : (0 : ℤ) < modulus (r + 1) := by exact_mod_cast hMposNat
  have hNodd : (modulus r : ℤ) % 2 = 1 := by exact_mod_cast
    (TwoRunSource.modulus_positive_odd r (by dsimp [r]; omega)).2
  have hModd : (modulus (r + 1) : ℤ) % 2 = 1 := by exact_mod_cast
    (TwoRunSource.modulus_positive_odd (r + 1) (by dsimp [r]; omega)).2
  have hN2 : (modulus r : ℤ) = 2 * (2 * p * L) - 1 := by rw [hN]; ring
  have hM2 : (modulus (r + 1) : ℤ) = 2 * (4 * p * L) - 1 := by rw [hM]; ring
  have hNH : (modulus r : ℤ) / 2 = H := by rw [hN2]; dsimp [H]; omega
  have hMH : (modulus (r + 1) : ℤ) / 2 = N := by rw [hM2]; dsimp [N]; omega
  have old_value (i : Fin r) (x m : ℤ)
      (hx : -(modulus r / 2) ≤ x ∧ x ≤ modulus r / 2)
      (he : (2 : ℤ) ^ i.val * (q : ℤ) = x + m * modulus r) : f i = x := by
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _)
      (by simpa [hNH] using hx)
    change centered (modulus r) ((2 : ℤ) ^ i.val *
      ((2 ^ (r - 2) + 2 ^ (b - 2) : ℕ) : ℤ)) % modulus r = x % modulus r
    rw [hqNat]
    rw [centered_mod, he]
    simp [Int.add_emod, Int.mul_emod]
  have new_value (i : Fin (r + 1)) (x m : ℤ)
      (hx : -N ≤ x ∧ x ≤ N)
      (he : (2 : ℤ) ^ i.val * ((2 * q : ℤ)) = x + m * modulus (r + 1)) : gn i = x := by
    apply centered_unique hMpos hModd (centered_bounds hMpos hModd _)
      (by simpa [hMH] using hx)
    change centered (modulus (r + 1)) ((2 : ℤ) ^ i.val *
      ((2 * (2 ^ (r - 2) + 2 ^ (b - 2)) : ℕ) : ℤ)) % modulus (r + 1) = x % modulus (r + 1)
    rw [show ((2 * (2 ^ (r - 2) + 2 ^ (b - 2)) : ℕ) : ℤ) = 2 * q by
      norm_num [hqNat]]
    rw [centered_mod, he]
    simp [Int.add_emod, Int.mul_emod]
  have hvalues (i : Fin r) :
      f i = (if i.val = 0 then q else if i.val = 1 then -B
        else if i.val < a + 1 then (2 * p + 1) * 2 ^ (i.val - 2)
        else if i.val = a + 1 then -C else (2 * L + 1) * 2 ^ (i.val - a - 2)) ∧
      g i = (if i.val = 0 then 2 * q else if i.val = 1 then -D
        else if i.val < a + 1 then (4 * p + 1) * 2 ^ (i.val - 2)
        else if i.val = a + 1 then -E else (2 * L + 1) * 2 ^ (i.val - a - 2)) := by
    by_cases h0 : i.val = 0
    · have hi0 : i = ⟨0, by dsimp [r]; omega⟩ := Fin.ext h0
      rw [hi0]
      simp only [Fin.val_mk, if_pos]
      constructor
      · apply old_value _ q 0 (by rw [hq]; constructor <;> nlinarith)
        simp [q]
      · apply new_value _ (2 * q) 0 (by constructor <;> nlinarith)
        simp [q, hM]
    by_cases h1 : i.val = 1
    · simp only [h0, if_false, h1, if_pos]
      constructor
      · apply old_value i (-B) 1 (by constructor <;> nlinarith)
        simp only [h1]
        rw [hq, hN]
        dsimp [B]
        nlinarith [hpHalf]
      · apply new_value i.castSucc (-D) 1 (by dsimp [N, D]; constructor <;> nlinarith)
        simp only [Fin.val_castSucc, h1, Nat.cast_ofNat]
        rw [hq, hM]
        dsimp [D]
        nlinarith [hpHalf]
    by_cases hlt : i.val < a + 1
    · have hi2 : 2 ≤ i.val := by omega
      simp only [h0, h1, if_false, hlt, if_pos]
      let z : ℤ := 2 ^ (i.val - 2)
      have hz : 0 < z := by dsimp [z]; positivity
      have hiE : (2 : ℤ) ^ i.val = 4 * z := by
        rw [show i.val = (i.val - 2) + 2 by omega, pow_add]
        dsimp [z]
        ring
      have hzL : 2 * z ≤ L := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (i.val - 2) + 1 ≤ a - 1 by omega)
        simpa only [pow_succ, z, L, mul_comm] using hh
      have hpz : 2 * p * z ≤ p * L := by
        nlinarith [mul_le_mul_of_nonneg_left hzL (show 0 ≤ p by omega)]
      have hpL : 2 * L ≤ p * L :=
        mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
      have hOldBank : -H ≤ (2 * p + 1) * z ∧ (2 * p + 1) * z ≤ H := by
        have ht : 0 ≤ (2 * p + 1) * z := by positivity
        dsimp [H]; constructor <;> nlinarith [hpz, hpL]
      have hNewBank : -N ≤ (4 * p + 1) * z ∧ (4 * p + 1) * z ≤ N := by
        have ht : 0 ≤ (4 * p + 1) * z := by positivity
        dsimp [N]; constructor <;> nlinarith [hpz, hpL]
      constructor
      · apply old_value i _ z (by simpa only [hNH] using hOldBank)
        rw [hiE, hq, hN]
        linear_combination 2 * z * hpHalf
      · apply new_value i.castSucc _ z hNewBank
        simp only [Fin.val_castSucc]
        rw [hiE, hq, hM]
        linear_combination 4 * z * hpHalf
    by_cases ha1 : i.val = a + 1
    · have ha0 : a + 1 ≠ 0 := by omega
      have haone : a + 1 ≠ 1 := by omega
      simp only [h0, h1, hlt, if_false, ha1, if_pos, ha0, haone,
        lt_self_iff_false]
      constructor
      · apply old_value i (-C) (L + 1) (by
          rw [hNH]; dsimp [H, C]; constructor <;> nlinarith)
        rw [ha1, pow_succ, haE, hq, hN]
        dsimp [C]
        linear_combination 2 * L * hpHalf
      · apply new_value i.castSucc (-E) (L + 1) (by
          dsimp [N, E]; constructor <;> nlinarith)
        simp only [Fin.val_castSucc]
        rw [ha1, pow_succ, haE, hq, hM]
        dsimp [E]
        linear_combination 4 * L * hpHalf
    · simp only [h0, h1, hlt, if_false, ha1, if_false]
      let z : ℤ := 2 ^ (i.val - a - 2)
      have hz : 0 < z := by dsimp [z]; positivity
      have hiE : (2 : ℤ) ^ i.val = 8 * L * z := by
        have ha2pow : (2 : ℤ) ^ (a + 2) = 8 * L := by
          rw [show a + 2 = (a - 1) + 3 by omega, pow_add]
          dsimp [L]
          ring
        rw [show i.val = (a + 2) + (i.val - a - 2) by omega, pow_add, ha2pow]
      have hltb : i.val - a - 2 < b - 2 := by
        have hi := i.isLt
        dsimp [r] at hi
        omega
      have hzp : 4 * z ≤ p := by
        have hh : (2 : ℤ) ^ ((i.val - a - 2) + 2) ≤ (2 : ℤ) ^ (b - 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
        calc
          4 * z = (2 : ℤ) ^ 2 * (2 : ℤ) ^ (i.val - a - 2) := by dsimp [z]
          _ = (2 : ℤ) ^ ((i.val - a - 2) + 2) := by rw [pow_add]; ring
          _ ≤ (2 : ℤ) ^ (b - 1) := hh
          _ = p := by rfl
      have hPL : 2 * L ≤ p * L :=
        mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
      have hLP : 2 * p ≤ p * L := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega))
      have hmul : (2 * L + 1) * (4 * z) ≤ (2 * L + 1) * p :=
        mul_le_mul_of_nonneg_left hzp (by nlinarith)
      have hboundOld : (2 * L + 1) * z ≤ H := by
        dsimp [H]
        nlinarith [hmul, hLP]
      have hboundNew : (2 * L + 1) * z ≤ N := by
        dsimp [N]
        nlinarith [hmul, hLP]
      have hH0 : 0 ≤ H := by dsimp [H]; nlinarith [hLP]
      have hN0 : 0 ≤ N := by dsimp [N]; nlinarith [hLP]
      constructor
      · apply old_value i ((2 * L + 1) * z) ((2 * L + 1) * z)
          (by rw [hNH]; exact ⟨by nlinarith [hH0, hz], hboundOld⟩)
        rw [hiE, hq, hN]
        linear_combination 4 * L * z * hpHalf
      · apply new_value i.castSucc ((2 * L + 1) * z) ((2 * L + 1) * z)
          (by exact ⟨by nlinarith [hN0, hz], hboundNew⟩)
        simp only [Fin.val_castSucc]
        rw [hiE, hq, hM]
        linear_combination 8 * L * z * hpHalf
  have hFresh : gn fresh = q := by
    apply new_value fresh q q (by rw [hq]; constructor <;> nlinarith)
    change (2 : ℤ) ^ r * (2 * q) = q + q * modulus (r + 1)
    rw [hrpow, hq, hM]
    ring

  have build (x y : ℤ) (alpha beta : Fin r) (halpha : f alpha = -((if alpha = one then B else C)))
      (hbeta : f beta = -((if alpha = one then C else B)))
      (galpha : g alpha = -((if alpha = one then D else E)))
      (gbeta : g beta = -((if alpha = one then E else D)))
      (halabel : alpha = one ∨ alpha = atA)
      (hblabel : beta = one ∨ beta = atA)
      (hab : alpha ≠ beta)
      (hlastOld : 0 ≤ (if alpha = one then C else B) ∧
        (if alpha = one then C else B) ≤ H)
      (hlastNew : 0 ≤ (if alpha = one then E else D) ∧
        (if alpha = one then E else D) ≤ N)
      (hx0 : 0 ≤ x) (hxL : x < L) (hy0 : 0 ≤ y) (hyp : y < p)
      (hPlo : (if alpha = one then B else C) ≤ (2 * p + 1) * x + (2 * L + 1) * y)
      (hPhi : (2 * p + 1) * x + (2 * L + 1) * y ≤ H)
      (hGlo : (if alpha = one then D else E) ≤
        ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + q)
      (hGhi : ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + q ≤ N) :
      ∃ sigma : List (Fin r), ∃ cut : ℕ, cut ≤ r ∧
        OriginalOrder r (2 ^ (r - 2) + 2 ^ (b - 2)) sigma ∧
        OriginalOrder (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2)))
          (earWord r sigma cut) := by
    have hPL : 2 * L ≤ p * L :=
      mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
    have hLP : 2 * p ≤ p * L :=
      by simpa [mul_comm] using (mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega))
    have hpL4 : 4 ≤ p * L := by nlinarith only [hPL, hL]
    have hB0 : 0 ≤ B := by dsimp [B]; nlinarith only [hLP, hpL4]
    have hC0 : 0 ≤ C := by dsimp [C]; nlinarith only [hPL, hpL4]
    have hD0 : 0 ≤ D := by dsimp [D]; nlinarith only [hLP, hpL4]
    have hE0 : 0 ≤ E := by dsimp [E]; nlinarith only [hPL, hpL4]
    have hfirstOld : 0 ≤ (if alpha = one then B else C) := by
      split_ifs <;> assumption
    have hfirstNew : 0 ≤ (if alpha = one then D else E) := by
      split_ifs <;> assumption
    let hxNat : x.toNat < 2 ^ (a - 1) := by
      have hx : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
      exact_mod_cast (show (x.toNat : ℤ) < (2 : ℤ) ^ (a - 1) by rw [hx]; exact hxL)
    let hyNat : y.toNat < 2 ^ (b - 1) := by
      have hy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
      exact_mod_cast (show (y.toNat : ℤ) < (2 : ℤ) ^ (b - 1) by rw [hy]; exact hyp)
    let maskU := DyadicPrefix.bitSubset (a - 1) x.toNat hxNat
    let maskV := DyadicPrefix.bitSubset (b - 1) y.toNat hyNat
    let labelU : Fin (a - 1) → Fin r := fun i => ⟨i.val + 2, by dsimp [r]; omega⟩
    let labelV : Fin (b - 1) → Fin r := fun i =>
      if h : i.val = b - 2 then ⟨0, by dsimp [r]; omega⟩
      else ⟨a + 2 + i.val, by
        dsimp [r]
        have hi := i.isLt
        omega⟩
    have injU : Function.Injective labelU := by
      intro i j h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp [labelU] at hh; omega
    have injV : Function.Injective labelV := by
      intro i j h
      by_cases hi : i.val = b - 2 <;> by_cases hj : j.val = b - 2
      · apply Fin.ext; omega
      · simp [labelV, hi, hj] at h
        omega
      · simp [labelV, hi, hj] at h
      · apply Fin.ext; simp [labelV, hi, hj] at h ⊢; omega
    let EU := maskU.image labelU
    let EV := maskV.image labelV
    let ES := EU ∪ EV
    let FS := Finset.univ \ (ES ∪ {alpha, beta})
    let E0 := ES.toList
    let F0 := FS.toList
    have hdisj : Disjoint EU EV := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hi
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hj
      have hh := congrArg Fin.val (hui.trans hvi.symm)
      by_cases hu' : u.val = b - 2
      · by_cases hv' : v.val = b - 2 <;> simp [labelU, labelV, hu', hv'] at hh <;> omega
      · by_cases hv' : v.val = b - 2
        · simp [labelU, labelV, hu', hv'] at hh
        · simp [labelU, labelV, hu', hv'] at hh
          omega
    have outside (i : Fin r) (hi : i ∈ ES) : i ≠ alpha ∧ i ≠ beta := by
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
        constructor <;> intro hh
        · rcases halabel with rfl | rfl <;> have hu' := u.isLt <;>
            have he := congrArg Fin.val hh <;> dsimp [labelU, one, atA] at he <;> omega
        · rcases hblabel with rfl | rfl <;> have hu' := u.isLt <;>
            have he := congrArg Fin.val hh <;> dsimp [labelU, one, atA] at he <;> omega
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
        constructor <;> intro hh
        · rcases halabel with rfl | rfl <;> by_cases hv' : v.val = b - 2 <;>
            have he := congrArg Fin.val hh <;> simp [labelV, hv', one, atA] at he <;> omega
        · rcases hblabel with rfl | rfl <;> by_cases hv' : v.val = b - 2 <;>
            have he := congrArg Fin.val hh <;> simp [labelV, hv', one, atA] at he <;> omega
    have hEa : alpha ∉ ES := fun hi => (outside alpha hi).1 rfl
    have hEb : beta ∉ ES := fun hi => (outside beta hi).2 rfl
    have hperm : (E0 ++ F0 ++ [alpha, beta]).Perm (List.finRange r) :=
      split_perm ES alpha beta hab hEa hEb
    have hmaskU : (∑ i ∈ maskU, (2 : ℤ) ^ i.val) = x := by
      have hh : (∑ i ∈ maskU, (2 : ℤ) ^ i.val) = (x.toNat : ℤ) := by
        exact_mod_cast DyadicPrefix.bit_subset_sum hxNat
      exact hh.trans (Int.toNat_of_nonneg hx0)
    have hmaskV : (∑ i ∈ maskV, (2 : ℤ) ^ i.val) = y := by
      have hh : (∑ i ∈ maskV, (2 : ℤ) ^ i.val) = (y.toNat : ℤ) := by
        exact_mod_cast DyadicPrefix.bit_subset_sum hyNat
      exact hh.trans (Int.toNat_of_nonneg hy0)
    have hUold (i : Fin (a - 1)) : f (labelU i) = (2 * p + 1) * 2 ^ i.val := by
      have h0 : (labelU i).val ≠ 0 := by dsimp [labelU]; omega
      have h1 : (labelU i).val ≠ 1 := by dsimp [labelU]; omega
      have hlt : (labelU i).val < a + 1 := by dsimp [labelU]; omega
      simpa [h0, h1, hlt, labelU] using (hvalues (labelU i)).1
    have hUnew (i : Fin (a - 1)) : g (labelU i) = (4 * p + 1) * 2 ^ i.val := by
      have h0 : (labelU i).val ≠ 0 := by dsimp [labelU]; omega
      have h1 : (labelU i).val ≠ 1 := by dsimp [labelU]; omega
      have hlt : (labelU i).val < a + 1 := by dsimp [labelU]; omega
      simpa [h0, h1, hlt, labelU] using (hvalues (labelU i)).2
    have hVold (i : Fin (b - 1)) : f (labelV i) = (2 * L + 1) * 2 ^ i.val := by
      by_cases hi : i.val = b - 2
      · have hv := hvalues (labelV i)
        have hqtop : q = (2 * L + 1) * (2 : ℤ) ^ (b - 2) := by
          rw [hq, hpowb]
          calc
            p * L + p / 2 = L * p + p / 2 := by ring
            _ = L * (2 * (p / 2)) + p / 2 := by rw [hpHalf]
            _ = (2 * L + 1) * (p / 2) := by ring
        calc
          f (labelV i) = q := by simpa [labelV, hi] using hv.1
          _ = (2 * L + 1) * 2 ^ i.val := by rw [hi]; exact hqtop
      · have hv := hvalues (labelV i)
        have hval : (labelV i).val = a + 2 + i.val := by simp [labelV, hi]
        have h0 : (labelV i).val ≠ 0 := by rw [hval]; omega
        have h1 : (labelV i).val ≠ 1 := by rw [hval]; omega
        have hlt : ¬ (labelV i).val < a + 1 := by rw [hval]; omega
        have hA : (labelV i).val ≠ a + 1 := by rw [hval]; omega
        have h0' : (a + 2 + i.val : ℕ) ≠ 0 := by omega
        have h1' : (a + 2 + i.val : ℕ) ≠ 1 := by omega
        have hlt' : ¬ (a + 2 + i.val < a + 1) := by omega
        have hA' : (a + 2 + i.val : ℕ) ≠ a + 1 := by omega
        have hexp : a + 2 + i.val - a - 2 = i.val := by omega
        have hlabel : labelV i = ⟨a + 2 + i.val, by dsimp [r]; omega⟩ := by simp [labelV, hi]
        rw [hlabel] at hv ⊢
        simpa [h0', h1', hlt', hA', hexp] using hv.1
    have hVnew (i : Fin (b - 1)) :
        g (labelV i) = (2 * L + 1) * 2 ^ i.val +
          (if i.val = b - 2 then q else 0) := by
      by_cases hi : i.val = b - 2
      · have hv := hvalues (labelV i)
        have hqtop : q = (2 * L + 1) * (2 : ℤ) ^ (b - 2) := by
          rw [hq, hpowb]
          calc
            p * L + p / 2 = L * p + p / 2 := by ring
            _ = L * (2 * (p / 2)) + p / 2 := by rw [hpHalf]
            _ = (2 * L + 1) * (p / 2) := by ring
        calc
          g (labelV i) = 2 * q := by simpa [labelV, hi] using hv.2
          _ = (2 * L + 1) * 2 ^ i.val + (if i.val = b - 2 then q else 0) := by
            simp only [hi, if_pos]
            nlinarith [hqtop]
      · have hv := hvalues (labelV i)
        have hval : (labelV i).val = a + 2 + i.val := by simp [labelV, hi]
        have h0 : (labelV i).val ≠ 0 := by rw [hval]; omega
        have h1 : (labelV i).val ≠ 1 := by rw [hval]; omega
        have hlt : ¬ (labelV i).val < a + 1 := by rw [hval]; omega
        have hA : (labelV i).val ≠ a + 1 := by rw [hval]; omega
        have h0' : (a + 2 + i.val : ℕ) ≠ 0 := by omega
        have h1' : (a + 2 + i.val : ℕ) ≠ 1 := by omega
        have hlt' : ¬ (a + 2 + i.val < a + 1) := by omega
        have hA' : (a + 2 + i.val : ℕ) ≠ a + 1 := by omega
        have hexp : a + 2 + i.val - a - 2 = i.val := by omega
        have hlabel : labelV i = ⟨a + 2 + i.val, by dsimp [r]; omega⟩ := by simp [labelV, hi]
        rw [hlabel] at hv ⊢
        simpa [hi, h0', h1', hlt', hA', hexp] using hv.2
    have hEUold : (EU.toList.map f).sum = (2 * p + 1) * x := by
      rw [← List.sum_toFinset _ EU.nodup_toList, Finset.toList_toFinset]
      rw [Finset.sum_image (fun i _ j _ hij => injU hij)]
      change (∑ i ∈ maskU, f (labelU i)) = _
      calc
        (∑ i ∈ maskU, f (labelU i)) =
            ∑ i ∈ maskU, ((2 * p + 1) * 2 ^ i.val) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hUold i
        _ = (2 * p + 1) * x := by rw [← Finset.mul_sum, hmaskU]
    have hEVold : (EV.toList.map f).sum = (2 * L + 1) * y := by
      rw [← List.sum_toFinset _ EV.nodup_toList, Finset.toList_toFinset]
      rw [Finset.sum_image (fun i _ j _ hij => injV hij)]
      change (∑ i ∈ maskV, f (labelV i)) = _
      calc
        (∑ i ∈ maskV, f (labelV i)) =
            ∑ i ∈ maskV, ((2 * L + 1) * 2 ^ i.val) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hVold i
        _ = (2 * L + 1) * y := by rw [← Finset.mul_sum, hmaskV]
    let P := (2 * p + 1) * x + (2 * L + 1) * y
    have hPnonneg : 0 ≤ P := by dsimp [P]; positivity
    have hEold : (E0.map f).sum = P := by
      change ((EU ∪ EV).toList.map f).sum = P
      rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
      change (∑ i ∈ EU ∪ EV, f i) = P
      rw [Finset.sum_union hdisj]
      dsimp only [EU, EV]
      rw [Finset.sum_image (fun i _ j _ hij => injU hij),
        Finset.sum_image (fun i _ j _ hij => injV hij)]
      simp_rw [show ∀ i, f (labelU i) = (2 * p + 1) * 2 ^ i.val from hUold,
        show ∀ i, f (labelV i) = (2 * L + 1) * 2 ^ i.val from hVold]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hmaskU, hmaskV]
    have hpos (i : Fin r) (hi : i ≠ one ∧ i ≠ atA) : 0 ≤ f i ∧ 0 ≤ g i := by
      by_cases h0 : i.val = 0
      · have hv := hvalues i
        simp only [h0, if_pos] at hv
        rw [hv.1, hv.2]
        constructor <;> dsimp [q] <;> positivity
      have h1 : i.val ≠ 1 := by intro hh; exact hi.1 (Fin.ext (by dsimp [one]; omega))
      have hA : i.val ≠ a + 1 := by intro hh; exact hi.2 (Fin.ext (by dsimp [atA]; omega))
      have hv := hvalues i
      by_cases hlt : i.val < a + 1
      · simp only [h0, h1, hlt, if_false, if_pos] at hv
        rw [hv.1, hv.2]; constructor <;> positivity
      · simp only [h0, h1, hlt, if_false, hA, if_false] at hv
        rw [hv.1, hv.2]; constructor <;> positivity
    have otherLabels (i : Fin r) (hi : i ≠ alpha ∧ i ≠ beta) :
        i ≠ one ∧ i ≠ atA := by
      rcases halabel with hα | hα <;> rcases hblabel with hβ | hβ
      · exact False.elim (hab (hα.trans hβ.symm))
      · simpa only [hα, hβ] using hi
      · simpa only [hα, hβ, and_comm] using hi
      · exact False.elim (hab (hα.trans hβ.symm))
    have Epos : ∀ i ∈ E0, 0 ≤ f i ∧ 0 ≤ g i := by
      intro i hi
      exact hpos i (otherLabels i (outside i (Finset.mem_toList.mp hi)))
    have Fpos : ∀ i ∈ F0, 0 ≤ f i ∧ 0 ≤ g i := by
      intro i hi
      have hh := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2
      apply hpos i
      apply otherLabels i
      constructor <;> intro h <;> apply hh <;> simp [h]
    let sigma := E0 ++ [alpha] ++ F0 ++ [beta]
    have hsperm : sigma.Perm (List.finRange r) := by
      have hswap : sigma.Perm (E0 ++ F0 ++ [alpha,beta]) := by
        simpa [sigma, List.append_assoc, List.cons_append] using
          ((List.perm_append_comm (l₁ := [alpha]) (l₂ := F0)).append_right [beta]).append_left E0
      exact hswap.trans hperm
    have hzero : (sigma.map f).sum = 0 := source_total (show 0 < r by dsimp [r]; omega) sigma hsperm
    have hsold : InStrip f H 0 sigma := by
      apply two_blocks f H E0 F0 alpha beta
        (fun i hi => (Epos i hi).1) (fun i hi => (Fpos i hi).1)
      · simpa [sigma, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, add_assoc] using hzero
      · rw [hEold]
        exact ⟨hPnonneg, hPhi⟩
      · rw [hEold, halpha]; dsimp [P]; linarith
      · rw [hbeta]; simpa only [neg_neg] using hlastOld
    let EN := E0.map Fin.castSucc
    let FN := F0.map Fin.castSucc
    have hENold : (EN.map gn).sum = (E0.map g).sum := by rw [List.map_map]; rfl
    have hEnew : (E0.map g).sum = P + 2 * p * x +
        (if (⟨b - 2, by omega⟩ : Fin (b - 1)) ∈ maskV then q else 0) := by
      change ((EU ∪ EV).toList.map g).sum = _
      rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
      change (∑ i ∈ EU ∪ EV, g i) = _
      rw [Finset.sum_union hdisj]
      dsimp [EU, EV]
      rw [Finset.sum_image (fun i _ j _ hij => injU hij),
        Finset.sum_image (fun i _ j _ hij => injV hij)]
      simp_rw [show ∀ i, g (labelU i) = (4 * p + 1) * 2 ^ i.val from hUnew,
        show ∀ i, g (labelV i) = (2 * L + 1) * 2 ^ i.val +
          (if i.val = b - 2 then q else 0) from hVnew]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmaskU, ← Finset.mul_sum, hmaskV]
      have htop : ∑ i ∈ maskV, (if i.val = b - 2 then q else 0) =
          if (⟨b - 2, by omega⟩ : Fin (b - 1)) ∈ maskV then q else 0 := by
        let top : Fin (b - 1) := ⟨b - 2, by omega⟩
        have hpoint : ∀ i : Fin (b - 1),
            (if i.val = b - 2 then q else 0) = (if i = top then q else 0) := by
          intro i
          by_cases hi : i = top
          · subst i; simp [top]
          · by_cases hv : i.val = b - 2
            · exfalso; apply hi; apply Fin.ext; dsimp [top]; omega
            · simp [hi, hv, top]
        rw [show (∑ i ∈ maskV, (if i.val = b - 2 then q else 0)) =
            ∑ i ∈ maskV, (if i = top then q else 0) by
              apply Finset.sum_congr rfl; intro i hi; exact hpoint i]
        by_cases ht : top ∈ maskV
        · have hsum : (∑ i ∈ maskV, (if i = top then q else 0)) =
              (if top = top then q else 0) := by
            apply Finset.sum_eq_single_of_mem top ht
            intro b hb hne
            simp [hne]
          rw [hsum]
          simp [top, ht]
        · rw [if_neg ht]
          apply Finset.sum_eq_zero
          intro i hi
          by_cases hh : i = top
          · exact False.elim (ht (hh ▸ hi))
          · simp [hh]
      rw [htop]
      dsimp [P]
      ring
    have ENpos : ∀ i ∈ EN, 0 ≤ gn i := by
      intro i hi; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi; exact (Epos j hj).2
    have FNpos : ∀ i ∈ FN, 0 ≤ gn i := by
      intro i hi; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi; exact (Fpos j hj).2
    have hFreshPos : 0 ≤ gn fresh := by rw [hFresh]; positivity
    have hgalpha : gn alpha.castSucc = (if alpha = one then -D else -E) := by
      change g alpha = _
      by_cases hα : alpha = one <;> simp [hα] at *
      · exact galpha
      · exact galpha
    have hgbeta : gn beta.castSucc = (if alpha = one then -E else -D) := by
      change g beta = _
      by_cases hα : alpha = one <;> simp [hα] at *
      · exact gbeta
      · exact gbeta
    by_cases ht : (⟨b - 2, by omega⟩ : Fin (b - 1)) ∈ maskV
    · have hEN : (EN.map gn).sum = P + 2 * p * x + q := by
        rw [hENold, hEnew, if_pos ht]
      have hnewstrip : InStrip gn N 0 (earWord r sigma (E0.length + 1 + F0.length)) := by
        have hnp := inserted_perm sigma (E0.length + 1 + F0.length) hsperm
        have hz := source_total (t := 2 * (2 ^ (r - 2) + 2 ^ (b - 2))) (show 0 < r + 1 by omega) _ hnp
        have hear : earWord r sigma (E0.length + 1 + F0.length) =
            EN ++ [alpha.castSucc] ++ FN ++ [fresh, beta.castSucc] := by
          have hA : (E0 ++ [alpha] ++ F0).length = E0.length + 1 + F0.length := by
            simp only [List.length_append, List.length_singleton]
          have hsigma : sigma = (E0 ++ [alpha] ++ F0) ++ [beta] := by
            simp [sigma, List.append_assoc]
          rw [hsigma, ← hA]
          unfold earWord
          rw [List.take_left, List.drop_left]
          simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append]
        rw [hear] at hz ⊢
        rw [show EN ++ [alpha.castSucc] ++ FN ++ [fresh, beta.castSucc] =
            EN ++ [alpha.castSucc] ++ (FN ++ [fresh]) ++ [beta.castSucc] by
              simp [List.append_assoc]]
        apply two_blocks gn N EN (FN ++ [fresh]) alpha.castSucc beta.castSucc ENpos
          (by intro i hi; rcases List.mem_append.mp hi with hi | hi
              · exact FNpos i hi
              · simp only [List.mem_singleton] at hi; subst i; exact hFreshPos)
        · simpa [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            add_assoc] using hz
        · rw [hEN]; exact ⟨by dsimp [P]; linarith [hPlo, hfirstOld], hGhi⟩
        · rw [hEN, hgalpha]; dsimp [P]; linarith [hGlo]
        · rw [hgbeta]
          by_cases hα : alpha = one
          · simpa only [hα, if_pos, neg_neg] using hlastNew
          · simpa only [hα, if_false, neg_neg] using hlastNew
      refine ⟨sigma, E0.length + 1 + F0.length, ?_, ?_, ?_⟩
      · have hh := hsperm.length_eq; simp [sigma] at hh; omega
      · refine ⟨hsperm, hzero, ?_⟩; intro n; change _ ∈ Set.Icc _ _; rw [hNH]; simpa using inStrip_prefix hsold n
      · refine ⟨inserted_perm sigma _ hsperm, source_total (show 0 < r + 1 by omega) _ (inserted_perm sigma _ hsperm), ?_⟩
        intro n; change _ ∈ Set.Icc _ _; rw [hMH]; simpa using inStrip_prefix hnewstrip n
    · have hEN : (EN.map gn).sum = P + 2 * p * x := by
        rw [hENold, hEnew, if_neg ht]
        ring
      have hnewstrip : InStrip gn N 0 (earWord r sigma E0.length) := by
        have hnp := inserted_perm sigma E0.length hsperm
        have hz := source_total (t := 2 * (2 ^ (r - 2) + 2 ^ (b - 2))) (show 0 < r + 1 by omega) _ hnp
        have hear : earWord r sigma E0.length =
            EN ++ [fresh] ++ [alpha.castSucc] ++ FN ++ [beta.castSucc] := by
          simp only [sigma, List.append_assoc]
          unfold earWord
          rw [List.take_left, List.drop_left]
          simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append]
        rw [hear] at hz ⊢
        apply two_blocks gn N (EN ++ [fresh]) FN alpha.castSucc beta.castSucc
          (by intro i hi; rcases List.mem_append.mp hi with hi | hi
              · exact ENpos i hi
              · simp only [List.mem_singleton] at hi; subst i; exact hFreshPos)
          FNpos
        · simpa [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            add_assoc] using hz
        · simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
          rw [hEN, hFresh]
          exact ⟨by dsimp [P]; linarith [hGlo, hfirstNew], hGhi⟩
        · rw [List.map_append, List.sum_append, hEN]
          simp only [List.map_singleton, List.sum_singleton]
          rw [hFresh, hgalpha]
          dsimp [P]; linarith [hGlo]
        · rw [hgbeta]
          by_cases hα : alpha = one
          · simpa only [hα, if_pos, neg_neg] using hlastNew
          · simpa only [hα, if_false, neg_neg] using hlastNew
      refine ⟨sigma, E0.length, ?_, ?_, ?_⟩
      · have hh := hsperm.length_eq; simp [sigma] at hh; omega
      · refine ⟨hsperm, hzero, ?_⟩; intro n; change _ ∈ Set.Icc _ _; rw [hNH]; simpa using inStrip_prefix hsold n
      · refine ⟨inserted_perm sigma _ hsperm, source_total (show 0 < r + 1 by omega) _ (inserted_perm sigma _ hsperm), ?_⟩
        intro n; change _ ∈ Set.Icc _ _; rw [hMH]; simpa using inStrip_prefix hnewstrip n

  have honeA : one ≠ atA := by
    intro hh
    have hv := congrArg Fin.val hh
    dsimp [one, atA] at hv
    omega
  have hAtA : atA ≠ one := Ne.symm honeA
  have hnegativeValues : f one = -B ∧ g one = -D ∧ f atA = -C ∧ g atA = -E := by
    have h1 := hvalues one
    have hA := hvalues atA
    have hA0 : a + 1 ≠ 0 := by omega
    have hA1 : a + 1 ≠ 1 := by omega
    simp only [one, Fin.val_mk, Nat.one_ne_zero, if_false, if_pos] at h1
    simp only [atA, Fin.val_mk, hA0, hA1, if_false, lt_self_iff_false, if_pos] at hA
    exact ⟨h1.1, h1.2, hA.1, hA.2⟩
  have orientValues (alpha beta : Fin r)
      (horient : (alpha = one ∧ beta = atA) ∨ (alpha = atA ∧ beta = one)) :
      f alpha = -(if alpha = one then B else C) ∧
        f beta = -(if alpha = one then C else B) ∧
        g alpha = -(if alpha = one then D else E) ∧
        g beta = -(if alpha = one then E else D) := by
    rcases horient with h | h
    · rw [h.1, h.2]
      simpa only [if_pos, if_false, honeA, hAtA, neg_neg] using
        And.intro hnegativeValues.1 (And.intro hnegativeValues.2.2.1
          (And.intro hnegativeValues.2.1 hnegativeValues.2.2.2))
    · rw [h.1, h.2]
      simpa only [if_pos, if_false, honeA, hAtA, neg_neg] using
        And.intro hnegativeValues.2.2.1 (And.intro hnegativeValues.1
          (And.intro hnegativeValues.2.2.2 hnegativeValues.2.1))
  set_option maxHeartbeats 100000000 in
  have chart (x y : ℤ) (alpha beta : Fin r)
      (horient : (alpha = one ∧ beta = atA) ∨ (alpha = atA ∧ beta = one))
      (horder : if alpha = one then L ≤ p else 2 * p ≤ L)
      (hxl : 0 ≤ x ∧ x < L) (hyl : 0 ≤ y ∧ y < p)
      (hPlo : (if alpha = one then B else C) ≤ (2 * p + 1) * x + (2 * L + 1) * y)
      (hPhi : (2 * p + 1) * x + (2 * L + 1) * y ≤ H)
      (hGlo : (if alpha = one then D else E) ≤
        ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + q)
      (hGhi : ((2 * p + 1) * x + (2 * L + 1) * y) + 2 * p * x + q ≤ N) :
      ∃ sigma : List (Fin r), ∃ cut : ℕ, cut ≤ r ∧
        OriginalOrder r (2 ^ (r - 2) + 2 ^ (b - 2)) sigma ∧
        OriginalOrder (r + 1) (2 * (2 ^ (r - 2) + 2 ^ (b - 2))) (earWord r sigma cut) := by
    have hPL : 2 * L ≤ p * L :=
      mul_le_mul_of_nonneg_right hp (show 0 ≤ L by omega)
    have hLP : 2 * p ≤ p * L := by
      simpa [mul_comm] using (mul_le_mul_of_nonneg_left hL (show 0 ≤ p by omega))
    have hpL4 : 4 ≤ p * L := by
      calc
        4 = (2 : ℤ) * 2 := by norm_num
        _ ≤ p * L := mul_le_mul hp hL (by norm_num) (by omega)
    have hB0 : 0 ≤ B := by
      dsimp [B]
      nlinarith only [hLP, hp]
    have hC0 : 0 ≤ C := by
      dsimp [C]
      nlinarith only [hPL, hL]
    have hD0 : 0 ≤ D := by
      dsimp [D]
      nlinarith only [hLP, hp]
    have hE0 : 0 ≤ E := by
      dsimp [E]
      nlinarith only [hPL, hL]
    have hfirstOld : 0 ≤ (if alpha = one then B else C) := by
      split_ifs <;> assumption
    have hfirstNew : 0 ≤ (if alpha = one then D else E) := by
      split_ifs <;> assumption
    have hmagOrder :
        (if alpha = one then B else C) ≤ (if alpha = one then C else B) ∧
        (if alpha = one then D else E) ≤ (if alpha = one then E else D) := by
      by_cases hα : alpha = one
      · simp only [hα, if_pos] at horder ⊢
        have hL2p : L ≤ 2 * p := by
          have hp0 : 0 ≤ p := by omega
          linarith only [horder, hp0]
        constructor
        · dsimp [B, C]
          linarith only [horder]
        · dsimp [D, E]
          linarith only [hL2p]
      · simp only [hα, if_false] at horder ⊢
        have hpL : p ≤ L := by
          have hp0 : 0 ≤ p := by omega
          linarith only [horder, hp0]
        constructor
        · dsimp [C, B]
          linarith only [hpL]
        · dsimp [E, D]
          linarith only [horder]
    have hlastOld : 0 ≤ (if alpha = one then C else B) ∧
        (if alpha = one then C else B) ≤ H := by
      refine ⟨le_trans hfirstOld hmagOrder.1, ?_⟩
      by_cases hα : alpha = one
      · simp only [hα, if_pos]
        dsimp [C, H]
        linarith only [hL]
      · simp only [hα, if_false]
        dsimp [B, H]
        linarith only [hp]
    have hlastNew : 0 ≤ (if alpha = one then E else D) ∧
        (if alpha = one then E else D) ≤ N := by
      refine ⟨le_trans hfirstNew hmagOrder.2, ?_⟩
      by_cases hα : alpha = one
      · simp only [hα, if_pos]
        dsimp [E, N]
        linarith only [hL]
      · simp only [hα, if_false]
        dsimp [D, N]
        linarith only [hp]
    have halabel : alpha = one ∨ alpha = atA := horient.elim
      (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hblabel : beta = one ∨ beta = atA := horient.elim
      (fun h => Or.inr h.2) (fun h => Or.inl h.2)
    have habLabels : alpha ≠ beta := by
      rcases horient with h | h
      · intro hab
        exact honeA (h.1.symm.trans (hab.trans h.2))
      · intro hab
        exact hAtA (h.1.symm.trans (hab.trans h.2))
    have hvals := orientValues alpha beta horient
    refine build x y alpha beta ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hvals.1
    · exact hvals.2.1
    · exact hvals.2.2.1
    · exact hvals.2.2.2
    · exact halabel
    · exact hblabel
    · exact habLabels
    · exact hlastOld
    · exact hlastNew
    · exact hxl.1
    · exact hxl.2
    · exact hyl.1
    · exact hyl.2
    · exact hPlo
    · exact hPhi
    · exact hGlo
    · exact hGhi

  have hu : (2 : ℤ) ^ (a - 2) > 0 := by positivity
  have vv : (2 : ℤ) ^ (b - 2) > 0 := by positivity
  have hL2 : L = 2 * (2 : ℤ) ^ (a - 2) := by
    dsimp [L]
    calc
      (2 : ℤ) ^ (a - 1) = (2 : ℤ) ^ (a - 2) * 2 := ha2.symm
      _ = 2 * (2 : ℤ) ^ (a - 2) := by rw [mul_comm]
  have hp2 : p = 2 * (2 : ℤ) ^ (b - 2) := by
    dsimp [p]
    calc
      (2 : ℤ) ^ (b - 1) = (2 : ℤ) ^ (b - 2) * 2 := hb2.symm
      _ = 2 * (2 : ℤ) ^ (b - 2) := by rw [mul_comm]
  by_cases hab : a ≤ b
  · by_cases heq : a = b
    · subst b
      let x : ℤ := (2 : ℤ) ^ (a - 2)
      let y : ℤ := (2 : ℤ) ^ (a - 2) - 1
      have hpl : p = L := by rw [hp2, hL2]
      have hxy : (0 ≤ x ∧ x < L) ∧ (0 ≤ y ∧ y < p) := by
        dsimp [x, y]; constructor <;> constructor <;> nlinarith
      have horder : L ≤ p := by
        rw [hpl]
      apply chart x y one atA (Or.inl ⟨rfl, rfl⟩) (by simpa using horder) hxy.1 hxy.2
      all_goals
        try simp
        dsimp only [B, C, D, E, H, N, x, y]
        simp only [hqv, hpl, hL2, hp2]
        nlinarith
    · have hba : a + 1 ≤ b := by omega
      let k : ℤ := (2 : ℤ) ^ (b - a - 1)
      have hk : 1 ≤ k := by
        have hh : 0 < k := by dsimp [k]; positivity
        omega
      have hslack : 0 ≤ 2 * k * (2 : ℤ) ^ (a - 2) - k - (2 : ℤ) ^ (a - 2) := by
        have h1 := mul_nonneg (show 0 ≤ (2 : ℤ) ^ (a - 2) by positivity)
          (show 0 ≤ k - 1 by omega)
        have h2 := mul_nonneg (show 0 ≤ k by omega)
          (show 0 ≤ (2 : ℤ) ^ (a - 2) - 1 by omega)
        nlinarith only [h1, h2]
      let x : ℤ := (2 : ℤ) ^ (a - 2) - 1
      let y : ℤ := (2 : ℤ) ^ (b - 2) + k
      have hrel : (2 : ℤ) ^ (b - 2) = 2 * (2 : ℤ) ^ (a - 2) * k := by
        dsimp [k]
        rw [show b - 2 = (a - 2) + (b - a) by omega, pow_add,
          show b - a = (b - a - 1) + 1 by omega, pow_succ]
        have hExp : (b - a - 1) + 1 - 1 = b - a - 1 := by omega
        rw [hExp]
        ring
      have hxy : (0 ≤ x ∧ x < L) ∧ (0 ≤ y ∧ y < p) := by
        dsimp [x, y]; rw [hL2, hp2, hrel]; constructor <;> constructor <;> nlinarith
      have horder : L ≤ p := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : a - 1 ≤ b - 1)
      apply chart x y one atA (Or.inl ⟨rfl, rfl⟩) (by simpa using horder) hxy.1 hxy.2
      all_goals
        try simp
        dsimp only [B, C, D, E, H, N, x, y]
        simp only [hqv, hL2, hp2, hrel]
        nlinarith
  · have hba : b < a := by omega
    by_cases heq : a = b + 1
    · let x : ℤ := (2 : ℤ) ^ (a - 2) - 1
      let y : ℤ := (2 : ℤ) ^ (b - 2)
      have hrel : (2 : ℤ) ^ (a - 2) = 2 * (2 : ℤ) ^ (b - 2) := by
        rw [show a - 2 = (b - 2) + 1 by omega, pow_succ]
        ring
      have hxy : (0 ≤ x ∧ x < L) ∧ (0 ≤ y ∧ y < p) := by
        dsimp [x, y]; rw [hL2, hp2, hrel]; constructor <;> constructor <;> nlinarith
      have horder : 2 * p ≤ L := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (b - 1) + 1 ≤ a - 1 by omega)
        simpa only [pow_succ, p, L, mul_comm] using hh
      apply chart x y atA one (Or.inr ⟨rfl, rfl⟩)
        (by simpa [honeA, hAtA] using horder) hxy.1 hxy.2
      all_goals
        try simp [honeA, hAtA]
        dsimp only [B, C, D, E, H, N, x, y]
        simp only [hqv, hL2, hp2, hrel]
        nlinarith
    · have hab2 : b + 2 ≤ a := by omega
      let k : ℤ := (2 : ℤ) ^ (a - b - 2)
      have hk : 1 ≤ k := by
        have hh : 0 < k := by dsimp [k]; positivity
        omega
      have hslack : 0 ≤ 4 * k * (2 : ℤ) ^ (b - 2) - k - 2 * (2 : ℤ) ^ (b - 2) := by
        have h1 := mul_nonneg (show 0 ≤ k by omega)
          (show 0 ≤ 2 * (2 : ℤ) ^ (b - 2) - 1 by omega)
        have h2 := mul_nonneg (show 0 ≤ 2 * (2 : ℤ) ^ (b - 2) by positivity)
          (show 0 ≤ k - 1 by omega)
        nlinarith only [h1, h2]
      let x : ℤ := (2 : ℤ) ^ (a - 2) + k
      let y : ℤ := (2 : ℤ) ^ (b - 2) - 1
      have hrel : (2 : ℤ) ^ (a - 2) = 4 * (2 : ℤ) ^ (b - 2) * k := by
        dsimp [k]
        rw [show a - 2 = (b - 2) + (a - b) by omega, pow_add,
          show a - b = (a - b - 2) + 2 by omega, pow_add]
        have hExp : 2 + (a - b - 2) - 2 = a - b - 2 := by omega
        try rw [hExp]
        norm_num
        ring
      have hxy : (0 ≤ x ∧ x < L) ∧ (0 ≤ y ∧ y < p) := by
        dsimp [x, y]; rw [hL2, hp2, hrel]; constructor <;> constructor <;> nlinarith
      have horder : 2 * p ≤ L := by
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show (b - 1) + 1 ≤ a - 1 by omega)
        simpa only [pow_succ, p, L, mul_comm] using hh
      apply chart x y atA one (Or.inr ⟨rfl, rfl⟩)
        (by simpa [honeA, hAtA] using horder) hxy.1 hxy.2
      all_goals
        try simp [honeA, hAtA]
        dsimp only [B, C, D, E, H, N, x, y]
        simp only [hqv, hL2, hp2, hrel]
        nlinarith

theorem actualSource_below_half_two_bit_uniform_cut (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      ∀ j : ℕ, j ≤ b - 2 →
        let sigma_j := sigma.map
          ((finRotate (a + b) : Equiv.Perm (Fin (a + b))) ^ (b - 2 - j))
        OriginalOrder (a + b) (2 ^ j * (2 ^ a + 1)) sigma_j ∧
        OriginalOrder (a + b + 1) (2 * (2 ^ j * (2 ^ a + 1)))
          (earWord (a + b) sigma_j cut) := by
  obtain ⟨sigma, cut, hcut, hold, hnew⟩ := boundary_joint a b ha hb
  refine ⟨sigma, cut, hcut, ?_⟩
  intro j hj
  let h : ℕ := b - 2 - j
  let s : ℕ := 2 ^ j * (2 ^ a + 1)
  have hh : 2 ^ h * s = 2 ^ (a + b - 2) + 2 ^ (b - 2) := by
    dsimp only [s]
    rw [← mul_assoc, ← pow_add,
      show h + j = b - 2 by dsimp [h]; omega,
      mul_add, mul_one, ← pow_add,
      show (b - 2) + a = a + b - 2 by omega]
  have hlt : 2 ^ h * s < 2 ^ ((a + b) - 1) := by
    rw [hh]
    have hsmall : (2 : ℕ) ^ (b - 2) < 2 ^ (a + b - 2) :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) (by omega)
    have hstep : (2 : ℕ) ^ (a + b - 1) = 2 ^ (a + b - 2) * 2 := by
      rw [show a + b - 1 = (a + b - 2) + 1 by omega, pow_succ]
    rw [hstep]
    omega
  have hspos : 1 ≤ s := by
    have hs : 0 < s := by dsimp only [s]; positivity
    omega
  have hd : 2 ≤ a + b := by omega
  have holdScaled : OriginalOrder (a + b) (2 ^ h * s) sigma := by
    rw [hh]
    exact hold
  have hnewScaled : OriginalOrder (a + b + 1) (2 * (2 ^ h * s))
      (earWord (a + b) sigma cut) := by
    rw [hh]
    exact hnew
  obtain ⟨holdT, hnewT, _⟩ :=
    native_dyadic_joint_transport (a + b) s h hd hspos hlt sigma cut hcut
      holdScaled hnewScaled
  dsimp only at holdT hnewT ⊢
  simpa only [h, s] using And.intro holdT hnewT

end D5.S3.Combinatorics.Circle.BelowHalfBoundary
