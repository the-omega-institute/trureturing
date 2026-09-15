/- GID: D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The seventh compositional iterate has coefficient period 7,1,3,5 modulo eight. -/

import D5.S1.Recurrence.Residue.IterateProductFourFiveThirdModEight
import D5.S1.Recurrence.Residue.IterateProductFourFiveFourthModEight

open PowerSeries
open D5.S1.Recurrence.Invariants
open D5.S1.Recurrence.Residue
open CompositionalIterateCongruence (iterate)
open IterateProductFourFiveEighthModEight (generatingSeries)
open private iterate_constant map_iterates from
  D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix
open private iterate_normal iterate_add iterate_top Agree from
  D5.S1.Recurrence.Parity.DiagonalIterateEven

namespace D5.S1.Recurrence.Residue.IterateProductFourFiveSeventhModEight

theorem result (n : Nat) (hn : 1 < n) :
  (8 : Int) ∣ PowerSeries.coeff n
    (CompositionalIterateCongruence.iterate
      IterateProductFourFiveEighthModEight.generatingSeries 7) -
    (if (n - 2) % 4 = 0 then (7 : Int)
     else if (n - 2) % 4 = 1 then 1
     else if (n - 2) % 4 = 2 then 3 else 5) := by
  let F : PowerSeries (ZMod 8) := generatingSeries.map (Int.castRingHom (ZMod 8))
  let U : PowerSeries (ZMod 8) := iterate F 3
  have source_zero : constantCoeff generatingSeries = 0 := by
    let H : PowerSeries ℤ → PowerSeries ℤ := fun f => X + iterate f 4 * iterate f 5
    have hz : constantCoeff (H 0) = 0 := by
      simp only [H, map_add, constantCoeff_X, map_mul,
        iterate_constant _ (map_zero _) _, mul_zero, zero_add]
    change coeff 0 (H^[1] 0) = 0
    simpa only [Function.iterate_one, coeff_zero_eq_constantCoeff] using hz
  have source_one : coeff 1 generatingSeries = 1 := by
    let H : PowerSeries ℤ → PowerSeries ℤ := fun f => X + iterate f 4 * iterate f 5
    have hz : constantCoeff (H 0) = 0 := by
      simp only [H, map_add, constantCoeff_X, map_mul,
        iterate_constant _ (map_zero _) _, mul_zero, zero_add]
    rw [generatingSeries, coeff_mk]
    change coeff 1 (H^[2] 0) = 1
    rw [Function.iterate_succ_apply' H 1 0, Function.iterate_one]
    simp only [H, map_add, coeff_one_X, coeff_one_mul,
      iterate_constant _ hz _, mul_zero, add_zero]
  have F_zero : constantCoeff F = 0 := by
    dsimp only [F]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      source_zero, map_zero]
  have F_one : coeff 1 F = 1 := by
    dsimp only [F]
    rw [coeff_map, source_one, map_one]
  have U_zero : constantCoeff U = 0 := (iterate_normal F_zero F_one 3).1
  have U_one : coeff 1 U = 1 := (iterate_normal F_zero F_one 3).2
  have third (m : ℕ) (hm : 1 < m) : coeff m U =
      if (m - 2) % 4 = 0 then (3 : ZMod 8)
      else if (m - 2) % 4 = 1 then 1
      else if (m - 2) % 4 = 2 then 7 else 5 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (IterateProductFourFiveThirdModEight.result m hm)
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_ofNat, Int.cast_one,
      sub_eq_zero] at h
    simpa only [U, F, ← map_iterates (Int.castRingHom (ZMod 8)) source_zero,
      coeff_map, Int.coe_castRingHom] using h
  have quadratic (j : ℕ) : coeff 2 (iterate F j) = (j : ZMod 8) * coeff 2 F := by
    have hX (k : ℕ) : iterate (X : PowerSeries (ZMod 8)) k = X := by
      induction k with
      | zero => rfl
      | succ k ih => simpa only [iterate, X_subst] using ih
    have hA : Agree 2 F X := by
      intro k hk
      interval_cases k
      · simpa only [coeff_zero_eq_constantCoeff, constantCoeff_X] using F_zero
      · simpa only [coeff_one_X] using F_one
    have h := iterate_top (by decide : 1 < 2) F_zero constantCoeff_X
      F_one coeff_one_X hA j
    simpa only [hX, coeff_X, show (2 : ℕ) ≠ 1 by decide, if_false, sub_zero] using h
  have F_two : coeff 2 F = 1 := by
    have h : (3 : ZMod 8) * coeff 2 F = 3 := by
      have hq := quadratic 3
      norm_num only [Nat.cast_ofNat] at hq
      rw [← hq]
      simpa only [U, Nat.sub_self, Nat.zero_mod, if_true] using third 2 (by decide)
    calc
      coeff 2 F = 3 * (3 * coeff 2 F) := by
        rw [← mul_assoc, show (3 : ZMod 8) * 3 = 1 by decide, one_mul]
      _ = 1 := by rw [h]; decide
  have fourth : iterate F 4 = X + C (4 : ZMod 8) * X ^ 2 := by
    ext m
    by_cases h0 : m = 0
    · subst m
      simp only [coeff_zero_eq_constantCoeff, (iterate_normal F_zero F_one 4).1,
        map_add, constantCoeff_X, map_mul, map_pow, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
    by_cases h1 : m = 1
    · subst m
      simp only [(iterate_normal F_zero F_one 4).2, map_add, coeff_one_X,
        coeff_C_mul, coeff_X_pow, show (1 : ℕ) ≠ 2 by decide, if_false, mul_zero, add_zero]
    by_cases h2 : m = 2
    · subst m
      rw [quadratic, F_two]
      norm_num [coeff_X_pow, coeff_X]
    have hm : 2 < m := by omega
    have ht : coeff m (iterate F 4) = 0 := by
      dsimp only [F]
      rw [← map_iterates (Int.castRingHom (ZMod 8)) source_zero, coeff_map]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (IterateProductFourFiveFourthModEight.result m hm)
    simp only [ht, map_add, coeff_X, if_neg h1, coeff_C_mul, coeff_X_pow,
      if_neg h2, mul_zero, add_zero]
  have seventh : iterate F 7 = U + C (4 : ZMod 8) * U ^ 2 := by
    have hs : HasSubst U := .of_constantCoeff_zero U_zero
    rw [show 7 = 4 + 3 by decide, iterate_add F_zero F_one, fourth]
    change (X + C (4 : ZMod 8) * X ^ 2).subst U = _
    rw [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_C]
    rfl
  have odd_weight (m : ℕ) (hm : 0 < m) : (4 : ZMod 8) * coeff m U = 4 := by
    by_cases h1 : m = 1
    · subst m
      rw [U_one, mul_one]
    rw [third m (by omega)]
    split_ifs <;> decide
  have convolution : (4 : ZMod 8) * coeff n (U ^ 2) = 4 * (n - 1 : ℕ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
    rw [Nat.add_comm 2 k, pow_two, coeff_mul, Finset.mul_sum]
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    simp only [coeff_zero_eq_constantCoeff, U_zero, zero_mul, mul_zero, zero_add]
    calc
      ∑ p ∈ Finset.antidiagonal k,
          (4 : ZMod 8) * (coeff (p.1 + 1) U * coeff (p.2 + 1) U) =
          ∑ _p ∈ Finset.antidiagonal k, (4 : ZMod 8) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← mul_assoc, odd_weight _ (by omega), odd_weight _ (by omega)]
      _ = 4 * (k + 2 - 1 : ℕ) := by
        simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        rw [show k + 2 - 1 = k + 1 by omega]
        ring
  have phase : (4 : ZMod 8) * (n - 1 : ℕ) =
      if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 2 then 4 else 0 := by
    have he : n - 1 = 4 * ((n - 2) / 4) + (n - 2) % 4 + 1 := by omega
    rw [he]
    push_cast
    simp only [mul_add, ← mul_assoc, show (4 : ZMod 8) * 4 = 0 by decide,
      zero_mul, zero_add, mul_one]
    have hr := Nat.mod_lt (n - 2) (by decide : 0 < 4)
    interval_cases h : (n - 2) % 4 <;> norm_num [h] <;> decide
  have hc : coeff n (iterate F 7) =
      if (n - 2) % 4 = 0 then (7 : ZMod 8)
      else if (n - 2) % 4 = 1 then 1
      else if (n - 2) % 4 = 2 then 3 else 5 := by
    rw [seventh, map_add, coeff_C_mul, third n hn, convolution, phase]
    have hr := Nat.mod_lt (n - 2) (by decide : 0 < 4)
    interval_cases h : (n - 2) % 4 <;> norm_num [h]
    decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub, Int.cast_ite, Int.cast_ofNat, Int.cast_one]
  apply sub_eq_zero.mpr
  simpa only [F, ← map_iterates (Int.castRingHom (ZMod 8)) source_zero,
    coeff_map, Int.coe_castRingHom] using hc

end D5.S1.Recurrence.Residue.IterateProductFourFiveSeventhModEight
