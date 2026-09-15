/- GID: D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalModThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative]
   utility: none
   digest: A ternary sparse square describes the nonzero coefficients of A397356 modulo three. -/

import D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalParity
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalModThree

open PowerSeries
open D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalParity

/-- Cube extraction and the formal derivative control the square-exponent diagonal. -/
theorem inverse_cube_diagonal (S Q : PowerSeries (ZMod 3))
    (hS : S = 1 + X + X * S ^ 3) (hSQ : S * Q = 1)
    (n : ℕ) (hn : 1 < n) :
    coeff n ((Q ^ 2) ^ (n ^ 2)) = coeff n ((Q ^ 2) ^ (n ^ 2 - 1)) := by
  have hthree : (3 : PowerSeries (ZMod 3)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 3)) (show (3 : ZMod 3) = 0 by decide)
  have hcube (F : PowerSeries (ZMod 3)) (i : ℕ) :
      coeff i (F ^ 3) = if i % 3 = 0 then coeff (i / 3) F else 0 := by
    have he := MvPowerSeries.map_frobenius_expand (f := F) 3 (by decide)
    rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at he
    rw [← he]
    exact (PowerSeries.coeff_expand 3 (by decide) F).trans (by
      simp only [Nat.dvd_iff_mod_eq_zero])
  have hshift (F : PowerSeries (ZMod 3)) (m d : ℕ) (hd : d = 1 ∨ d = 2) :
      coeff (3 * m) (X ^ d * F ^ 3) = 0 := by
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [hcube, if_neg (by rcases hd with rfl | rfl <;> omega)]
    · rfl
  have hSsq : S ^ 2 = 1 - X * (1 + S ^ 3) + X ^ 2 * (1 + S ^ 3) ^ 2 := by
    linear_combination (S + 1 + X * (1 + S ^ 3)) * hS + X * (1 + S ^ 3) * hthree
  have hcart (F : PowerSeries (ZMod 3)) (m : ℕ) :
      coeff (3 * m) (Q * F ^ 3) = coeff m (Q * F) := by
    have he : Q * F ^ 3 = (Q * F) ^ 3 -
        X * ((1 + S) * (Q * F)) ^ 3 +
        X ^ 2 * ((1 + S) ^ 2 * (Q * F)) ^ 3 := by
      calc
        Q * F ^ 3 = S ^ 2 * (Q * F) ^ 3 := by
          calc
            _ = Q * F ^ 3 * (S * Q) ^ 2 := by rw [hSQ]; ring
            _ = _ := by ring
        _ = _ := by
          rw [hSsq]
          simp only [mul_pow]
          have hadd : (1 + S) ^ 3 = 1 + S ^ 3 := by
            linear_combination (S + S ^ 2) * hthree
          rw [show ((1 + S) ^ 2) ^ 3 = ((1 + S) ^ 3) ^ 2 by ring, hadd]
          ring
    rw [he, map_add, map_sub, hcube, hshift _ m 2 (Or.inr rfl)]
    have hz := hshift ((1 + S) * (Q * F)) m 1 (Or.inl rfl)
    simp only [pow_one] at hz
    simp [hz]
  have hQ : Q ^ 2 = X + (1 + X) * Q ^ 3 := by
    calc
      Q ^ 2 = S * Q ^ 3 := by
        calc
          _ = (S * Q) * Q ^ 2 := by rw [hSQ, one_mul]
          _ = _ := by ring
      _ = (1 + X) * Q ^ 3 + X * (S * Q) ^ 3 := by
        conv_lhs => rw [hS]
        ring
      _ = _ := by rw [hSQ]; ring
  have hder : X * derivative (ZMod 3) Q = Q * (Q - 1) := by
    have hds := congrArg (derivative (ZMod 3)) hS
    simp only [map_add, derivative_one, derivative_X, Derivation.leibniz,
      derivative_pow, smul_eq_mul, Nat.cast_ofNat, hthree, zero_mul, mul_zero,
      zero_add, mul_one] at hds
    have hdq := congrArg (derivative (ZMod 3)) hSQ
    simp only [Derivation.leibniz, derivative_one, smul_eq_mul] at hdq
    linear_combination X * Q * hdq - X * Q ^ 2 * hds + Q ^ 2 * hS -
      (Q + X * derivative (ZMod 3) Q) * hSQ
  have hvanish : ∀ m : ℕ, 0 < m → ∀ t : ℕ, t % 3 = 1 →
      coeff m (Q ^ (m * t) * (1 + Q)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm t ht
      by_cases hmod : m % 3 = 0
      · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
        have he : Q ^ (3 * k * t) * (1 + Q) =
            (Q ^ (k * t)) ^ 3 + Q * (Q ^ (k * t)) ^ 3 := by
          rw [← pow_mul]
          have : k * t * 3 = 3 * k * t := by ring
          rw [this]; ring
        rw [he, map_add, hcube, hcart]
        simpa [mul_add, mul_comm] using ih k (by omega) (by omega) t ht
      · have hm0 : (m : ZMod 3) ≠ 0 := by
          exact fun h => hmod (Nat.dvd_iff_mod_eq_zero.mp
            ((ZMod.natCast_eq_zero_iff m 3).mp h))
        have ht1 : (t : ZMod 3) = 1 := by
          rw [← ZMod.natCast_mod t 3, ht]; rfl
        have hmt : 0 < m * t := Nat.mul_pos hm (by omega)
        have he : X * derivative (ZMod 3) (Q ^ (m * t)) =
            C (m : ZMod 3) * (Q ^ (m * t + 1) - Q ^ (m * t)) := by
          rw [derivative_pow]
          have hc : ((m * t : ℕ) : PowerSeries (ZMod 3)) = C (m : ZMod 3) := by
            rw [← map_natCast (PowerSeries.C (R := ZMod 3)), Nat.cast_mul, ht1, mul_one]
          rw [hc]
          calc
            _ = C (m : ZMod 3) * Q ^ (m * t - 1) *
                (X * derivative (ZMod 3) Q) := by ring
            _ = _ := by
              rw [hder]
              have hp : Q ^ (m * t - 1) * Q = Q ^ (m * t) := by
                rw [← pow_succ, Nat.sub_add_cancel hmt]
              rw [pow_succ]
              linear_combination C (m : ZMod 3) * (Q - 1) * hp
        have hc := congrArg (coeff m) he
        have hleft : coeff m (X * derivative (ZMod 3) (Q ^ (m * t))) =
            coeff m (Q ^ (m * t)) * (m : ZMod 3) := by
          conv_lhs => arg 1; rw [show m = (m - 1) + 1 by omega]
          rw [coeff_succ_X_mul, coeff_derivative, show m - 1 + 1 = m by omega]
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one] using
            congrArg (fun k : ℕ => (k : ZMod 3)) (show m - 1 + 1 = m by omega)
        rw [hleft, coeff_C_mul, map_sub] at hc
        have hz : (3 : ZMod 3) = 0 := by decide
        apply (mul_eq_zero.mp (show (m : ZMod 3) *
            coeff m (Q ^ (m * t) * (1 + Q)) = 0 from by
          rw [mul_add, mul_one, ← pow_succ, map_add]
          linear_combination -hc + ((m : ZMod 3) * coeff m (Q ^ (m * t))) * hz)).resolve_left hm0
  have hn2 : 2 ≤ n ^ 2 := by nlinarith
  rcases Nat.mod_lt n (by decide : 0 < 3) |> (by omega : n % 3 < 3 →
    n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    have hm : 0 < m := by omega
    have hp : 2 * ((3 * m) ^ 2 - 1) = 3 * (6 * m ^ 2 - 1) + 1 := by
      have : (3 * m) ^ 2 = 9 * m ^ 2 := by ring
      have : 1 ≤ m ^ 2 := by nlinarith
      omega
    rw [← pow_mul, ← pow_mul, show 2 * (3 * m) ^ 2 = 6 * m ^ 2 * 3 by ring,
      pow_mul, hcube, hp, pow_succ' Q (3 * (6 * m ^ 2 - 1)), show 3 * (6 * m ^ 2 - 1) =
        (6 * m ^ 2 - 1) * 3 by ring, pow_mul Q (6 * m ^ 2 - 1) 3, hcart]
    simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left, Nat.ofNat_pos, if_true]
    rw [← pow_succ' Q (6 * m ^ 2 - 1), Nat.sub_add_cancel (by nlinarith : 1 ≤ 6 * m ^ 2)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
    have hm : 0 < m := by omega
    have hp : 2 * ((3 * m + 1) ^ 2 - 1) = (m * (6 * m + 4)) * 3 := by
      have : (3 * m + 1) ^ 2 = 9 * m ^ 2 + 6 * m + 1 := by ring
      have : m * (6 * m + 4) = 6 * m ^ 2 + 4 * m := by ring
      omega
    apply sub_eq_zero.mp
    rw [← map_sub, ← pow_mul, ← pow_mul]
    have he : Q ^ (2 * (3 * m + 1) ^ 2) - Q ^ (2 * ((3 * m + 1) ^ 2 - 1)) =
        (Q ^ (m * (6 * m + 4))) ^ 3 * (Q ^ 2 - 1) := by
      rw [← pow_mul, ← hp, mul_sub, mul_one, ← pow_add]
      congr 2
    rw [he, hQ]
    have he' (F : PowerSeries (ZMod 3)) :
        F ^ 3 * (X + (1 + X) * Q ^ 3 - 1) =
        (F * Q) ^ 3 - F ^ 3 + X * (F ^ 3 + (F * Q) ^ 3) := by
      simp only [mul_pow]; ring
    rw [he', map_add, map_sub, coeff_succ_X_mul, map_add, hcube, hcube, hcube, hcube]
    simp only [show (3 * m + 1) % 3 ≠ 0 by omega, if_false, sub_self, zero_add,
      Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left, Nat.ofNat_pos]
    simpa only [mul_add, mul_one, map_add] using hvanish m hm (6 * m + 4) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    have hp : 2 * ((3 * m + 2) ^ 2 - 1) = (6 * m ^ 2 + 8 * m + 2) * 3 := by
      have : (3 * m + 2) ^ 2 = 9 * m ^ 2 + 12 * m + 4 := by ring
      omega
    rw [← pow_mul, ← pow_mul, show 2 * (3 * m + 2) ^ 2 =
      (6 * m ^ 2 + 8 * m + 2) * 3 + 2 by ring, pow_add, hQ, hp, pow_mul]
    have he (F : PowerSeries (ZMod 3)) :
        F ^ 3 * (X + (1 + X) * Q ^ 3) =
        (F * Q) ^ 3 + X * (F ^ 3 + (F * Q) ^ 3) := by
      simp only [mul_pow]; ring
    rw [he, map_add, show 3 * m + 2 = (3 * m + 1) + 1 by omega,
      coeff_succ_X_mul, map_add, hcube, hcube, hcube, hcube]
    simp [show (3 * m + 2) % 3 ≠ 0 by omega]

open private equation_unique from
  D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalParity

/-- Hanna's unrestricted sum-of-two-ternary-powers criterion for OEIS A397356. -/
theorem a397356_mod_three (n : ℕ) :
    ¬ ((3 : ℤ) ∣ a n) ↔ ∃ u v : ℕ, 2 * (n + 1) = 3 ^ u + 3 ^ v := by
  classical
  let S : PowerSeries (ZMod 3) := mk fun i =>
    if i = 0 then 1 else if ∃ k : ℕ, 2 * i + 1 = 3 ^ k then -1 else 0
  have hsupp (i : ℕ) : coeff i S ≠ 0 ↔ ∃ k : ℕ, 2 * i + 1 = 3 ^ k := by
    by_cases hi : i = 0
    · subst i
      simp [S, show ∃ k : ℕ, 1 = 3 ^ k from ⟨0, rfl⟩]
    · simp [S, hi]
  have hs0 : coeff 0 S = 1 := by simp [S]
  have hs1 : coeff 1 S = -1 := by
    simp [S, show ∃ k : ℕ, 3 = 3 ^ k from ⟨1, rfl⟩]
  have hstep (i : ℕ) : (∃ k : ℕ, 2 * (i + 1) + 1 = 3 ^ k) ↔
      i % 3 = 0 ∧ ∃ k : ℕ, 2 * (i / 3) + 1 = 3 ^ k := by
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp only [pow_zero] at hk; omega
      | succ k =>
        rw [pow_succ] at hk
        refine ⟨by omega, k, ?_⟩
        omega
    · rintro ⟨hi, k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [pow_succ]; omega
  have hS : S = 1 + X + X * S ^ 3 := by
    have hcube (i : ℕ) : coeff i (S ^ 3) =
        if i % 3 = 0 then coeff (i / 3) S else 0 := by
      have he := MvPowerSeries.map_frobenius_expand (f := S) 3 (by decide)
      rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at he
      rw [← he]
      exact (PowerSeries.coeff_expand 3 (by decide) S).trans (by
        simp only [Nat.dvd_iff_mod_eq_zero])
    ext i
    cases i with
    | zero => simp [S]
    | succ i =>
      rw [map_add, map_add, coeff_succ_X_mul, hcube]
      by_cases hi : i = 0
      · subst i
        simp only [coeff_one, one_ne_zero, if_false, coeff_one_X,
          zero_add, Nat.zero_mod, if_true, Nat.zero_div, hs0, hs1]
        decide
      · by_cases hmod : i % 3 = 0
        · have hdiv : i / 3 ≠ 0 := by omega
          simp [S, coeff_X, hi, hdiv, hmod, hstep]
        · simp [S, coeff_X, hi, hmod, hstep]
  let Q : PowerSeries (ZMod 3) := PowerSeries.invOfUnit S 1
  have hSQ : S * Q = 1 := PowerSeries.mul_invOfUnit S 1 (by
    simpa [coeff_zero_eq_constantCoeff] using hs0)
  have hq0 : coeff 0 Q = 1 := by simp [Q, coeff_zero_eq_constantCoeff]
  have hq1 : coeff 1 Q = 1 := by
    have h := congrArg (coeff 1) hSQ
    simp only [coeff_one_mul, ← coeff_zero_eq_constantCoeff, hs0, hs1, hq0,
      coeff_one, one_ne_zero, if_false, mul_one] at h
    linear_combination h
  have hR : reciprocalSeries.map (Int.castRingHom (ZMod 3)) = Q ^ 2 := by
    apply equation_unique
    · simp [coeff_map, reciprocalSeries, r]
    · rw [coeff_zero_eq_constantCoeff, map_pow, ← coeff_zero_eq_constantCoeff, hq0, one_pow]
    · simp [coeff_map, reciprocalSeries, r]
    · rw [pow_two, coeff_one_mul, ← coeff_zero_eq_constantCoeff, hq0, hq1]
      decide
    · intro i hi
      simpa only [← map_pow, coeff_map, Int.coe_castRingHom] using
        congrArg (Int.castRingHom (ZMod 3)) (generating_equation.2.2.2 i hi)
    · exact inverse_cube_diagonal S Q hS hSQ
  have hA : generatingSeries.map (Int.castRingHom (ZMod 3)) = S ^ 2 := by
    have hinv := congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) generating_equation.1
    simp only [map_mul, map_one, hR] at hinv
    have hQS : Q ^ 2 * S ^ 2 = 1 := by
      rw [← mul_pow, mul_comm Q S, hSQ, one_pow]
    calc
      _ = (Q ^ 2 * S ^ 2) * generatingSeries.map (Int.castRingHom (ZMod 3)) := by
        rw [hQS, one_mul]
      _ = S ^ 2 * (Q ^ 2 * generatingSeries.map (Int.castRingHom (ZMod 3))) := by ring
      _ = _ := by rw [hinv, mul_one]
  have hordered (u v w z : ℕ) (huv : u ≤ v) (hwz : w ≤ z)
      (he : (3 : ℕ) ^ u + 3 ^ v = 3 ^ w + 3 ^ z) : u = w ∧ v = z := by
    have hm : v = z := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hvz := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hlt
        have huv' := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) huv
        have hp : 0 < (3 : ℕ) ^ v := by positivity
        rw [pow_succ] at hvz
        have hlt : (3 : ℕ) ^ u + 3 ^ v < 3 ^ z := calc
          _ ≤ 3 ^ v + 3 ^ v := Nat.add_le_add_right huv' _
          _ < 3 ^ v * 3 := by
            rw [← mul_two]
            exact Nat.mul_lt_mul_of_pos_left (by decide : 2 < 3) hp
          _ ≤ _ := hvz
        rw [he] at hlt
        exact (Nat.not_lt.mpr (Nat.le_add_left _ _)) hlt
      · have hzv := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hgt
        have hwz' := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hwz
        have hp : 0 < (3 : ℕ) ^ z := by positivity
        rw [pow_succ] at hzv
        have hlt : (3 : ℕ) ^ w + 3 ^ z < 3 ^ v := calc
          _ ≤ 3 ^ z + 3 ^ z := Nat.add_le_add_right hwz' _
          _ < 3 ^ z * 3 := by
            rw [← mul_two]
            exact Nat.mul_lt_mul_of_pos_left (by decide : 2 < 3) hp
          _ ≤ _ := hzv
        rw [← he] at hlt
        exact (Nat.not_lt.mpr (Nat.le_add_left _ _)) hlt
    subst z
    have heq : (3 : ℕ) ^ u = 3 ^ w := Nat.add_right_cancel he
    exact ⟨Nat.pow_right_injective (by decide : 2 ≤ (3 : ℕ)) heq, rfl⟩
  have huniq (u v w z : ℕ) (he : 3 ^ u + 3 ^ v = 3 ^ w + 3 ^ z) :
      (u = w ∧ v = z) ∨ (u = z ∧ v = w) := by
    rcases le_total u v with h | h <;> rcases le_total w z with h' | h'
    · exact Or.inl (hordered u v w z h h' he)
    · exact Or.inr (hordered u v z w h h' (by omega))
    · have := hordered v u w z h h' (by omega); omega
    · have := hordered v u z w h h' (by omega); omega
  have hdiv : (a n : ZMod 3) = 0 ↔ (3 : ℤ) ∣ a n := by
    convert ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 3 using 1
    norm_num
  rw [← hdiv]
  have hcoeff : (a n : ZMod 3) = coeff n (S ^ 2) := by
    simpa only [a, coeff_map, Int.coe_castRingHom] using congrArg (coeff n) hA
  rw [hcoeff]
  constructor
  · intro hc
    by_contra hnone
    apply hc
    rw [pow_two, coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases h1 : coeff p.1 S = 0
    · simp [h1]
    by_cases h2 : coeff p.2 S = 0
    · simp [h2]
    obtain ⟨u, hu⟩ := (hsupp p.1).mp h1
    obtain ⟨v, hv⟩ := (hsupp p.2).mp h2
    have := Finset.mem_antidiagonal.mp hp
    exact False.elim (hnone ⟨u, v, by omega⟩)
  · rintro ⟨u, v, huv⟩
    obtain ⟨i, hi⟩ := ((show Odd (3 : ℕ) by decide).pow : Odd ((3 : ℕ) ^ u))
    obtain ⟨j, hj⟩ := ((show Odd (3 : ℕ) by decide).pow : Odd ((3 : ℕ) ^ v))
    have hij : i + j = n := by omega
    have hsi : coeff i S ≠ 0 := (hsupp i).mpr ⟨u, by omega⟩
    have hsj : coeff j S ≠ 0 := (hsupp j).mpr ⟨v, by omega⟩
    have hsub : {(i, j), (j, i)} ⊆ Finset.antidiagonal n := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> exact Finset.mem_antidiagonal.mpr (by omega)
    have he : coeff n (S ^ 2) =
        ∑ p ∈ ({(i, j), (j, i)} : Finset (ℕ × ℕ)), coeff p.1 S * coeff p.2 S := by
      rw [pow_two, coeff_mul]
      symm
      apply Finset.sum_subset hsub
      intro p hp hnot
      by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
      obtain ⟨w, hw⟩ := (hsupp p.1).mp h1
      obtain ⟨z, hz⟩ := (hsupp p.2).mp h2
      have hp' := Finset.mem_antidiagonal.mp hp
      have hsum : 3 ^ u + 3 ^ v = 3 ^ w + 3 ^ z := by omega
      rcases huniq u v w z hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : p = (i, j) := Prod.ext (by omega) (by omega)
        exact hnot (by simp [this])
      · have : p = (j, i) := Prod.ext (by omega) (by omega)
        exact hnot (by simp [this])
    rw [he]
    by_cases heq : i = j
    · subst j
      simpa using mul_ne_zero hsi hsi
    · have hpair : (i, j) ≠ (j, i) := by
        intro h
        exact heq (congrArg Prod.fst h)
      simp only [Finset.sum_pair hpair]
      change coeff i S * coeff j S + coeff j S * coeff i S ≠ 0
      have he' : coeff i S * coeff j S + coeff j S * coeff i S =
          (2 : ZMod 3) * (coeff i S * coeff j S) := by ring
      rw [he']
      exact mul_ne_zero (by decide) (mul_ne_zero hsi hsj)


end D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalModThree
