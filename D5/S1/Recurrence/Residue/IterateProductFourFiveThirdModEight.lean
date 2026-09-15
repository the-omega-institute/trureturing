/- GID: D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The third compositional iterate has coefficient period 3,1,7,5 modulo eight. -/

import D5.S1.Recurrence.Residue.IterateProductFourFiveFifthModEight
import D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight
import Mathlib.Tactic.LinearCombination

open PowerSeries
open D5.S1.Recurrence.Invariants
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate)
open D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight (generatingSeries)

namespace D5.S1.Recurrence.Residue.IterateProductFourFiveThirdModEight

/-- The third iterate of the ordinary integer generating series has residues
    3, 1, 7, 5 modulo eight, starting at degree two. -/
theorem result (n : Nat) (hn : 1 < n) :
  (8 : Int) ∣ PowerSeries.coeff n
    (CompositionalIterateCongruence.iterate
      IterateProductFourFiveEighthModEight.generatingSeries 3) -
    (if (n - 2) % 4 = 0 then (3 : Int)
     else if (n - 2) % 4 = 1 then 1
     else if (n - 2) % 4 = 2 then 7 else 5) := by
  let F : PowerSeries (ZMod 8) :=
    generatingSeries.map (Int.castRingHom (ZMod 8))
  let Q : PowerSeries (ZMod 8) :=
    PowerSeries.mk (fun k : ℕ => if k % 4 = 0 then (1 : ZMod 8) else 0)
  let K : PowerSeries (ZMod 8) :=
    X + X ^ 2 * (3 + X + 7 * X ^ 2 + 5 * X ^ 3) * Q

  have iterate_constant {R : Type} [CommRing R] {f : PowerSeries R} (hf : constantCoeff f = 0) (j : ℕ) :
      constantCoeff (iterate f j) = 0 := by
    induction j with
    | zero => simp [iterate]
    | succ j ih => exact constantCoeff_subst_eq_zero hf _ ih

  have source_zero : constantCoeff generatingSeries = 0 := by
    let H : PowerSeries ℤ → PowerSeries ℤ := fun f => X + iterate f 4 * iterate f 5
    have hz : constantCoeff (H 0) = 0 := by
      simp only [H, map_add, constantCoeff_X, map_mul,
        iterate_constant (map_zero _) _, mul_zero, zero_add]
    change coeff 0 (H^[1] 0) = 0
    simpa only [Function.iterate_one, coeff_zero_eq_constantCoeff] using hz

  have source_one : coeff 1 generatingSeries = 1 := by
    let H : PowerSeries ℤ → PowerSeries ℤ := fun f => X + iterate f 4 * iterate f 5
    have hz : constantCoeff (H 0) = 0 := by
      simp only [H, map_add, constantCoeff_X, map_mul,
        iterate_constant (map_zero _) _, mul_zero, zero_add]
    rw [generatingSeries, coeff_mk]
    change coeff 1 (H^[2] 0) = 1
    rw [Function.iterate_succ_apply' H 1 0, Function.iterate_one]
    simp only [H, map_add, coeff_one_X, coeff_one_mul,
      iterate_constant hz _, mul_zero, add_zero]

  have subst_coeff_one {R : Type} [CommRing R] (f u : PowerSeries R) (hu : constantCoeff u = 0) :
      coeff 1 (f.subst u) = coeff 1 f * coeff 1 u := by
    rw [coeff_subst' (.of_constantCoeff_zero hu)]
    simp only [smul_eq_mul]
    rw [finsum_eq_single (a := 1)]
    · simp
    · intro k hk
      rcases k with _ | _ | k
      · simp
      · exact (hk rfl).elim
      · have hp : coeff 1 (u ^ (k + 2)) = 0 :=
          X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hu) (k + 2)) 1 (by omega)
        rw [hp, mul_zero]

  have iterate_one {R : Type} [CommRing R] {f : PowerSeries R} (hf : constantCoeff f = 0)
      (h1 : coeff 1 f = 1) (j : ℕ) : coeff 1 (iterate f j) = 1 := by
    induction j with
    | zero => simp [iterate]
    | succ j ih => rw [iterate, subst_coeff_one _ _ hf, ih, h1, mul_one]

  have map_iterates {R : Type} [CommRing R] {S : Type} [CommRing S] (hom : R →+* S)
      {f : PowerSeries R} (hf : constantCoeff f = 0) (j : ℕ) :
      (iterate f j).map hom = iterate (f.map hom) j := by
    induction j with
    | zero => simp [iterate]
    | succ j ih =>
      change ((iterate f j).subst f).map hom = (iterate (f.map hom) j).subst (f.map hom)
      rw [map_subst (.of_constantCoeff_zero hf), ih]
      rfl

  have iterate_add {R : Type} [CommRing R] {f : PowerSeries R} (hf : constantCoeff f = 0) (j k : ℕ) :
      iterate f (j + k) = (iterate f j).subst (iterate f k) := by
    induction k with
    | zero => simp [iterate]
    | succ k ih =>
      change (iterate f (j + k)).subst f = (iterate f j).subst ((iterate f k).subst f)
      rw [ih]
      exact subst_comp_subst_apply (.of_constantCoeff_zero (iterate_constant hf k))
        (.of_constantCoeff_zero hf) (iterate f j)

  have F_zero : constantCoeff F = 0 := by
    dsimp only [F]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      source_zero, map_zero]

  have F_one : coeff 1 F = 1 := by
    dsimp only [F]
    rw [coeff_map, source_one, map_one]

  have Q_geometric : Q * ((1 : PowerSeries (ZMod 8)) -
      (X : PowerSeries (ZMod 8)) ^ 4) = 1 := by
    ext n
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
    simp only [Q, coeff_mk, coeff_one]
    by_cases hn : n < 4
    · interval_cases n <;> norm_num
    · have h4 : 4 ≤ n := by omega
      have hm : (n - 4) % 4 = n % 4 := by omega
      rw [if_pos h4, hm, sub_self, if_neg (by omega : n ≠ 0)]

  have mapped_tail (n : ℕ) (hn : 1 < n) :
      coeff n ((iterate generatingSeries 5).map (Int.castRingHom (ZMod 8))) =
        if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then 5 else 1 := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub
      (coeff n (iterate generatingSeries 5))
      (if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then (5 : ℤ) else 1) 8).mpr
        (dvd_sub_comm.mp
          (D5.S1.Recurrence.Residue.IterateProductFourFiveFifthModEight.result n hn))
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ite,
      Int.cast_ofNat, Int.cast_one] using h

  have reconstruction (J : PowerSeries (ZMod 8))
      (hzero : coeff 0 J = 0)
      (hone : coeff 1 J = 1)
      (hperiod : ∀ n : ℕ, 1 < n → coeff n J =
        if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then 5 else 1) :
      J = X + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) * Q := by
    have periodic (m : ℕ) :
        coeff m ((5 + X + X ^ 2 + 5 * X ^ 3) * Q) =
          if m % 4 = 0 ∨ m % 4 = 3 then 5 else 1 := by
      have hs : (5 + X + X ^ 2 + 5 * X ^ 3) * Q =
          C (5 : ZMod 8) * Q + X ^ 1 * Q + X ^ 2 * Q +
            C (5 : ZMod 8) * (X ^ 3 * Q) := by
        simp only [map_ofNat]
        ring
      rw [hs]
      simp only [map_add, coeff_C_mul, coeff_X_pow_mul', Q, coeff_mk]
      by_cases hm : m < 3
      · interval_cases m <;> norm_num
      · have hr := Nat.mod_lt m (by omega : 0 < 4)
        interval_cases h : m % 4 <;>
          simp (disch := omega) only [if_pos, if_neg, mul_one, mul_zero, zero_add, add_zero] <;>
            norm_num
    ext n
    by_cases hn : 1 < n
    · rw [hperiod n hn, map_add, coeff_X, if_neg (by omega : n ≠ 1), zero_add,
        mul_assoc, coeff_X_pow_mul', if_pos (by omega : 2 ≤ n)]
      exact (periodic (n - 2)).symm
    · interval_cases n
      · simp [hzero, mul_assoc]
      · simp [hone, coeff_X_pow_mul', mul_assoc]

  have Jshape : iterate F 5 =
      X + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) * Q := by
    apply reconstruction
    · simpa only [coeff_zero_eq_constantCoeff] using iterate_constant F_zero 5
    · exact iterate_one F_zero F_one 5
    · intro m hm
      simpa only [map_iterates (Int.castRingHom (ZMod 8)) source_zero, F] using
        mapped_tail m hm

  have cleared_residual {R : Type} [CommRing R] (h8 : (8 : R) = 0) (x : R) :
      let D := 1 - x ^ 4
      let N := x * D + x ^ 2 * (5 + x + x ^ 2 + 5 * x ^ 3)
      N * D ^ 4 - N ^ 5 +
        N ^ 2 * (3 * D ^ 3 + N * D ^ 2 + 7 * N ^ 2 * D + 5 * N ^ 3) -
        x * (D ^ 5 - N ^ 4 * D) = 0 := by
    dsimp
    linear_combination (1 * x ^ 2 +
        4 * x ^ 3 +
        13 * x ^ 4 +
        33 * x ^ 5 +
        173 * x ^ 6 +
        659 * x ^ 7 +
        1624 * x ^ 8 +
        3096 * x ^ 9 +
        5219 * x ^ 10 +
        7141 * x ^ 11 +
        9924 * x ^ 12 +
        13244 * x ^ 13 +
        12257 * x ^ 14 +
        13401 * x ^ 15 +
        15948 * x ^ 16 +
        10252 * x ^ 17 +
        9004 * x ^ 18 +
        10223 * x ^ 19 +
        4235 * x ^ 20 +
        2975 * x ^ 21 +
        3426 * x ^ 22 +
        700 * x ^ 23 +
        384 * x ^ 24 +
        480 * x ^ 25) * h8

  have inverse_of_products {R : Type} [CommRing R] (h8 : (8 : R) = 0)
      (x j k : R) (hD : IsUnit (1 - x ^ 4)) (hE : IsUnit (1 - j ^ 4))
      (hj : j * (1 - x ^ 4) =
        x * (1 - x ^ 4) + x ^ 2 * (5 + x + x ^ 2 + 5 * x ^ 3))
      (hk : k * (1 - j ^ 4) =
        j * (1 - j ^ 4) + j ^ 2 * (3 + j + 7 * j ^ 2 + 5 * j ^ 3)) :
      k = x := by
    let D := 1 - x ^ 4
    let N := x * D + x ^ 2 * (5 + x + x ^ 2 + 5 * x ^ 3)
    have hjD : j * D = N := hj
    have hclear :
        (j * (1 - j ^ 4) + j ^ 2 * (3 + j + 7 * j ^ 2 + 5 * j ^ 3) -
          x * (1 - j ^ 4)) * D ^ 5 = 0 := by
      calc
        _ = (j * D) * D ^ 4 - (j * D) ^ 5 +
            (j * D) ^ 2 * (3 * D ^ 3 + (j * D) * D ^ 2 +
              7 * (j * D) ^ 2 * D + 5 * (j * D) ^ 3) -
            x * (D ^ 5 - (j * D) ^ 4 * D) := by ring
        _ = 0 := by
          rw [hjD]
          exact cleared_residual h8 x
    have hcancel :
        j * (1 - j ^ 4) + j ^ 2 * (3 + j + 7 * j ^ 2 + 5 * j ^ 3) =
          x * (1 - j ^ 4) := by
      apply sub_eq_zero.mp
      apply (hD.pow 5).mul_right_cancel
      simpa only [zero_mul] using hclear
    exact hE.mul_right_cancel (hk.trans hcancel)

  have subst_inverse (Q : PowerSeries (ZMod 8))
      (hQ : Q * (1 - X ^ 4) = 1) :
      let J : PowerSeries (ZMod 8) := X + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) * Q
      let K : PowerSeries (ZMod 8) := X + X ^ 2 * (3 + X + 7 * X ^ 2 + 5 * X ^ 3) * Q
      K.subst J = X := by
    let J : PowerSeries (ZMod 8) := X + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) * Q
    let K : PowerSeries (ZMod 8) := X + X ^ 2 * (3 + X + 7 * X ^ 2 + 5 * X ^ 3) * Q
    change K.subst J = X
    have h8 : (8 : PowerSeries (ZMod 8)) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 8)) (show (8 : ZMod 8) = 0 by decide)
    have hD : IsUnit (1 - X ^ 4 : PowerSeries (ZMod 8)) := by
      apply isUnit_iff_constantCoeff.mpr
      simp
    have Jzero : constantCoeff J = 0 := by simp [J]
    have hE : IsUnit (1 - J ^ 4) := by
      apply isUnit_iff_constantCoeff.mpr
      simp [Jzero]
    have Jsubst : HasSubst J := .of_constantCoeff_zero Jzero
    let S := substAlgHom (R := ZMod 8) (S := ZMod 8) Jsubst
    have SX : S X = J := substAlgHom_X Jsubst
    have hj : J * (1 - X ^ 4) =
        X * (1 - X ^ 4) + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) := by
      dsimp [J]
      rw [add_mul, mul_assoc, hQ, mul_one]
    have hK : K * (1 - X ^ 4) =
        X * (1 - X ^ 4) + X ^ 2 * (3 + X + 7 * X ^ 2 + 5 * X ^ 3) := by
      dsimp [K]
      rw [add_mul, mul_assoc, hQ, mul_one]
    have hk : (K.subst J) * (1 - J ^ 4) =
        J * (1 - J ^ 4) + J ^ 2 * (3 + J + 7 * J ^ 2 + 5 * J ^ 3) := by
      have h := congrArg S hK
      simpa only [map_mul, map_sub, map_one, map_pow, map_add, map_ofNat,
        SX, S, coe_substAlgHom] using h
    exact inverse_of_products h8 X J (K.subst J) hD hE hj hk

  have inverse : K.subst (iterate F 5) = X := by
    rw [Jshape]
    exact subst_inverse Q Q_geometric

  have eighth_identity : iterate F 8 = (X : PowerSeries (ZMod 8)) := by
    ext n
    by_cases h0 : n = 0
    · subst n
      simp only [coeff_zero_eq_constantCoeff, iterate_constant F_zero, constantCoeff_X]
    by_cases h1 : n = 1
    · subst n
      rw [iterate_one F_zero F_one, coeff_one_X]
    have hn : 1 < n := by omega
    dsimp only [F]
    rw [← map_iterates (Int.castRingHom (ZMod 8)) source_zero, coeff_map,
      coeff_X, if_neg h1]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight.result n hn)

  have third_fifth_identity : (iterate F 3).subst (iterate F 5) = X := by
    rw [← iterate_add F_zero]
    exact eighth_identity

  have subst_injective_of_linear_unit {R : Type} [CommRing R] (u : PowerSeries R)
      (h0 : constantCoeff u = 0) (h1 : IsUnit (coeff 1 u)) :
      Function.Injective (fun f : PowerSeries R => f.subst u) := by
    intro f g h
    have hh := congrArg (fun p : PowerSeries R => p.subst (u.substInvOfIsUnit h1)) h
    rw [subst_comp_subst_apply (.of_constantCoeff_zero h0) (.substInvOfIsUnit u h1),
      subst_comp_subst_apply (.of_constantCoeff_zero h0) (.substInvOfIsUnit u h1),
      subst_substInvOfIsUnit_right u h0 h1, X_subst, X_subst] at hh
    exact hh

  have third_equals_K (inverse : K.subst (iterate F 5) = X) : iterate F 3 = K := by
    apply subst_injective_of_linear_unit (iterate F 5) (iterate_constant F_zero 5)
      (by rw [iterate_one F_zero F_one]; exact isUnit_one)
    exact third_fifth_identity.trans inverse.symm

  have periodic (m : ℕ) :
      coeff m (((3 : PowerSeries (ZMod 8)) + (X : PowerSeries (ZMod 8)) +
        (7 : PowerSeries (ZMod 8)) * (X : PowerSeries (ZMod 8)) ^ 2 +
        (5 : PowerSeries (ZMod 8)) * (X : PowerSeries (ZMod 8)) ^ 3) * Q) =
      if m % 4 = 0 then (3 : ZMod 8) else if m % 4 = 1 then 1 else
        if m % 4 = 2 then 7 else 5 := by
    have hs :
        ((3 : PowerSeries (ZMod 8)) + X + 7 * X ^ 2 + 5 * X ^ 3) * Q =
        C (3 : ZMod 8) * Q + (X : PowerSeries (ZMod 8)) ^ 1 * Q +
        C (7 : ZMod 8) * ((X : PowerSeries (ZMod 8)) ^ 2 * Q) +
        C (5 : ZMod 8) * ((X : PowerSeries (ZMod 8)) ^ 3 * Q) := by
      simp only [map_ofNat]
      ring
    rw [hs]
    simp only [map_add, coeff_C_mul, coeff_X_pow_mul', Q, coeff_mk]
    by_cases hm : m < 3
    · interval_cases m <;> norm_num
    · have hr := Nat.mod_lt m (by omega : 0 < 4)
      interval_cases h : m % 4 <;>
        simp (disch := omega) only [if_pos, if_neg, mul_one, mul_zero, zero_add, add_zero] <;>
          norm_num

  have K_coeff (n : ℕ) (hn : 1 < n) : coeff n K =
      if (n - 2) % 4 = 0 then (3 : ZMod 8) else if (n - 2) % 4 = 1 then 1 else
        if (n - 2) % 4 = 2 then 7 else 5 := by
    dsimp only [K]
    rw [map_add, coeff_X, if_neg (by omega : n ≠ 1), zero_add,
      mul_assoc, coeff_X_pow_mul', if_pos (by omega : 2 ≤ n)]
    exact periodic (n - 2)

  have hc := K_coeff n hn
  rw [← third_equals_K inverse] at hc
  have h : ((coeff n (iterate generatingSeries 3) -
      (if (n - 2) % 4 = 0 then (3 : ℤ) else if (n - 2) % 4 = 1 then 1 else
        if (n - 2) % 4 = 2 then 7 else 5) : ℤ) : ZMod 8) = 0 := by
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_ofNat, Int.cast_one]
    apply sub_eq_zero.mpr
    simpa only [F, ← map_iterates (Int.castRingHom (ZMod 8)) source_zero,
      coeff_map, Int.coe_castRingHom] using hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h


#print axioms result

end D5.S1.Recurrence.Residue.IterateProductFourFiveThirdModEight
