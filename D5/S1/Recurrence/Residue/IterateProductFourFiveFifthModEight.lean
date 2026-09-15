/- GID: D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fifth iterate of A396798 repeats 5,1,1,5 modulo eight above degree one. -/

import D5.S1.Recurrence.Residue.IterateProductFourFiveFourthModEight

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate)
open D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight (generatingSeries)
open private product_contract iterate_constant coeff_eq_of_dvd map_iterates from
  D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix
open private iterate_normal iterate_top Agree from
  D5.S1.Recurrence.Residue.IterateProductTwentyFiveModFive
open private iterate_add from D5.S1.Recurrence.Parity.DiagonalIterateEven

namespace D5.S1.Recurrence.Residue.IterateProductFourFiveFifthModEight

/-- Hanna's fifth conjecture for A396798, with the period beginning at degree two. -/
theorem result (n : ℕ) (hn : 1 < n) :
    (8 : ℤ) ∣ coeff n (iterate generatingSeries 5) -
      (if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then (5 : ℤ) else 1) := by
  let H : PowerSeries ℤ → PowerSeries ℤ := fun f => X + iterate f 4 * iterate f 5
  let approx : ℕ → PowerSeries ℤ := fun d => H^[d] 0
  have approx_succ (d : ℕ) : approx (d + 1) = H (approx d) :=
    Function.iterate_succ_apply' H d 0
  have approx_zero (d : ℕ) : constantCoeff (approx d) = 0 := by
    induction d with
    | zero => simp [approx]
    | succ d ih =>
      rw [approx_succ]
      simp only [H, map_add, constantCoeff_X, map_mul,
        iterate_constant _ ih, mul_zero, zero_add]
  have approx_stable {d e : ℕ} (h : d ≤ e) :
      (X : PowerSeries ℤ) ^ d ∣ approx d - approx e := by
    induction d generalizing e with
    | zero => simp
    | succ d ih =>
      cases e with
      | zero => omega
      | succ e =>
        rw [approx_succ, approx_succ]
        exact product_contract (approx_zero d) (approx_zero e) (ih (by omega)) 4 5
  have generating_approx (d : ℕ) :
      (X : PowerSeries ℤ) ^ d ∣ generatingSeries - approx d := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp only [map_sub, sub_eq_zero, generatingSeries, coeff_mk]
    exact coeff_eq_of_dvd (approx_stable (by omega : k + 1 ≤ d)) (Nat.lt_succ_self k)
  have source_zero : constantCoeff generatingSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff,
      coeff_eq_of_dvd (generating_approx 1) (by omega : 0 < 1), coeff_zero_eq_constantCoeff]
    exact approx_zero 1
  have source_equation : generatingSeries =
      X + iterate generatingSeries 4 * iterate generatingSeries 5 := by
    ext k
    have ha := coeff_eq_of_dvd (generating_approx (k + 2)) (by omega : k < k + 2)
    rw [approx_succ] at ha
    exact ha.trans (coeff_eq_of_dvd
      (product_contract source_zero (approx_zero (k + 1)) (generating_approx (k + 1)) 4 5)
      (by omega : k < k + 1 + 1)).symm
  have source_one : coeff 1 generatingSeries = 1 := by
    have h := congrArg (coeff 1) source_equation
    simpa only [map_add, coeff_one_X, coeff_one_mul,
      iterate_constant _ source_zero, mul_zero, zero_mul, add_zero] using h
  have normal (j : ℕ) := iterate_normal source_zero source_one j
  have source_two : coeff 2 generatingSeries = 1 := by
    have h := congrArg (coeff 2) source_equation
    have ha : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
    simpa [coeff_mul, coeff_X, ha, coeff_zero_eq_constantCoeff, (normal 4).1, (normal 5).1,
      (normal 4).2, (normal 5).2] using h
  have source_agree : Agree 2 generatingSeries X := by
    intro k hk
    interval_cases k
    · simpa only [coeff_zero_eq_constantCoeff, constantCoeff_X] using source_zero
    · simpa only [coeff_one_X] using source_one
  have fourth_two : coeff 2 (iterate generatingSeries 4) = 4 := by
    have h := iterate_top (by omega : 1 < 2) source_zero constantCoeff_X
      source_one coeff_one_X source_agree 4
    simpa [iterate, source_two, coeff_X] using h
  let hom8 := Int.castRingHom (ZMod 8)
  let F : PowerSeries (ZMod 8) := generatingSeries.map hom8
  let P : PowerSeries (ZMod 8) := iterate F 4
  let J : PowerSeries (ZMod 8) := iterate F 5
  have Fzero : constantCoeff F = 0 := by
    dsimp [F]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      source_zero, map_zero]
  have Fone : coeff 1 F = 1 := by
    dsimp [F]
    rw [source_one, map_one]
  have F_equation : F = X + P * J := by
    simpa only [F, P, J, map_add, map_X, map_mul, map_iterates hom8 source_zero] using
      congrArg (fun f : PowerSeries ℤ => f.map hom8) source_equation
  have map_normal (j : ℕ) := iterate_normal Fzero Fone j
  have Pshape : P = X + 4 * X ^ 2 := by
    ext k
    change coeff k (iterate F 4) = coeff k (X + C (4 : ZMod 8) * X ^ 2)
    rw [← map_iterates hom8 source_zero, coeff_map]
    by_cases hk : 2 < k
    · have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (D5.S1.Recurrence.Residue.IterateProductFourFiveFourthModEight.result k hk)
      simpa [hom8, coeff_C_mul, coeff_X, coeff_X_pow, show k ≠ 1 by omega,
        show k ≠ 2 by omega] using hz
    · interval_cases k
      · simp [coeff_zero_eq_constantCoeff, (normal 4).1]
      · simp [hom8, (normal 4).2, coeff_C_mul, coeff_X_pow]
      · simp [hom8, fourth_two, coeff_C_mul, coeff_X, coeff_X_pow]
  have eighth : iterate F 8 = X := by
    ext k
    rw [← map_iterates hom8 source_zero, coeff_map]
    by_cases hk : 1 < k
    · have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight.result k hk)
      simpa [hom8, coeff_X, show k ≠ 1 by omega] using hz
    · interval_cases k
      · simp [coeff_zero_eq_constantCoeff, (normal 8).1]
      · simp [hom8, (normal 8).2]
  have Psubst : HasSubst P := .of_constantCoeff_zero (map_normal 4).1
  have first : iterate F 1 = F := by
    simpa only [iterate] using subst_X (.of_constantCoeff_zero Fzero)
  have FP : F.subst P = J := by
    simpa only [first, P, J] using (iterate_add Fzero Fone 1 4).symm
  have PP : P.subst P = X := by
    exact (iterate_add Fzero Fone 4 4).symm.trans eighth
  have JP : J.subst P = F := by
    calc
      J.subst P = iterate F 9 := (iterate_add Fzero Fone 5 4).symm
      _ = (iterate F 8).subst (iterate F 1) := iterate_add Fzero Fone 8 1
      _ = F := by rw [eighth, first, subst_X (.of_constantCoeff_zero Fzero)]
  have J_linear : J = P + X * F := by
    have h := congrArg (fun f : PowerSeries (ZMod 8) => f.subst P) F_equation
    simpa only [subst_add Psubst, subst_mul Psubst, subst_X Psubst, FP, PP, JP] using h
  have J_denominator : J * (1 - X ^ 2 - 4 * X ^ 3) = X + 5 * X ^ 2 := by
    rw [Pshape] at F_equation J_linear
    linear_combination J_linear + X * F_equation
  have h8 : (8 : PowerSeries (ZMod 8)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 8)) (show (8 : ZMod 8) = 0 by decide)
  have den_product : (1 - X ^ 2 - 4 * X ^ 3 : PowerSeries (ZMod 8)) *
      (1 + X ^ 2 + 4 * X ^ 3) = 1 - X ^ 4 := by
    linear_combination -(X ^ 5 + 2 * X ^ 6) * h8
  have num_product : (X + 5 * X ^ 2 : PowerSeries (ZMod 8)) *
      (1 + X ^ 2 + 4 * X ^ 3) = X + 5 * X ^ 2 + X ^ 3 + X ^ 4 + 4 * X ^ 5 := by
    linear_combination (X ^ 4 + 2 * X ^ 5) * h8
  have J_product : J * (1 - X ^ 4) =
      X + 5 * X ^ 2 + X ^ 3 + X ^ 4 + 4 * X ^ 5 := by
    rw [← den_product, ← mul_assoc, J_denominator, num_product]
  have tail_product : (J - X) * (1 - X ^ 4) =
      5 * X ^ 2 + X ^ 3 + X ^ 4 + 5 * X ^ 5 := by
    linear_combination J_product
  let Q : PowerSeries (ZMod 8) := (mk 1 : PowerSeries (ZMod 8)).subst (X ^ 4)
  have Q_inverse : Q * (1 - X ^ 4) = 1 := by
    have h := congrArg (substAlgHom (R := ZMod 8) (S := ZMod 8)
      (HasSubst.X_pow (by omega : (4 : ℕ) ≠ 0)))
      (mk_one_mul_one_sub_eq_one (ZMod 8))
    simpa only [map_mul, map_sub, map_one, coe_substAlgHom,
      subst_X (HasSubst.X_pow (by omega : (4 : ℕ) ≠ 0)), Q] using h
  have denominator_unit : IsUnit (1 - X ^ 4 : PowerSeries (ZMod 8)) := by
    apply isUnit_iff_constantCoeff.mpr
    simp
  have Jshape : J = X + X ^ 2 * (5 + X + X ^ 2 + 5 * X ^ 3) * Q := by
    apply denominator_unit.mul_right_cancel
    rw [add_mul, mul_assoc, Q_inverse, mul_one]
    linear_combination tail_product
  have Qcoeff (m : ℕ) : coeff m Q = if 4 ∣ m then 1 else 0 := by
    simp [Q, coeff_subst_X_pow (by omega : (4 : ℕ) ≠ 0)]
  have periodic (m : ℕ) : coeff m ((5 + X + X ^ 2 + 5 * X ^ 3) * Q) =
      if m % 4 = 0 ∨ m % 4 = 3 then 5 else 1 := by
    have hs : (5 + X + X ^ 2 + 5 * X ^ 3) * Q =
        C (5 : ZMod 8) * Q + X ^ 1 * Q + X ^ 2 * Q + C (5 : ZMod 8) * (X ^ 3 * Q) := by
      simp only [map_ofNat]
      ring
    rw [hs]
    simp only [map_add, coeff_C_mul, coeff_X_pow_mul', Qcoeff, Nat.dvd_iff_mod_eq_zero]
    by_cases hm : m < 3
    · interval_cases m <;> norm_num
    · have hr := Nat.mod_lt m (by omega : 0 < 4)
      interval_cases h : m % 4 <;>
        simp (disch := omega) only [if_pos, if_neg, mul_one, mul_zero, zero_add, add_zero] <;>
          norm_num
  have Jcoeff : coeff n J =
      if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then 5 else 1 := by
    rw [Jshape, map_add, coeff_X, if_neg (by omega : n ≠ 1), zero_add,
      mul_assoc, coeff_X_pow_mul', if_pos (by omega : 2 ≤ n)]
    exact periodic (n - 2)
  have h : ((coeff n (iterate generatingSeries 5) -
      (if (n - 2) % 4 = 0 ∨ (n - 2) % 4 = 3 then (5 : ℤ) else 1) : ℤ) : ZMod 8) = 0 := by
    rw [Int.cast_sub, Int.cast_ite, Int.cast_ofNat, Int.cast_one]
    apply sub_eq_zero.mpr
    simpa only [J, F, ← map_iterates hom8 source_zero, coeff_map, hom8,
      Int.coe_castRingHom] using Jcoeff
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h


end D5.S1.Recurrence.Residue.IterateProductFourFiveFifthModEight
