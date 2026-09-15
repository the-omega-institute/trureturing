/- GID: D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's A204061 residues mod 5 are one exactly when no base-5 digit is two. -/

import D5.S1.Recurrence.PellCompanionGcd
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

open PowerSeries
open D5.S1.Recurrence.PellCompanionGcd (Q)
open scoped Classical

namespace D5.S1.Recurrence.Invariants.CompanionPellExpBaseFiveResidue

local notation "ℚ₅" => @Padic 5 ⟨Nat.prime_five⟩
local notation "ℤ₅" => @PadicInt 5 ⟨Nat.prime_five⟩

private noncomputable def exponent : PowerSeries ℚ₅ :=
  PowerSeries.mk fun k => if k = 0 then 0 else ((Q k : ℚ₅) ^ 2) / k

private noncomputable def f : PowerSeries ℚ₅ := (PowerSeries.exp ℚ₅).subst exponent
noncomputable def a (n : ℕ) : ℚ₅ :=
  PowerSeries.coeff n ((PowerSeries.exp ℚ₅).subst
    (PowerSeries.mk fun k => if k = 0 then 0 else ((Q k : ℚ₅) ^ 2) / k))

theorem result (n : ℕ) :
    ∃ z : ℤ₅, (z : ℚ₅) = a n ∧
      (@PadicInt.toZMod 5 ⟨Nat.prime_five⟩ z) =
        (if 2 ∈ Nat.digits 5 n then (0 : ZMod 5) else 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let r : ℤ₅ := -(4 : ℤ₅).inv
  let quartic : PowerSeries ℤ₅ := (1 + X) ^ 2 * (1 - 6 * X + X ^ 2)
  let E : PowerSeries ℤ₅ := quartic - 1
  let g : PowerSeries ℤ₅ := (binomialSeries ℤ₅ r).subst E
  have hr : r + r + r + r + 1 = 0 := by
    have hu : ‖(4 : ℤ₅)‖ = 1 :=
      (PadicInt.norm_natCast_eq_one_iff (n := 4)).mpr (by decide)
    have hi := PadicInt.mul_inv hu
    dsimp [r]
    linear_combination -hi
  have hE0 : constantCoeff E = 0 := by
    simp [E, quartic, ← map_ofNat C 6]
  have hE : HasSubst E := .of_constantCoeff_zero' hE0
  have hb1 : binomialSeries ℤ₅ (1 : ℤ₅) = 1 + X := by
    simpa only [Nat.cast_one, pow_one] using
      (binomialSeries_nat (R := ℤ₅) (A := ℤ₅) 1)
  have hb : (binomialSeries ℤ₅ r) ^ 4 * (1 + X) = 1 := by
    calc
      _ = binomialSeries ℤ₅ (r + r + r + r + 1) := by
        simp only [binomialSeries_add, hb1]
        ring
      _ = 1 := by rw [hr, binomialSeries_zero]
  have hgQ : g ^ 4 * quartic = 1 := by
    have hh := congrArg (substAlgHom (R := ℤ₅) hE) hb
    simp only [map_mul, map_pow, map_add, map_one, coe_substAlgHom, subst_X hE] at hh
    change g ^ 4 * (1 + E) = 1 at hh
    calc
      _ = g ^ 4 * (1 + E) := by dsimp [E]; ring
      _ = 1 := hh
  have hg0 : constantCoeff g = 1 := by
    have hz := constantCoeff_subst_eq_zero hE0 (binomialSeries ℤ₅ r - 1) (by simp)
    have h1 : (1 : PowerSeries ℤ₅).subst E = 1 := by
      simpa only [coe_substAlgHom] using (map_one (substAlgHom (R := ℤ₅) hE))
    simpa only [subst_sub hE, h1, map_sub, map_one, sub_eq_zero, g,
      PowerSeries.constantCoeff] using hz
  let H : PowerSeries ℚ₅ := g.map (algebraMap ℤ₅ ℚ₅)
  have hH0 : constantCoeff H = 1 := by
    change algebraMap ℤ₅ ℚ₅ (constantCoeff g) = 1
    rw [hg0, map_one]
  have hHQ : H ^ 4 * ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2)) = 1 := by
    have hh := congrArg (PowerSeries.map (algebraMap ℤ₅ ℚ₅)) hgQ
    simpa only [quartic, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat, map_X, H] using hh
  have hf : constantCoeff f = 1 ∧
      f ^ 4 * ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2)) = 1 := by
    have he0 : constantCoeff exponent = 0 := by simp [exponent]
    have hs : HasSubst exponent := .of_constantCoeff_zero' he0
    have hf0 : constantCoeff f = 1 := by
      have hz := constantCoeff_subst_eq_zero he0 (PowerSeries.exp ℚ₅ - 1) (by simp)
      have h1 : (1 : PowerSeries ℚ₅).subst exponent = 1 := by
        simpa only [coe_substAlgHom] using (map_one (substAlgHom (R := ℚ₅) hs))
      simpa only [subst_sub hs, h1, map_sub, map_one, sub_eq_zero, f, PowerSeries.constantCoeff] using hz
    have hD (k : ℕ) : coeff k (derivative ℚ₅ exponent) = (Q (k + 1) : ℚ₅) ^ 2 := by
      have hk : (k : ℚ₅) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp [coeff_derivative, exponent, hk]
    have hC : (1 + X) * (1 - 6 * X + X ^ 2) * derivative ℚ₅ exponent =
        1 + 4 * X - X ^ 2 := by
      rw [show ((1 + X) * (1 - 6 * X + X ^ 2) : PowerSeries ℚ₅) =
        1 - C 5 * X ^ 1 - C 5 * X ^ 2 + X ^ 3 by simp only [map_ofNat]; ring]
      rw [show (4 : PowerSeries ℚ₅) = C 4 from (map_ofNat C 4).symm]
      ext k
      simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
        coeff_X_pow_mul', hD, coeff_one, coeff_X_pow, coeff_X]
      rcases k with _ | _ | _ | k
      · norm_num [Q]
      · norm_num [Q]
      · norm_num [Q]
      · simp only [show 1 ≤ k + 1 + 1 + 1 by omega, show 2 ≤ k + 1 + 1 + 1 by omega,
          show 3 ≤ k + 1 + 1 + 1 by omega, if_true,
          show k + 1 + 1 + 1 ≠ 0 by omega, show k + 1 + 1 + 1 ≠ 1 by omega,
          show k + 1 + 1 + 1 ≠ 2 by omega, if_false]
        have hp1 : Q (k + 4) = 2 * Q (k + 3) + Q (k + 2) := by rw [Q]
        have hp2 : Q (k + 3) = 2 * Q (k + 2) + Q (k + 1) := by rw [Q]
        have hp3 : Q (k + 2) = 2 * Q (k + 1) + Q k := by rw [Q]
        norm_num [show k + 1 + 1 + 1 - 1 + 1 = k + 3 by omega,
          show k + 1 + 1 + 1 - 2 + 1 = k + 2 by omega,
          show k + 1 + 1 + 1 - 3 + 1 = k + 1 by omega,
          show k + 1 + 1 + 1 + 1 = k + 4 by omega,
          hp1, hp2, hp3, Nat.cast_add, Nat.cast_mul]
        ring
    have hdf : derivative ℚ₅ f = f * derivative ℚ₅ exponent := by
      rw [f, derivative_subst hs, derivative_exp]
    have hode : (1 + X) * (1 - 6 * X + X ^ 2) * derivative ℚ₅ f =
        f * (1 + 4 * X - X ^ 2) := by
      rw [hdf]
      linear_combination f * hC
    refine ⟨hf0, PowerSeries.derivative.ext ?_ ?_⟩
    · rw [derivative_one]
      have hd6 : derivative ℚ₅ (6 : PowerSeries ℚ₅) = 0 := by
        rw [← map_ofNat C 6, derivative_C]
      simp only [hd6, Derivation.leibniz, derivative_pow, map_add, map_sub, derivative_one,
        derivative_X, smul_eq_mul, Nat.reduceSub]
      linear_combination 4 * f ^ 3 * (1 + X) * hode
    · simp [hf0]
  obtain ⟨hf0, hfQ⟩ := hf
  have hHf : H = f := by
    have hm : (H - f) *
        ((H ^ 3 + H ^ 2 * f + H * f ^ 2 + f ^ 3) *
          ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2))) = 0 := by
      linear_combination hHQ - hfQ
    have hn : (H ^ 3 + H ^ 2 * f + H * f ^ 2 + f ^ 3) *
        ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2)) ≠ 0 := by
      intro hz
      have hh := congrArg constantCoeff hz
      norm_num [hH0, hf0] at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hn)
  let B : PowerSeries (ZMod 5) :=
    g.map (@PadicInt.toZMod 5 ⟨Nat.prime_five⟩)
  have hB0 : constantCoeff B = 1 := by
    change (@PadicInt.toZMod 5 ⟨Nat.prime_five⟩ (constantCoeff g)) = 1
    rw [hg0, map_one]
  have hBQ : B ^ 4 * ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2)) = 1 := by
    have hh := congrArg (PowerSeries.map (@PadicInt.toZMod 5 ⟨Nat.prime_five⟩)) hgQ
    simpa only [quartic, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat, map_X, B] using hh
  refine ⟨coeff n g, ?_, ?_⟩
  · have hh := congrArg (coeff n) hHf
    simpa [H, coeff_map, a, f, exponent] using hh
  · have quartic_digit_formula (B : PowerSeries (ZMod 5))
        (h0 : constantCoeff B = 1)
        (hB : B ^ 4 * ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2)) = 1) (n : ℕ) :
        coeff n B = if 2 ∈ Nat.digits 5 n then 0 else 1 := by
      have hchar : (5 : PowerSeries (ZMod 5)) = 0 := by
        rw [← map_ofNat C 5, show (5 : ZMod 5) = 0 from rfl, map_zero]
      have hpoly : ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2) : PowerSeries (ZMod 5)) =
          1 + X ^ 1 + X ^ 3 + X ^ 4 := by
        linear_combination -(X + 2 * X ^ 2 + X ^ 3) * hchar
      have hfrob : B ^ 5 = B.subst (X ^ 5) := by
        have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 5)
          5 (by decide) (f := B)
        rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
        exact h.symm.trans (PowerSeries.expand_apply 5 (by decide) B)
      have hfunc : B = (1 + X ^ 1 + X ^ 3 + X ^ 4) * B.subst (X ^ 5) := by
        rw [← hfrob, ← hpoly]
        calc
          B = (B ^ 4 * ((1 + X) ^ 2 * (1 - 6 * X + X ^ 2))) * B := by rw [hB, one_mul]
          _ = _ := by ring
      have hcoeff (m : ℕ) : coeff m B =
          if m % 5 = 2 then 0 else coeff (m / 5) B := by
        conv_lhs => rw [hfunc]
        simp only [add_mul, one_mul, map_add, coeff_X_pow_mul',
          coeff_subst_X_pow (by decide : 5 ≠ 0), Algebra.algebraMap_self, RingHom.id_apply]
        rcases (show m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 by omega)
          with hm | hm | hm | hm | hm
        all_goals simp (disch := omega) only [if_pos, if_neg, ite_self, zero_add, add_zero]
        all_goals (congr 2; omega)
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n = 0
        · subst n
          simpa only [Nat.digits_zero, List.not_mem_nil, if_false, coeff_zero_eq_constantCoeff] using h0
        · rw [hcoeff, Nat.digits_def' (by decide) (by omega),
            ih (n / 5) (by omega)]
          by_cases hd : n % 5 = 2
          · simp [hd]
          · simp [hd, Ne.symm hd]
    exact quartic_digit_formula B hB0 hBQ n

end D5.S1.Recurrence.Invariants.CompanionPellExpBaseFiveResidue
