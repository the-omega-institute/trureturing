/- GID: D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The eighth iterate of A396798 has coefficients above degree one divisible by eight. -/

import D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix
import D5.S1.Recurrence.Residue.IterateProductTwentyFiveModFive
import D5.S1.Recurrence.Parity.DiagonalIterateEven

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate mobius mobius_iterate)
open D5.S1.Recurrence.Residue.IterateProductTwentyFiveModFive (nilpotent_iterate)
open private product_contract iterate_constant coeff_eq_of_dvd map_iterates from
  D5.S1.Recurrence.Invariants.ThreeFourIterateProductModSix
open private mobius_zero mobius_denominator denominator from
  D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
open private iterate_add from D5.S1.Recurrence.Parity.DiagonalIterateEven

namespace D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight

/-- The integer ordinary series obtained by coefficientwise stabilization of the source equation. -/
noncomputable def generatingSeries : PowerSeries ℤ :=
  mk fun n => coeff n
    ((fun f : PowerSeries ℤ => X + iterate f 4 * iterate f 5)^[n + 1] 0)

/-- Hanna's eighth conjecture for A396798, over every index in its stated range. -/
theorem result (n : ℕ) (hn : 1 < n) :
    (8 : ℤ) ∣ coeff n (iterate generatingSeries 8) := by
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
  -- Uniqueness holds over every coefficient ring, including the integer source and its reductions.
  have unique (S : Type) [CommRing S] {f g : PowerSeries S}
      (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
      (hff : f = X + iterate f 4 * iterate f 5)
      (hgg : g = X + iterate g 4 * iterate g 5) : f = g := by
    have hd : ∀ d : ℕ, (X : PowerSeries S) ^ d ∣ f - g := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        have h := product_contract hf hg ih 4 5
        simpa only [← hff, ← hgg] using h
    ext k
    exact coeff_eq_of_dvd (hd (k + 1)) (Nat.lt_succ_self k)
  have source_one : coeff 1 generatingSeries = 1 := by
    have h := congrArg (coeff 1) source_equation
    simpa only [map_add, coeff_one_X, coeff_one_mul,
      iterate_constant _ source_zero, mul_zero, zero_mul, add_zero] using h
  let hom4 := Int.castRingHom (ZMod 4)
  have map4_zero : constantCoeff (generatingSeries.map hom4) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      source_zero, map_zero]
  have map4_equation : generatingSeries.map hom4 =
      X + iterate (generatingSeries.map hom4) 4 * iterate (generatingSeries.map hom4) 5 := by
    simpa only [map_add, map_X, map_mul, map_iterates hom4 source_zero] using
      congrArg (fun f : PowerSeries ℤ => f.map hom4) source_equation
  have mobius4 : iterate (mobius (1 : ZMod 4)) 4 = X := by
    rw [mobius_iterate]
    simp only [Nat.cast_ofNat, mul_one]
    rw [show (4 : ZMod 4) = 0 by decide]
    simp [mobius]
  have mobius5 : iterate (mobius (1 : ZMod 4)) 5 = mobius 1 := by
    rw [mobius_iterate]
    simp only [Nat.cast_ofNat, mul_one]
    rw [show (5 : ZMod 4) = 1 by decide]
  have mobius_equation : mobius (1 : ZMod 4) =
      X + iterate (mobius (1 : ZMod 4)) 4 * iterate (mobius (1 : ZMod 4)) 5 := by
    rw [mobius4, mobius5]
    have h := mobius_denominator (1 : ZMod 4)
    simp only [denominator, map_one, one_mul] at h
    linear_combination h
  have mod4 : generatingSeries.map hom4 = mobius 1 :=
    unique (ZMod 4) map4_zero (mobius_zero 1) map4_equation mobius_equation
  have fourth_mod4 : (iterate generatingSeries 4).map hom4 = X := by
    rw [map_iterates hom4 source_zero, mod4]
    exact mobius4
  have fourth_div (k : ℕ) : (4 : ℤ) ∣ coeff k (iterate generatingSeries 4 - X) := by
    have hzero : (iterate generatingSeries 4 - X).map hom4 = 0 := by
      rw [map_sub, map_X, fourth_mod4, sub_self]
    have h := congrArg (coeff k) hzero
    simp only [coeff_map, map_zero, hom4, Int.coe_castRingHom] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  let b : PowerSeries ℤ := mk fun k => coeff k (iterate generatingSeries 4 - X) / 4
  have fourth_decomposition : iterate generatingSeries 4 = X + C (4 : ℤ) * b := by
    ext k
    have h := Int.mul_ediv_cancel' (fourth_div k)
    simp only [map_sub] at h
    simp only [map_add, coeff_C_mul, b, coeff_mk, map_sub]
    linear_combination -h
  let hom8 := Int.castRingHom (ZMod 8)
  have fourth_zero : constantCoeff (iterate generatingSeries 4) = 0 :=
    iterate_constant _ source_zero 4
  have map8_zero : constantCoeff ((iterate generatingSeries 4).map hom8) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      fourth_zero, map_zero]
  have map8_decomposition : (iterate generatingSeries 4).map hom8 =
      X + C (4 : ZMod 8) * b.map hom8 := by
    rw [fourth_decomposition]
    simp only [map_add, map_mul, map_X, map_C, hom8, Int.coe_castRingHom]
    norm_num
  have twice_fourth : iterate ((iterate generatingSeries 4).map hom8) 2 = X := by
    rw [map8_decomposition]
    have h := nilpotent_iterate (4 : ZMod 8) (by decide) (b.map hom8)
      (map8_decomposition ▸ map8_zero) 2
    simpa only [Nat.cast_ofNat, show (2 : ZMod 8) * 4 = 0 by decide,
      map_zero, zero_mul, add_zero] using h
  have grouping : iterate generatingSeries 8 = iterate (iterate generatingSeries 4) 2 := by
    calc
      iterate generatingSeries 8 =
          (iterate generatingSeries 4).subst (iterate generatingSeries 4) :=
        iterate_add source_zero source_one 4 4
      _ = iterate (iterate generatingSeries 4) 2 := by
        change _ = PowerSeries.subst (iterate generatingSeries 4)
          (PowerSeries.subst (iterate generatingSeries 4) (X : PowerSeries ℤ))
        rw [subst_X (.of_constantCoeff_zero fourth_zero)]
  have eighth_mod8 : (iterate generatingSeries 8).map hom8 = X := by
    rw [grouping, map_iterates hom8 fourth_zero]
    exact twice_fourth
  have h := congrArg (coeff n) eighth_mod8
  simp only [coeff_map, hom8, Int.coe_castRingHom, coeff_X,
    if_neg (by omega : n ≠ 1)] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end D5.S1.Recurrence.Residue.IterateProductFourFiveEighthModEight
