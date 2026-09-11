/- GID: D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Frobenius and binary descent prove Hanna's Fibbinary parity conjecture. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Bitwise

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity

noncomputable def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 0 then a ((n + 1) / 2)
      else -∑ j : Fin (n / 2 + 1), a j * a (n / 2 - j)
termination_by n => n
decreasing_by all_goals omega

noncomputable def generatingSeries : PowerSeries ℤ := mk a

/-- The bitwise intersection detects precisely pairs of adjacent one bits. -/
def Fibbinary (n : ℕ) : Prop := n &&& (n >>> 1) = 0

private theorem coeff_square {R : Type*} [CommRing R] (B : PowerSeries R) (n : ℕ) :
    coeff n (B ^ 2) = ∑ j : Fin (n + 1), coeff j B * coeff (n - j) B := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]

private theorem coeff_step {R : Type*} [CommRing R] (B : PowerSeries R) (n : ℕ) :
    coeff (n + 1) (B.subst (X ^ 2) - X * (B.subst (X ^ 2)) ^ 2) =
      if (n + 1) % 2 = 0 then coeff ((n + 1) / 2) B
      else -∑ j : Fin (n / 2 + 1), coeff j B * coeff (n / 2 - j) B := by
  rw [map_sub, coeff_succ_X_mul, ← subst_pow (.X_pow (by decide : 2 ≠ 0)),
    coeff_subst_X_pow (by decide : 2 ≠ 0), coeff_subst_X_pow (by decide : 2 ≠ 0)]
  simp only [Algebra.algebraMap_self_apply, Nat.dvd_iff_mod_eq_zero]
  by_cases h : (n + 1) % 2 = 0
  · rw [if_pos h, if_pos h, if_neg (by omega), sub_zero]
  · rw [if_neg h, if_neg h, if_pos (by omega), zero_sub, coeff_square]

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = generatingSeries.subst (X ^ 2) -
      X * (generatingSeries.subst (X ^ 2)) ^ 2 := by
  refine ⟨by simp [generatingSeries, a], ?_⟩
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n => simpa [generatingSeries, a] using (coeff_step generatingSeries n).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = B.subst (X ^ 2) - X * (B.subst (X ^ 2)) ^ 2) :
    B = generatingSeries := by
  have hc : ∀ n, coeff n B = a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa [a, coeff_zero_eq_constantCoeff] using h0
      | succ n =>
        have he := congrArg (coeff (n + 1)) hB
        rw [coeff_step] at he
        rw [he, a]
        split_ifs with h
        · exact ih _ (by omega)
        · congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j (by have := j.isLt; omega), ih (n / 2 - j) (by omega)]
  ext n
  simpa [generatingSeries] using hc n

private theorem square_subst (f : PowerSeries (ZMod 2)) :
    f ^ 2 = f.subst (X ^ 2) := by
  have he := MvPowerSeries.map_frobenius_expand (f := f) 2 (by decide)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at he
  exact he.symm.trans (PowerSeries.expand_apply 2 (by decide) f)

private theorem binary_recurrence (n : ℕ) :
    (a (n + 1) : ZMod 2) =
      if (n + 1) % 2 = 0 then (a ((n + 1) / 2) : ZMod 2)
      else if (n / 2) % 2 = 0 then (a (n / 2 / 2) : ZMod 2) else 0 := by
  let hom := Int.castRingHom (ZMod 2)
  let f := generatingSeries.map hom
  have hm : PowerSeries.map hom (generatingSeries.subst (X ^ 2)) = f.subst (X ^ 2) := by
    have he : PowerSeries.map hom (generatingSeries.subst (X ^ 2)) =
        f.subst ((X ^ 2 : PowerSeries ℤ).map hom) :=
      map_subst (.X_pow (by decide : 2 ≠ 0)) _
    simpa only [map_pow, map_X] using he
  have hf : f = f.subst (X ^ 2) - X * (f.subst (X ^ 2)) ^ 2 := by
    have he := congrArg (PowerSeries.map hom) generating_equation.2
    rw [map_sub, map_mul, map_pow, map_X, hm] at he
    exact he
  have hc := congrArg (coeff (n + 1)) hf
  rw [coeff_step, ← coeff_square, square_subst, coeff_subst_X_pow (by decide : 2 ≠ 0)] at hc
  simpa only [f, coeff_map, generatingSeries, coeff_mk, hom,
    Int.coe_castRingHom, Algebra.algebraMap_self_apply, Nat.dvd_iff_mod_eq_zero,
    CharTwo.neg_eq] using hc

private theorem fibbinary_bits (n : ℕ) :
    Fibbinary n ↔ ∀ i, (n.testBit i && n.testBit (i + 1)) = false := by
  constructor
  · intro h i
    have he := congrArg (fun k => Nat.testBit k i) h
    simpa only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.zero_testBit,
      Nat.add_comm 1 i] using he
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro i
    simpa only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.add_comm 1 i] using h i

private theorem fibbinary_bit (b : Bool) (n : ℕ) :
    Fibbinary (Nat.bit b n) ↔ (b && n.testBit 0) = false ∧ Fibbinary n := by
  rw [fibbinary_bits, fibbinary_bits]
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · simpa only [Nat.testBit_bit_zero, Nat.testBit_bit_succ] using h 0
    · simpa only [Nat.testBit_bit_succ] using h (i + 1)
  · rintro ⟨hz, hs⟩ i
    cases i with
    | zero => simpa only [Nat.testBit_bit_zero, Nat.testBit_bit_succ] using hz
    | succ i => simpa only [Nat.testBit_bit_succ] using hs i

private theorem fibbinary_even (n : ℕ) : Fibbinary (2 * n) ↔ Fibbinary n := by
  simpa only [Nat.bit_false, two_mul, Bool.false_and, true_and] using fibbinary_bit false n

private theorem fibbinary_one (n : ℕ) : Fibbinary (4 * n + 1) ↔ Fibbinary n := by
  have he : 4 * n + 1 = Nat.bit true (Nat.bit false n) := by simp [Nat.bit]; omega
  simp only [he, fibbinary_bit, Nat.testBit_bit_zero, Bool.true_and, Bool.false_and,
    true_and]

private theorem fibbinary_three (n : ℕ) : ¬ Fibbinary (4 * n + 3) := by
  have he : 4 * n + 3 = Nat.bit true (Nat.bit true n) := by simp [Nat.bit]; omega
  rw [he, fibbinary_bit, Nat.testBit_bit_zero]
  simp

private theorem parity_all (n : ℕ) : (a n : ZMod 2) = 1 ↔ Fibbinary n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a, Fibbinary]
    | succ n =>
      by_cases he : (n + 1) % 2 = 0
      · rw [binary_recurrence, if_pos he, ih _ (by omega)]
        have hi : n + 1 = 2 * ((n + 1) / 2) := by omega
        simpa only [← hi] using (fibbinary_even ((n + 1) / 2)).symm
      · by_cases hp : (n / 2) % 2 = 0
        · rw [binary_recurrence, if_neg he, if_pos hp, ih _ (by omega)]
          have hi : n + 1 = 4 * (n / 2 / 2) + 1 := by omega
          simpa only [← hi] using (fibbinary_one (n / 2 / 2)).symm
        · rw [binary_recurrence, if_neg he, if_neg hp]
          have hi : n + 1 = 4 * (n / 4) + 3 := by omega
          exact iff_of_false (by decide) (hi ▸ fibbinary_three (n / 4))

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ Fibbinary n := by
  cases n with
  | zero => omega
  | succ n => exact ZMod.intCast_eq_one_iff_odd.symm.trans (parity_all (n + 1))

#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity
