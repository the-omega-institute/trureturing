/- GID: D5/S3/Analytic/Zeta/PrimeQuadraticLValues
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/PrimeQuadraticLValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The genuine prime quadratic Dirichlet character and its half-interval L-zero value. -/

import D5.S3.Analytic.Zeta.QuadraticLValueSquare
import D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

namespace D5.S3.Analytic.Zeta.PrimeQuadraticLValues

open scoped BigOperators
open DirichletCharacter

/-- The same integer-valued quadratic character as in the Legendre symbol,
mapped to the coefficient field used by Mathlib's L-functions. -/
noncomputable def primeCharacter (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem primeCharacter_quadratic (p : ℕ) [Fact p.Prime] :
    (primeCharacter p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem primeCharacter_nontrivial (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeCharacter p ≠ 1 := by
  apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective : Function.Injective
    (Int.castRingHom ℂ))).mpr
  exact quadraticChar_ne_one ((ZMod.ringChar_zmod_n p).substr hp)

theorem primeCharacter_primitive (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (primeCharacter p).IsPrimitive := by
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
      (DirichletCharacter.conductor_dvd_level (primeCharacter p)) with h | h
  · exact (primeCharacter_nontrivial p hp
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
  · exact h

theorem primeCharacter_odd (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    (primeCharacter p).Odd := by
  have hp2 : p ≠ 2 := by omega
  change ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) = -1
  rw [quadraticChar_neg_one ((ZMod.ringChar_zmod_n p).substr hp2),
    ZMod.card, ZMod.χ₄_nat_three_mod_four hp]
  norm_num

/-- A finite doubling argument gives the half-interval sum from the actual analytic L(0).
This theorem uses no class-number parameter or class-number identity. -/
theorem half_sum_eq_LFunction_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) :
    (∑ x : ZMod p, if x.val ≤ (p - 1) / 2 then χ x else 0) =
      (2 - χ 2) * LFunction χ 0 := by
  have hpodd : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
  have hχtwo : χ 2 ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr htwo)
  have hχsq : χ 2 ^ 2 = 1 := by
    rcases hquad 2 with h | h | h
    · exact (hχtwo h).elim
    · rw [h]; norm_num
    · rw [h]; norm_num
  let W : ℂ := ∑ x : ZMod p, (x.val : ℂ) * χ x
  let c : ℂ := ∑ x : ZMod p, if x.val ≤ (p - 1) / 2 then χ x else 0
  have hval (x : ZMod p) : ((2 * x).val : ℂ) =
      2 * (x.val : ℂ) - p + if x.val ≤ (p - 1) / 2 then (p : ℂ) else 0 := by
    have hxlt := x.val_lt
    by_cases hx : x.val ≤ (p - 1) / 2
    · have hxx : x.val + x.val < p := by omega
      rw [two_mul, ZMod.val_add_of_lt hxx, Nat.cast_add, if_pos hx]
      ring
    · have hxx : p ≤ x.val + x.val := by omega
      rw [two_mul, ZMod.val_add_of_le hxx, Nat.cast_sub hxx, Nat.cast_add, if_neg hx]
      ring
  have htotal : ∑ x : ZMod p, χ x = 0 := χ.sum_eq_zero_of_ne_one hne
  have hW : W = χ 2 * (2 * W + p * c) := by
    calc
      W = ∑ x : ZMod p, ((2 * x).val : ℂ) * χ (2 * x) :=
        (Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) htwo)
          (fun x : ZMod p => (x.val : ℂ) * χ x)).symm
      _ = ∑ x : ZMod p,
          χ 2 * (2 * ((x.val : ℂ) * χ x) - (p : ℂ) * χ x +
            p * (if x.val ≤ (p - 1) / 2 then χ x else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hval, map_mul]
        split_ifs <;> ring
      _ = χ 2 * (2 * W + p * c) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          htotal, mul_zero, sub_zero, W, c]
  have hrelation : (p : ℂ) * c = (χ 2 - 2) * W := by
    have h := congrArg (fun z : ℂ => χ 2 * z) hW
    have hs : χ 2 * (χ 2 * (2 * W + p * c)) = 2 * W + p * c := by
      rw [← mul_assoc, ← sq, hχsq, one_mul]
    rw [hs] at h
    linear_combination -h
  rw [CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum p χ hne]
  change c = (2 - χ 2) * (-W / (p : ℂ))
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hpne
  rw [hrelation]
  field_simp [hpne] <;> ring

end D5.S3.Analytic.Zeta.PrimeQuadraticLValues
