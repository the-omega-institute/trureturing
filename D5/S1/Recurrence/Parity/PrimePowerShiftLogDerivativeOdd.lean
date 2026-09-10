/- GID: D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Paired coefficients modulo two imply that every A393867 term is odd. -/

import D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative
import Mathlib.Data.ZMod.Basic

open PowerSeries
open D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative

namespace D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivativeOdd

private noncomputable def f : PowerSeries (ZMod 2) :=
  map (Int.castRingHom (ZMod 2)) generatingSeries

private noncomputable def defect (B : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  (1 + X) * derivative (ZMod 2) B - B

private theorem coeff_defect (B : PowerSeries (ZMod 2)) (k : ℕ) :
    coeff k (defect B) = coeff (k + 1) B * (k + 1) + coeff k B * (k - 1) := by
  cases k with
  | zero =>
    simp only [defect, add_mul, one_mul, map_add, map_neg, coeff_zero_X_mul,
      coeff_derivative, Nat.cast_zero, zero_add, mul_one, add_zero, mul_neg,
      sub_eq_add_neg]
  | succ k =>
    simp only [defect, add_mul, one_mul, map_sub, map_add, coeff_succ_X_mul,
      coeff_derivative, Nat.cast_add, Nat.cast_one]
    ring

private theorem defect_pow (B : PowerSeries (ZMod 2)) {p : ℕ}
    (hp : 1 ≤ p) (hp2 : (p : ZMod 2) = 1) :
    defect (B ^ p) = defect B * B ^ (p - 1) := by
  have hc : (p : PowerSeries (ZMod 2)) = 1 := by
    rw [← map_natCast C, hp2, map_one]
  rw [defect, derivative_pow, hc, one_mul]
  have hpow : B ^ p = B * B ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rw [hpow, defect]
  ring

private theorem f_zero : constantCoeff f = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp only [f, coeff_map, coeff_zero_eq_constantCoeff, generating_equation.1, map_one]

private theorem f_one : coeff 1 f = 1 := by
  have h := generating_equation.2 1 (by omega)
  norm_num [prime, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
    generating_equation.1] at h
  have h1 : coeff 1 generatingSeries = 1 := by omega
  simp [f, h1]

private theorem defect_f_zero : defect f = 0 := by
  ext k
  simp only [map_zero]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      simpa [coeff_defect, f_zero, f_one] using (CharTwo.add_self_eq_zero (1 : ZMod 2))
    by_cases hk2 : (k : ZMod 2) = 0
    · have hn : 1 < k + 1 := by omega
      have hprime := Nat.prime_nth_prime (k + 1 - 1)
      have hp := lt_prime (k + 1) (by omega)
      have hp2 : (prime (k + 1) : ZMod 2) = 1 :=
        (hprime.odd_of_ne_two (by change prime (k + 1) ≠ 2; omega)).natCast_zmod_two
      have he := congrArg (fun z : ℤ => (z : ZMod 2))
        (generating_equation.2 (k + 1) (by omega))
      have heq : coeff (k + 1) (f ^ prime (k + 1)) = coeff k (f ^ prime (k + 1)) := by
        simpa [f, ← map_pow, hp2] using he
      have hz : coeff k (defect (f ^ prime (k + 1))) = 0 := by
        rw [coeff_defect, hk2, heq]
        ring
      rw [defect_pow f (by omega) hp2] at hz
      obtain ⟨T, hT⟩ := X_pow_dvd_iff.mpr ih
      have hcoeff (S : PowerSeries (ZMod 2)) :
          coeff k (X ^ k * S) = constantCoeff S := by
        simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul S k 0
      rw [hT, mul_assoc, hcoeff, map_mul, map_pow, f_zero, one_pow, mul_one] at hz
      rw [hT, hcoeff]
      exact hz
    · have hk1 : (k : ZMod 2) = 1 := by
        have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        exact (hcases _).resolve_left hk2
      rw [coeff_defect, hk1]
      have htwo : (1 : ZMod 2) + 1 = 0 := rfl
      simp only [htwo, sub_self, mul_zero, add_zero]

end D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivativeOdd
