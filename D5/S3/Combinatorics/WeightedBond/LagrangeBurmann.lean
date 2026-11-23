/- GID: D5/S3/Combinatorics/WeightedBond/LagrangeBurmann
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/LagrangeBurmann
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: Formal Lagrange-Bürmann coefficient extraction over rational algebras. -/

import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

/-! Formal Lagrange-Bürmann coefficient extraction over rational algebras. -/

set_option autoImplicit false
open Finset PowerSeries

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/- This rational-algebra version follows the coefficient induction in
D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient. -/
theorem lagrange_power_coefficient (root factor : PowerSeries R) (zero : constantCoeff root = 0)
    (equation : root = X * subst root factor) :
    ∀ degree power : ℕ, 1 ≤ power → power ≤ degree →
      (degree : R) * coeff degree (root ^ power) =
        (power : R) * coeff (degree - power) (factor ^ degree) := by
  classical
  have substitution : HasSubst root := HasSubst.of_constantCoeff_zero' zero
  have vanishes (degree power : ℕ) (bound : degree < power) :
      coeff degree (root ^ power) = 0 := by
    apply coeff_of_lt_order
    exact (show (degree : ENat) < (power : ENat) by exact_mod_cast bound).trans_le
      (le_order_pow_of_constantCoeff_eq_zero power zero)
  have finiteSubstitution (source : PowerSeries R) (degree : ℕ) :
      coeff degree (subst root source) =
        ∑ power ∈ Finset.range (degree + 1),
          coeff power source * coeff degree (root ^ power) := by
    rw [coeff_subst' substitution]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro power supported
    apply Finset.mem_range.mpr
    by_contra unbounded
    have vanish := vanishes degree power (by omega)
    exact supported (by simp [vanish])
  have shifted (degree power : ℕ) (bound : power ≤ degree) :
      coeff degree (root ^ power) = coeff (degree - power) (subst root (factor ^ power)) := by
    have powers : root ^ power = X ^ power * subst root (factor ^ power) := by
      rw [subst_pow substitution, ← mul_pow, ← equation]
    rw [powers, coeff_X_pow_mul', ite_eq_left bound]
  have derivativeCoefficients (source : PowerSeries R) (degree : ℕ) :
      coeff degree (X * PowerSeries.derivative (R := R) source) = (degree : R) * coeff degree source := by
    cases degree with
    | zero => simp
    | succ degree =>
      rw [coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree inductionHypothesis =>
    intro power positive bounded
    by_cases equal : degree = power
    · subst degree
      rw [shifted power power le_rfl]
      simp only [Nat.sub_self]
      rw [finiteSubstitution]
      simp
    have differencePositive : 0 < degree - power := by omega
    have differenceSmaller : degree - power < degree := by omega
    have weighted : (degree - power : ℕ) * coeff degree (root ^ power) =
        coeff (degree - power)
          (X * PowerSeries.derivative (R := R) (factor ^ power) * factor ^ (degree - power)) := by
      rw [shifted degree power bounded, finiteSubstitution, Finset.mul_sum]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro index member
      have indexBound : index ≤ degree - power := by simpa using Finset.mem_range.mp member
      rw [derivativeCoefficients]
      by_cases indexZero : index = 0
      · subst index
        simp [coeff_one, Nat.ne_of_gt differencePositive]
      have inductionResult := inductionHypothesis (degree - power) differenceSmaller index
        (by omega) indexBound
      linear_combination coeff index (factor ^ power) * inductionResult
    have derivativeIdentity :
        (degree : PowerSeries R) * (X * PowerSeries.derivative (R := R) (factor ^ power) * factor ^ (degree - power)) =
          (power : PowerSeries R) * (X * PowerSeries.derivative (R := R) (factor ^ degree)) := by
      rw [derivative_pow, derivative_pow]
      have exponent : power - 1 + (degree - power) = degree - 1 := by omega
      rw [← exponent, pow_add]
      ring
    have coefficientIdentity := congrArg (coeff (degree - power)) derivativeIdentity
    simp only [← map_natCast C, coeff_C_mul, derivativeCoefficients] at coefficientIdentity
    have nonzero : (degree - power : ℕ) ≠ 0 := by omega
    have hunit : IsUnit (((degree - power : ℕ) : R)) := by
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr nonzero : ((degree-power : ℕ) : ℚ) ≠ 0)).map
          (algebraMap ℚ R)
    apply hunit.mul_left_cancel
    linear_combination (degree : R) * weighted + coefficientIdentity


theorem lagrange_burmann (A g F : PowerSeries R) (h0 : constantCoeff A = 0)
    (heq : A = X * F.subst A) (n : ℕ) :
    (n+1 : R) * coeff (n+1) (g.subst A) =
      coeff n (derivative (R := R) g * F^(n+1)) := by
  rw [coeff_subst' (.of_constantCoeff_zero h0)]
  simp only [smul_eq_mul]
  have hs : (∑ᶠ k : ℕ, coeff k g * coeff (n+1) (A^k)) =
      ∑ k ∈ range (n+2), coeff k g * coeff (n+1) (A^k) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra! hn
    have hlt : n+1 < k := by
      have hh : n+2 ≤ k := by simpa using hn
      omega
    have hz := coeff_of_lt_order (n+1)
      ((show ((n+1 : ℕ) : ENat) < (k : ENat) by exact_mod_cast hlt).trans_le
        (le_order_pow_of_constantCoeff_eq_zero k h0))
    exact hk (by simp [hz])
  rw [hs, sum_range_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (derivative (R := R) g) * coeff j (F^(n+1)))]
  simp only [pow_zero, coeff_one, Nat.succ_ne_zero, ite_false, mul_zero, add_zero, mul_sum]
  apply sum_congr rfl
  intro i hi
  have h := lagrange_power_coefficient A F h0 heq (n+1) (i+1)
    (by omega) (by simpa using hi)
  rw [Nat.add_sub_add_right] at h
  simp only [Nat.cast_succ] at h
  rw [coeff_derivative]
  linear_combination coeff (i+1) g * h

end
end D5.S3.Combinatorics.WeightedBond
