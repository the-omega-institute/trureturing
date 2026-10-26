/- GID: D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: The literal rational formal series for all actual trapezohedral minimal connected dominating subsets. -/

import D5.S3.Combinatorics.Graph.Domination.TrapezohedralPathEquivalence
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-! All identities are in rational formal power series; the denominator is a unit.
The zero coefficients at orders zero, one and two are included in actualCount. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TrapezohedralDominationSeries

open PowerSeries
open TrapezohedralMinimalDomination TrapezohedralPathEquivalence
open PathMaximalIndependentCount PathEndpointCount

private noncomputable def F : PowerSeries ℚ := mk (fun n => (count n : ℚ))
private noncomputable def R : PowerSeries ℚ := mk (fun n => (restrictedCount n : ℚ))

private theorem F_identity : F * (1 - X^2 - X^3) = 1 + X + X^2 := by
  ext n
  rw [mul_sub, mul_sub, mul_one]
  simp only [map_sub, map_add, coeff_mul_X_pow', F, coeff_mk]
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [coeff_X, count_initial.1, count_initial.2.1, count_initial.2.2]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have h := count_recurrence k
    have hc : (count (k + 3) : ℚ) = count (k + 1) + count k := by exact_mod_cast h
    simp only [show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega, ↓reduceIte]
    have h2 : k + 3 - 2 = k + 1 := by omega
    have h3 : k + 3 - 3 = k := by omega
    rw [h2, h3, hc]
    simp [coeff_one, coeff_X, coeff_X_pow, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega]

private theorem R_from_F :
    R = (1 - X^4) * F - 1 - X - 2 * X^2 - X^3 := by
  ext n
  rw [sub_mul, one_mul]
  simp only [map_sub, coeff_X_pow_mul', R, F, coeff_mk]
  by_cases hn : n < 4
  · have h3 := count_recurrence 0
    have hc3 : count 3 = 2 := by simpa [count_initial.1, count_initial.2.1] using h3
    interval_cases n <;>
      norm_num [coeff_X, restricted_initial.1, restricted_initial.2.1,
        restricted_initial.2.2.1, restricted_initial.2.2.2,
        count_initial.1, count_initial.2.1, count_initial.2.2, hc3] at *
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h := restricted_complement k
    have hc : (restrictedCount (k + 4) : ℚ) + count k = count (k + 4) := by
      exact_mod_cast h
    simp only [show 4 ≤ k + 4 by omega, ↓reduceIte, Nat.add_sub_cancel]
    have hz1 : k + 4 ≠ 1 := by omega
    have hz2 : k + 4 ≠ 2 := by omega
    have hz3 : k + 4 ≠ 3 := by omega
    simp [coeff_one, coeff_X, coeff_X_pow, hz1, hz2, hz3]
    linarith

private theorem R_identity : R * (1 - X^2 - X^3) = X^3 + 2*X^4 + 2*X^5 := by
  rw [R_from_F]
  linear_combination (1 - X^4) * F_identity

/-- The actual labelled-subset generating series, including the complete zero prefix. -/
noncomputable def actualSeries : PowerSeries ℚ := mk (fun n => (actualCount n : ℚ))

private theorem series_derivative : actualSeries = 2 * X * (PowerSeries.derivative (R := ℚ)) R := by
  ext n
  cases n with
  | zero => simp [actualSeries, actual_count, mul_assoc, coeff_zero_X_mul, restricted_initial.1]
  | succ n =>
    rw [mul_assoc]
    simp only [coeff_ofNat_mul, coeff_succ_X_mul, coeff_derivative,
      R, coeff_mk, actualSeries]
    rw [actual_count]
    push_cast
    ring

/-- The complete original all-n series, with the original polynomial and squared denominator. -/
theorem actual_series :
    actualSeries =
      -2 * X^3 * (4*X^5 + 8*X^4 + 4*X^3 - 9*X^2 - 8*X - 3) *
        ((X^3 + X^2 - 1)^2)⁻¹ := by
  have hd := congrArg ((PowerSeries.derivative (R := ℚ))) R_identity
  simp only [map_sub, map_add,
    Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    derivative_one, mul_one, smul_eq_mul] at hd
  have hd2 : (PowerSeries.derivative (R := ℚ)) (2 : PowerSeries ℚ) = 0 :=
    (PowerSeries.derivative (R := ℚ)).map_natCast 2
  rw [hd2] at hd
  have hproduct : (2 * X * (PowerSeries.derivative (R := ℚ)) R) * (X^3 + X^2 - 1)^2 =
      -2 * X^3 * (4*X^5 + 8*X^4 + 4*X^3 - 9*X^2 - 8*X - 3) := by
    linear_combination 2 * X * (1 - X^2 - X^3) * hd +
      (4*X^2 + 6*X^3) * R_identity
  have hu : constantCoeff ((X^3 + X^2 - 1 : PowerSeries ℚ)^2) ≠ 0 := by simp
  have hinv := PowerSeries.mul_inv_cancel ((X^3 + X^2 - 1 : PowerSeries ℚ)^2) hu
  rw [series_derivative, ← hproduct,
    mul_assoc (2 * X * (PowerSeries.derivative (R := ℚ)) R) _ _, hinv, mul_one]

end D5.S3.Combinatorics.Graph.Domination.TrapezohedralDominationSeries
