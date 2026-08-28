/- GID: D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation
   generality: G
   mirror-B: D5/B/S0/Observation/PowerTraceCharacteristicPolynomialSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cayley-Hamilton fixes higher power traces from bounded initial data. -/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/- Library-search audit trail (2026-08-26):
   * Repository searches for `charpoly.*trace`, `powerTrace`,
     `aeval_self_charpoly`, and the coefficient-trace recurrence found no
     existing theorem with the source's matrix recurrence, trace recurrence,
     and all-higher-traces clause. The adjacent bounded integer recovery and
     nilpotent countermodel modules have different carriers and conclusions.
   * Pinned Mathlib's exact Cayley-Hamilton primitive is
     `Matrix.aeval_self_charpoly`; `Polynomial.aeval_eq_sum_range`, matrix
     trace linearity, and characteristic-polynomial monicity supply the
     standard steps below. No Mathlib theorem packages the full statement.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation

open Polynomial

/-- Cayley-Hamilton gives a dimension-bounded recurrence for matrix powers and
their traces. Consequently, among matrices with the same characteristic
polynomial, agreement on the first `n` positive-power traces forces agreement
on every positive-power trace. -/
theorem power_trace_characteristic_polynomial_saturation
    {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    (A ^ n =
        -∑ k ∈ Finset.range n, A.charpoly.coeff k • A ^ k) ∧
      (∀ m : ℕ,
        Matrix.trace (A ^ (n + m)) =
          -∑ k ∈ Finset.range n,
            A.charpoly.coeff k * Matrix.trace (A ^ (k + m))) ∧
      ∀ B : Matrix (Fin n) (Fin n) K,
        B.charpoly = A.charpoly →
        (∀ k < n,
          Matrix.trace (A ^ (k + 1)) = Matrix.trace (B ^ (k + 1))) →
        ∀ r : ℕ,
          Matrix.trace (A ^ (r + 1)) = Matrix.trace (B ^ (r + 1)) := by
  have matrixRecurrence (M : Matrix (Fin n) (Fin n) K) :
      M ^ n = -∑ k ∈ Finset.range n, M.charpoly.coeff k • M ^ k := by
    have hLeading : M.charpoly.coeff n = 1 := by
      simpa [Matrix.charpoly_natDegree_eq_dim] using
        M.charpoly_monic.coeff_natDegree
    have hCayley :
        (∑ k ∈ Finset.range n, M.charpoly.coeff k • M ^ k) + M ^ n = 0 := by
      simpa [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
        Finset.sum_range_succ, hLeading] using
        Matrix.aeval_self_charpoly M
    exact eq_neg_of_add_eq_zero_right hCayley
  have traceRecurrence (M : Matrix (Fin n) (Fin n) K) (m : ℕ) :
      Matrix.trace (M ^ (n + m)) =
        -∑ k ∈ Finset.range n,
          M.charpoly.coeff k * Matrix.trace (M ^ (k + m)) := by
    have hPower :
        M ^ (n + m) =
          -∑ k ∈ Finset.range n, M.charpoly.coeff k • M ^ (k + m) := by
      calc
        M ^ (n + m) = M ^ n * M ^ m := pow_add M n m
        _ = (-∑ k ∈ Finset.range n, M.charpoly.coeff k • M ^ k) * M ^ m := by
          rw [matrixRecurrence M]
        _ = -∑ k ∈ Finset.range n, M.charpoly.coeff k • M ^ (k + m) := by
          simp [Finset.sum_mul, pow_add]
    rw [hPower]
    simp
  refine ⟨matrixRecurrence A, traceRecurrence A, ?_⟩
  intro B hCharpoly hInitial r
  have hAll : ∀ e : ℕ, Matrix.trace (A ^ e) = Matrix.trace (B ^ e) := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
        by_cases heZero : e = 0
        · subst e
          simp
        by_cases heSmall : e ≤ n
        · have hePositive : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr heZero
          simpa [Nat.sub_add_cancel hePositive] using
            hInitial (e - 1) (by omega)
        · have hnlt : n < e := Nat.lt_of_not_ge heSmall
          let m := e - n
          have hmPositive : 0 < m := Nat.sub_pos_of_lt hnlt
          have heq : n + m = e := by
            dsimp [m]
            omega
          rw [← heq, traceRecurrence A m, traceRecurrence B m, hCharpoly]
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih (k + m) (by
            have hklt : k < n := Finset.mem_range.mp hk
            omega)]
  exact hAll (r + 1)

#print axioms power_trace_characteristic_polynomial_saturation

end D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation
