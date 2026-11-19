/- GID: D5/S1/Recurrence/Witt/EulerExponentialCoefficients
   generality: G
   mirror-B: D5/B/S1/Recurrence/Witt/EulerExponentialCoefficients
   mirror-E: none(waiver:formal-coefficient-recurrence)
   anchors: []
   utility: none
   digest: Positive increasing ghosts give positive nondecreasing coefficients of the actual formal exponential. -/

/- admission_basis: escape-witness. Proposed content: coefficient_monotone
compares adjacent convolution equations, using the actual ghost differences
and positive previously derived coefficients. All domains are unbounded;
utility none, with no checker, finite instance or numerical reduction. -/

import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

noncomputable section

namespace D5.S1.Recurrence.Witt.EulerExponentialCoefficients

open PowerSeries Finset
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

/-- The coefficient recurrence, with exactly the positive input indices. -/
theorem coefficient_recurrence (g : ℕ → ℚ) (n : ℕ) :
    (n : ℚ) * coeff n (exponentialSum g) =
      ∑ k ∈ range n, g (k + 1) * coeff (n - (k + 1)) (exponentialSum g) := by
  cases n with
  | zero => simp
  | succ n =>
    have hstep : D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step g 0 =
        mk (fun n => if n = 0 then 0 else g n) := by
      change mk (fun n => if n = 0 then 0 else g n -
        coeff n ((X * derivative (R := ℚ) 0) * 0 * invOfUnit (1 - C (n : ℚ) * 0) 1)) = _
      simp only [mul_zero, zero_mul, map_zero, sub_zero]
    have h := congrArg (coeff (n + 1)) (exponential_sum_equation g)
    rw [hstep, coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ'] at h
    simp only [coeff_mk, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ite_false, ite_true, zero_mul, add_zero, Nat.sub_zero] at h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_add_right, mul_comm] using h

/-- Positive ghost coefficients force every actual exponential coefficient to
be positive, including its constant coefficient. -/
theorem coefficient_positive (g : ℕ → ℚ) (hg : ∀ n, 0 < n → 0 < g n) :
    ∀ n, 0 < coeff n (exponentialSum g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simpa only [coeff_zero_eq_constantCoeff, exponential_sum_constant] using
        (zero_lt_one : (0 : ℚ) < 1)
    | succ n =>
      have hrec := coefficient_recurrence g (n + 1)
      have hsum : 0 < ∑ k ∈ range (n + 1),
          g (k + 1) * coeff (n + 1 - (k + 1)) (exponentialSum g) := by
        apply Finset.sum_pos'
        · intro k hk
          have hk' := mem_range.mp hk
          exact (mul_pos (hg (k + 1) (by omega))
            (ih (n + 1 - (k + 1)) (by omega))).le
        · refine ⟨n, mem_range.mpr (by omega), ?_⟩
          simpa only [Nat.sub_self, coeff_zero_eq_constantCoeff,
            exponential_sum_constant, mul_one] using hg (n + 1) (by omega)
      have hnQ : (0 : ℚ) < n + 1 := by positivity
      nlinarith

/-- Adjacent convolution equations transfer increasing ghosts to increasing
coefficients; no partition-count definition is used. -/
theorem coefficient_monotone (g : ℕ → ℚ)
    (hg : ∀ n, 0 < n → 0 < g n) (h1 : 1 ≤ g 1)
    (hinc : ∀ n, 0 < n → g n ≤ g (n + 1)) :
    Monotone (fun n => coeff n (exponentialSum g)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hc := coefficient_recurrence g n
  have hn := coefficient_recurrence g (n + 1)
  rw [sum_range_succ'] at hn
  have hsum : (∑ k ∈ range n,
      g (k + 1) * coeff (n - (k + 1)) (exponentialSum g)) ≤
      ∑ k ∈ range n,
        g (k + 1 + 1) * coeff (n + 1 - (k + 1 + 1)) (exponentialSum g) := by
    apply sum_le_sum
    intro k hk
    rw [show n + 1 - (k + 1 + 1) = n - (k + 1) by omega]
    exact mul_le_mul_of_nonneg_right (hinc (k + 1) (by omega))
      (coefficient_positive g hg _).le
  have hbase : coeff n (exponentialSum g) ≤ g 1 * coeff n (exponentialSum g) := by
    nlinarith [coefficient_positive g hg n]
  simp only [zero_add, Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one] at hn
  have hnQ : (0 : ℚ) < n + 1 := by positivity
  nlinarith

end D5.S1.Recurrence.Witt.EulerExponentialCoefficients
