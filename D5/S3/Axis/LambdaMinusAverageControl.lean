/- GID: D5/S3/Axis/LambdaMinusAverageControl
   generality: I
   mirror-B: D5/B/S3/Axis/LambdaMinusAverageControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transfer the diagonal prime-axis average to the contraction-face summatory function. -/

import D5.S3.Axis.LambdaMinusDirichletSeries
import D5.S1.Deficit.Beatty.BetaBeattyClosedForms
import Mathlib.NumberTheory.PrimeCounting

/- Library-search audit trail (2026-08-31):
   * Current-tree name and body-shape searches found no public finite prime-axis
     summatory construction and no average theorem for `lambdaMinus`.
   * The frozen Dirichlet-series theorem is an exact component hit for the zeta
     factor, but it does not state finite summatory control or the leading scale.
   * Pinned Mathlib supplies `Nat.primesBelow`, finite-sum interchange, and the
     topology of sequence limits. It contains Chebyshev bounds but no prime-number
     or additive-function average theorem that proves the required limit directly.
   * No `loogle` or `leansearch` executable is available on this lane. -/

open scoped ArithmeticFunction LSeries BigOperators Topology
open Filter
open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.BetaBeattyClosedForms
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S3.Axis.LambdaMinusDirichletSeries

namespace D5.S3.Axis.LambdaMinusAverageControl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The diagonal prime-axis summatory function, assembled prime-first from the
contraction reading of each exponent occurring below the cutoff. -/
noncomputable def lambdaMinusPrimeAxisSummatory (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (x + 1),
    ∑ n ∈ Finset.range (x + 1),
      if p ∈ n.factorization.support then
        betaContraction (n.factorization p) * Real.log p
      else 0

/-- The zeta factor and the diagonal prime-axis decomposition together transport
the diagonal `x log x` average to the contraction-face summatory function. The
diagonal asymptotic is explicit because the pinned library does not yet supply the
needed prime-number average theorem. -/
theorem lambda_minus_average_diagonal_control
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (lambdaMinus n : ℂ)) s =
        riemannZeta s * lambdaMinusAxisSeries s ∧
      (∀ x : ℕ,
        (∑ n ∈ Finset.range (x + 1), lambdaMinus n) =
          lambdaMinusPrimeAxisSummatory x) ∧
      (Tendsto
          (fun x : ℕ => lambdaMinusPrimeAxisSummatory x /
            ((x : ℝ) * Real.log x))
          atTop (𝓝 (Real.goldenConj ^ 2)) →
        Tendsto
          (fun x : ℕ =>
            (∑ n ∈ Finset.range (x + 1), lambdaMinus n) /
              ((x : ℝ) * Real.log x))
          atTop (𝓝 (Real.goldenConj ^ 2))) ∧
      betaContraction 1 = Real.goldenConj ^ 2 := by
  have summatory_eq_prime_axis : ∀ x : ℕ,
      (∑ n ∈ Finset.range (x + 1), lambdaMinus n) =
        lambdaMinusPrimeAxisSummatory x := by
    intro x
    calc
      (∑ n ∈ Finset.range (x + 1), lambdaMinus n) =
          ∑ n ∈ Finset.range (x + 1),
            ∑ p ∈ Nat.primesBelow (x + 1),
              if p ∈ n.factorization.support then
                betaContraction (n.factorization p) * Real.log p
              else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [lambdaMinus]
        change (∑ p ∈ n.factorization.support,
            betaContraction (n.factorization p) * Real.log p) = _
        have hsubset : n.factorization.support ⊆ Nat.primesBelow (x + 1) := by
          intro p hp
          apply Nat.mem_primesBelow.mpr
          exact ⟨(Nat.le_of_mem_primeFactors hp).trans_lt (Finset.mem_range.mp hn),
            Nat.prime_of_mem_primeFactors hp⟩
        calc
          (∑ p ∈ n.factorization.support,
              betaContraction (n.factorization p) * Real.log p) =
              ∑ p ∈ n.factorization.support,
                if p ∈ n.factorization.support then
                  betaContraction (n.factorization p) * Real.log p
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  rw [if_pos hp]
          _ = _ := Finset.sum_subset hsubset (by
            intro p hp hnot
            rw [if_neg hnot])
      _ = lambdaMinusPrimeAxisSummatory x := by
        rw [lambdaMinusPrimeAxisSummatory, Finset.sum_comm]
  have average_transfer : Tendsto
        (fun x : ℕ => lambdaMinusPrimeAxisSummatory x /
          ((x : ℝ) * Real.log x))
        atTop (𝓝 (Real.goldenConj ^ 2)) →
      Tendsto
        (fun x : ℕ =>
          (∑ n ∈ Finset.range (x + 1), lambdaMinus n) /
            ((x : ℝ) * Real.log x))
        atTop (𝓝 (Real.goldenConj ^ 2)) := by
    intro hdiagonal
    simpa only [summatory_eq_prime_axis] using hdiagonal
  have beta_one : betaContraction 1 = Real.goldenConj ^ 2 := by
    rw [betaContraction_eq_displacement_sub_goldenRatio]
    have hdecode : displacementDecode 1 = 2 := by
      have hfloor : ⌊(((1 : ℕ) : ℝ) + 1) * Real.goldenRatio⌋ = 3 := by
        rw [Int.floor_eq_iff]
        constructor
        · norm_num
          nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
        · norm_num
          linarith [Real.goldenRatio_lt_two]
      have hdecodeInt := displacement_decode_eq_beatty_floor 1
      rw [hfloor] at hdecodeInt
      norm_num at hdecodeInt
      exact_mod_cast hdecodeInt
    rw [hdecode]
    norm_num
    linarith [Real.goldenRatio_add_goldenConj, Real.goldenConj_sq]
  exact ⟨(lambda_minus_dirichlet_series s hs).1,
    summatory_eq_prime_axis, average_transfer, beta_one⟩

#print axioms lambda_minus_average_diagonal_control

end D5.S3.Axis.LambdaMinusAverageControl
