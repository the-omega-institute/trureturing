/- GID: D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenSubstitutionOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves that the hidden product nS is nonzero and preserves the prime radical, extends radical invariance and the frozen contraction bound along every nS orbit, and bounds the accumulated logarithmic displacement by a geometric golden-ratio envelope. -/

import D5.S1.Deficit.Displacement.GoldenContractionRadicalBound

open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenContractionRadicalBound
open GoldenDesubstitutionClosedForms
open GoldenDesubstitutionLength

namespace GoldenSubstitutionOrbit

/-- The substituted hidden product is always nonzero, including at zero. -/
theorem nS_ne_zero (n : ℕ) : nS n ≠ 0 := by
  rw [nS, Finsupp.prod]
  exact Nat.ne_of_gt (Finset.prod_pos fun p hp ↦
    pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors (by
      simpa only [Nat.support_factorization] using hp))) _)

/-- Golden substitution of the prime exponents preserves the set of prime divisors. -/
theorem primeRadical_nS (n : ℕ) : primeRadical (nS n) = primeRadical n := by
  have hprimeFactors : (nS n).primeFactors = n.primeFactors := by
    calc
      (nS n).primeFactors = (nS n).factorization.support := by
        rw [Nat.support_factorization]
      _ = (Finsupp.mapRange goldenSubstStart goldenSubstStart_zero
          n.factorization).support := by
        rw [nS_factorization]
      _ = n.factorization.support :=
        Finsupp.support_mapRange_of_injective goldenSubstStart_zero n.factorization
          goldenSubstStart_strictMono.injective
      _ = n.primeFactors := by rw [Nat.support_factorization]
  unfold primeRadical
  rw [hprimeFactors]

/-- Every iterate of the hidden product preserves the original prime radical. -/
theorem primeRadical_nS_iterate (k n : ℕ) :
    primeRadical (nS^[k] n) = primeRadical n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', primeRadical_nS, ih]

private theorem nS_iterate_ne_zero {n : ℕ} (hn : n ≠ 0) (k : ℕ) : nS^[k] n ≠ 0 := by
  induction k with
  | zero => simpa using hn
  | succ k _ =>
      rw [Function.iterate_succ_apply']
      exact nS_ne_zero _

private theorem log_primeRadical_nonneg (n : ℕ) :
    0 ≤ Real.log (primeRadical n) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ primeRadical n by
    rw [primeRadical]
    apply Finset.one_le_prod
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).one_le)

private theorem goldenRatio_sub_inv_goldenRatio :
    Real.goldenRatio - Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  change (1 + Real.sqrt 5) / 2 - -((1 - Real.sqrt 5) / 2) = 1
  nlinarith [Real.goldenRatio_sq]

/-- The contraction error at every point of an `nS` orbit obeys the single radical bound of its
starting point. -/
theorem abs_lambdaMinus_nS_iterate_le {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    |lambdaMinus (nS^[k] n)| ≤
      Real.goldenRatio⁻¹ * Real.log (primeRadical n) := by
  calc
    |lambdaMinus (nS^[k] n)| ≤
        Real.goldenRatio⁻¹ * Real.log (primeRadical (nS^[k] n)) :=
      abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical (nS_iterate_ne_zero hn k)
    _ = Real.goldenRatio⁻¹ * Real.log (primeRadical n) := by
      rw [primeRadical_nS_iterate]

/-- The accumulated logarithmic displacement after `k` substitutions is bounded by the geometric
golden-ratio envelope with the original prime radical held fixed. -/
theorem abs_log_nS_iterate_sub_goldenRatio_pow_mul_log_le {n : ℕ} (hn : n ≠ 0)
    (k : ℕ) :
    |Real.log (nS^[k] n) - Real.goldenRatio ^ k * Real.log n| ≤
      (Real.goldenRatio ^ k - 1) * Real.log (primeRadical n) := by
  let L := Real.log (primeRadical n)
  have hL : 0 ≤ L := by
    simpa [L] using log_primeRadical_nonneg n
  induction k with
  | zero =>
      have hz : 0 ≤ (Real.goldenRatio ^ 0 - 1) * L :=
        mul_nonneg (by simp) hL
      simp [L] at hz ⊢
  | succ k ih =>
      have hnonzero : nS^[k] n ≠ 0 := nS_iterate_ne_zero hn k
      have hdecomp :
          Real.log (nS^[k + 1] n) - Real.goldenRatio ^ (k + 1) * Real.log n =
            lambdaMinus (nS^[k] n) + Real.goldenRatio *
              (Real.log (nS^[k] n) - Real.goldenRatio ^ k * Real.log n) := by
        rw [Function.iterate_succ_apply',
          lambdaMinus_eq_log_nS_sub_goldenRatio_log _ hnonzero, pow_succ']
        ring
      have hcoefficient :
          Real.goldenRatio⁻¹ + Real.goldenRatio * (Real.goldenRatio ^ k - 1) =
            Real.goldenRatio ^ (k + 1) - 1 := by
        calc
          Real.goldenRatio⁻¹ + Real.goldenRatio * (Real.goldenRatio ^ k - 1) =
              Real.goldenRatio * Real.goldenRatio ^ k +
                (Real.goldenRatio⁻¹ - Real.goldenRatio) := by ring
          _ = Real.goldenRatio * Real.goldenRatio ^ k - 1 := by
            rw [show Real.goldenRatio⁻¹ - Real.goldenRatio = -1 by
              linarith [goldenRatio_sub_inv_goldenRatio]]
            ring
          _ = Real.goldenRatio ^ (k + 1) - 1 := by rw [pow_succ']
      rw [hdecomp]
      calc
        |lambdaMinus (nS^[k] n) + Real.goldenRatio *
            (Real.log (nS^[k] n) - Real.goldenRatio ^ k * Real.log n)| ≤
            |lambdaMinus (nS^[k] n)| +
              |Real.goldenRatio *
                (Real.log (nS^[k] n) - Real.goldenRatio ^ k * Real.log n)| :=
          abs_add_le _ _
        _ = |lambdaMinus (nS^[k] n)| + Real.goldenRatio *
              |Real.log (nS^[k] n) - Real.goldenRatio ^ k * Real.log n| := by
          rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
        _ ≤ Real.goldenRatio⁻¹ * L +
              Real.goldenRatio * ((Real.goldenRatio ^ k - 1) * L) := by
          exact add_le_add (by
            simpa [L] using abs_lambdaMinus_nS_iterate_le hn k)
            (mul_le_mul_of_nonneg_left ih Real.goldenRatio_pos.le)
        _ = (Real.goldenRatio ^ (k + 1) - 1) * L := by
          calc
            Real.goldenRatio⁻¹ * L +
                Real.goldenRatio * ((Real.goldenRatio ^ k - 1) * L) =
              (Real.goldenRatio⁻¹ +
                Real.goldenRatio * (Real.goldenRatio ^ k - 1)) * L := by ring
            _ = (Real.goldenRatio ^ (k + 1) - 1) * L := by rw [hcoefficient]

example : primeRadical (nS^[3] 12) = primeRadical 12 := by
  exact primeRadical_nS_iterate 3 12

end GoldenSubstitutionOrbit
