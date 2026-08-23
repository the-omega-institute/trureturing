/- GID: D5/S3/Analytic/ZetaMinEntropy/PrimeDecomposition
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta law's min-entropy decomposes into summable prime-coordinate min-entropies. -/

import D5.S3.Analytic.Zeta.EulerLogBridge
import D5.S3.Analytic.Zeta.ZetaMinEntropy

/- Provenance: Native proof over pinned mathlib.

Search receipt (2026-08-23): `countableMinEntropy` was searched throughout `D5` and pinned
Mathlib. The only repository occurrences were its definition, the zeta closed form, and the
infinite-order Renyi limit in `ZetaMinEntropy.lean`; no prime-coordinate min-entropy statement
exists. The public `primeExponentPMF_apply`, `primeExponent_entropy_eq`,
`summable_primeExponent_entropy`, `log_partitionFunction_eq_tsum_prime`, and
`zeta_min_entropy_eq` declarations supply the local mass formula, the Shannon majorant, and the
two sides of the decomposition. Pinned Mathlib supplies `ciSup_le`, `le_ciSup`, and
`Summable.of_nonneg_of_le`; its complex-valued
`summable_neg_log_one_sub_mul_prime_cpow` was inspected but is not needed. The private
`zeta_iSup_pmfReal` and `summable_prime_eulerLog` declarations were read for comparison and are
not imported or used. -/

namespace D5.S3.Analytic.ZetaMinEntropy.PrimeDecomposition

open scoped BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.EulerLogBridge
open D5.S3.Analytic.Zeta.ZetaMinEntropy

noncomputable section

private lemma primeExponent_mass_le_zero_mass (s : ℝ) (hs : 1 < s) (p : Nat.Primes)
    (k : ℕ) :
    pmfReal (primeExponentPMF s hs p) k ≤ pmfReal (primeExponentPMF s hs p) 0 := by
  rw [primeExponentPMF_apply, primeExponentPMF_apply]
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.rpow_zero, mul_one]
  have hp1 : 1 ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le
  have hk0 : -(k : ℝ) * s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) hs0
  have hpow : (p.1 : ℝ) ^ (-(k : ℝ) * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 hk0
  have hcoefficient : 0 ≤ 1 - (p.1 : ℝ) ^ (-s) := by
    exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hcoefficient

private lemma primeExponent_iSup_pmfReal (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    (⨆ k, pmfReal (primeExponentPMF s hs p) k) =
      pmfReal (primeExponentPMF s hs p) 0 := by
  have hbdd : BddAbove (Set.range (pmfReal (primeExponentPMF s hs p))) := by
    refine ⟨pmfReal (primeExponentPMF s hs p) 0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact primeExponent_mass_le_zero_mass s hs p k
  apply le_antisymm
  · exact ciSup_le (primeExponent_mass_le_zero_mass s hs p)
  · exact le_ciSup hbdd 0

/-- A prime-exponent marginal has min-entropy equal to its Euler-log contribution. -/
theorem primeExponent_min_entropy_eq (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    countableMinEntropy (primeExponentPMF s hs p) =
      -Real.log (1 - (p.1 : ℝ) ^ (-s)) := by
  rw [countableMinEntropy, primeExponent_iSup_pmfReal, primeExponentPMF_apply]
  simp

/-- The family of prime-coordinate min-entropies is summable. -/
theorem summable_primeExponent_minEntropy (s : ℝ) (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ countableMinEntropy (primeExponentPMF s hs p)) := by
  apply Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    (summable_primeExponent_entropy s hs)
  · rw [primeExponent_min_entropy_eq]
    have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 < (p.1 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
    have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    exact neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr hq1).le (sub_le_self 1 hq0.le))
  · rw [primeExponent_min_entropy_eq, primeExponent_entropy_eq]
    have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 < (p.1 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
    have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by linarith) (Real.log_pos hpR).le)
        (div_nonneg hq0.le (sub_pos.mpr hq1).le))

/-- The zeta law's min-entropy is the sum of its prime-coordinate min-entropies. -/
theorem countableMinEntropy_zeta_eq_tsum_prime (s : ℝ) (hs : 1 < s) :
    countableMinEntropy (zetaDist s hs) =
      ∑' p : Nat.Primes, countableMinEntropy (primeExponentPMF s hs p) := by
  have hpartition := congrArg Complex.re (partition_function_toReal_eq_riemannZeta s hs)
  simp only [Complex.ofReal_re] at hpartition
  rw [zeta_min_entropy_eq s hs, ← hpartition, log_partitionFunction_eq_tsum_prime s hs]
  apply tsum_congr
  intro p
  rw [primeExponent_min_entropy_eq]

end

end D5.S3.Analytic.ZetaMinEntropy.PrimeDecomposition
