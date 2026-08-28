/- GID: D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Defines prime code length and proves global additivity, including n = 1. -/
/- Library-search audit trail (2026-08-25): repository search found the exact Euler baseline
   bridge `log_partitionFunction_eq_tsum_prime`, the zeta mass identity `log_zeta_real`,
   `primeEvidence_summable`, and `factorization_log_length_eq_log`; all are reused. Pinned
   mathlib supplied `Real.log_nat_eq_sum_factorization`, `Real.log_prod`, `Real.rpow` bounds,
   `tsum_subtype`, and `Finsupp.sum`. No declaration combined these into pointwise global code
   additivity. The complex prime-log summability result was inspected but was not needed. -/

import D5.S3.Analytic.Zeta.EulerLogBridge
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
import D5.S3.Factorization.LogarithmicLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.GlobalCodeLengthAdditivity

open scoped BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.EulerLogBridge
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Factorization.LogarithmicLength

noncomputable section

/-- The surprisal of exponent `k` in the geometric coordinate at prime `p`. -/
def primeCodeLength (p : Nat.Primes) (s : Real) (k : Nat) : Real :=
  -Real.log (1 - primeEvidence s p) + s * k * Real.log p.1

private lemma prime_code_baseline_nonneg (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    0 <= -Real.log (1 - primeEvidence s p) := by
  have hq0 : 0 < primeEvidence s p := primeEvidence_pos s p
  have hq1 : primeEvidence s p < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith)
  exact neg_nonneg.mpr
    (Real.log_nonpos (sub_pos.mpr hq1).le (sub_le_self 1 hq0.le))

private lemma summable_prime_code_baseline (s : Real) (hs : 1 < s) :
    Summable (fun p : Nat.Primes => -Real.log (1 - primeEvidence s p)) := by
  apply Summable.of_nonneg_of_le
    (prime_code_baseline_nonneg s hs) (fun p => ?_) ((primeEvidence_summable s hs).mul_left 2)
  have hpR : 1 < (p.1 : Real) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < primeEvidence s p := primeEvidence_pos s p
  have hq1 : primeEvidence s p < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hqhalf : primeEvidence s p <= (2 : Real)⁻¹ := by
    calc
      primeEvidence s p <= (p.1 : Real) ^ (-1 : Real) := by
        exact Real.rpow_le_rpow_of_exponent_le hpR.le (by linarith)
      _ = (p.1 : Real)⁻¹ := Real.rpow_neg_one _
      _ <= (2 : Real)⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast p.2.two_le)
  have ha : 0 < 1 - primeEvidence s p := sub_pos.mpr hq1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
  rw [Real.log_inv] at hlog
  calc
    -Real.log (1 - primeEvidence s p) <=
        (1 - primeEvidence s p)⁻¹ - 1 := hlog
    _ = primeEvidence s p / (1 - primeEvidence s p) := by
      field_simp [ha.ne']
      ring
    _ <= 2 * primeEvidence s p := by
      rw [div_le_iff₀ ha]
      nlinarith

private lemma tsum_prime_factorization_log (n : Nat) :
    ∑' p : Nat.Primes, (n.factorization p.1 : Real) * Real.log p.1 = Real.log n := by
  rw [← factorization_log_length_eq_log n, factorizationLogLength]
  change (∑' p : ↑({p : Nat | p.Prime} : Set Nat),
    (n.factorization p.1 : Real) * Real.log p.1) = n.factorization.sum _
  have hsub := tsum_subtype ({p : Nat | p.Prime} : Set Nat)
    (fun p => (n.factorization p : Real) * Real.log p)
  rw [hsub]
  rw [tsum_eq_sum (s := n.factorization.support)]
  · rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by
      simpa [Nat.support_factorization] using hp)
    simp [Set.indicator, hprime]
  · intro p hp
    have hz : n.factorization p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    by_cases hprime : p.Prime
    · simp [Set.indicator, hprime, hz]
    · simp [Set.indicator, hprime]

/-- The negative log mass of a positive zeta sample is the sum of all prime-coordinate
code lengths. The Euler baseline uses the prime product; the occupied term uses unique
factorization. -/
theorem global_code_length_additive (s : Real) (hs : 1 < s) (n : Nat) (hn : 0 < n) :
    -Real.log (pmfReal (zetaDist s hs) n) =
      ∑' p : Nat.Primes, primeCodeLength p s (n.factorization p.1) := by
  have hbaseline := summable_prime_code_baseline s hs
  have hfactorNat : Summable (fun p : Nat =>
      (n.factorization p : Real) * Real.log p) := by
    apply summable_of_ne_finset_zero (s := n.factorization.support)
    intro p hp
    have hz : n.factorization p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    simp [hz]
  have hfactor : Summable (fun p : Nat.Primes =>
      (n.factorization p.1 : Real) * Real.log p.1) :=
    hfactorNat.comp_injective Subtype.coe_injective
  have hpartition :
      Real.log (partitionFunction s).toReal =
        ∑' p : Nat.Primes, -Real.log (1 - primeEvidence s p) := by
    simpa [primeEvidence] using log_partitionFunction_eq_tsum_prime s hs
  calc
    -Real.log (pmfReal (zetaDist s hs) n) =
        Real.log (partitionFunction s).toReal + s * Real.log n := by
      rw [log_zeta_real s hs hn]
      ring
    _ = (∑' p : Nat.Primes, -Real.log (1 - primeEvidence s p)) +
        s * (∑' p : Nat.Primes,
          (n.factorization p.1 : Real) * Real.log p.1) := by
      rw [hpartition, tsum_prime_factorization_log]
    _ = ∑' p : Nat.Primes,
        (-Real.log (1 - primeEvidence s p) +
          s * ((n.factorization p.1 : Real) * Real.log p.1)) := by
      rw [← hfactor.tsum_mul_left s, hbaseline.tsum_add (hfactor.mul_left s)]
    _ = ∑' p : Nat.Primes, primeCodeLength p s (n.factorization p.1) := by
      apply tsum_congr
      intro p
      simp only [primeCodeLength]
      ring

#print axioms global_code_length_additive

/-- The positivity restriction on the sampled natural is necessary: the totalized logarithm
at zero is zero, while the prime-coordinate baseline has a strictly positive sum. -/
theorem positive_sample_is_necessary :
    -Real.log (pmfReal (zetaDist 2 (by norm_num)) 0) ≠
      ∑' p : Nat.Primes, primeCodeLength p 2 ((0 : Nat).factorization p.1) := by
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hleft : -Real.log (pmfReal (zetaDist 2 (by norm_num)) 0) = 0 := by
    rw [zeta_real_apply]
    norm_num [Real.zero_rpow]
  have hpositive : 0 < -Real.log (1 - primeEvidence 2 twoPrime) := by
    rw [show primeEvidence 2 twoPrime = (1 / 4 : Real) by
      exact primeEvidence_two_at_two]
    exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have hbaselinePositive :
      0 < ∑' p : Nat.Primes, -Real.log (1 - primeEvidence 2 p) := by
    exact (summable_prime_code_baseline 2 (by norm_num)).tsum_pos
      (prime_code_baseline_nonneg 2 (by norm_num)) twoPrime hpositive
  have hright :
      0 < ∑' p : Nat.Primes, primeCodeLength p 2 ((0 : Nat).factorization p.1) := by
    simpa [primeCodeLength, Nat.factorization_zero] using hbaselinePositive
  rw [hleft]
  exact ne_of_lt hright

#print axioms positive_sample_is_necessary

/- Degeneracy audit: there are no variable types or map parameters, so empty/singleton types
and constant/identity/zero maps are inapplicable. The three intended positive inputs compile. -/
example (s : Real) (hs : 1 < s) :
    (∑' p : Nat.Primes, primeCodeLength p s ((1 : Nat).factorization p.1)) =
      Real.log (partitionFunction s).toReal := by
  rw [← global_code_length_additive s hs 1 (by norm_num)]
  rw [log_zeta_real s hs (by norm_num)]
  simp

example (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    (∑' q : Nat.Primes, primeCodeLength q s (p.1.factorization q.1)) =
      Real.log (partitionFunction s).toReal + s * Real.log p.1 := by
  rw [← global_code_length_additive s hs p.1 p.2.pos]
  rw [log_zeta_real s hs p.2.pos]
  ring

example (s : Real) (hs : 1 < s) (p : Nat.Primes) (k : Nat) :
    (∑' q : Nat.Primes, primeCodeLength q s ((p.1 ^ k).factorization q.1)) =
      Real.log (partitionFunction s).toReal + s * k * Real.log p.1 := by
  have hpk : 0 < p.1 ^ k := pow_pos p.2.pos k
  rw [← global_code_length_additive s hs (p.1 ^ k) hpk]
  rw [log_zeta_real s hs hpk, Nat.cast_pow, Real.log_pow]
  ring

end

end D5.S3.Analytic.ZetaObservation.GlobalCodeLengthAdditivity
