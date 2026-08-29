/- GID: D5/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain
   generality: I
   mirror-B: D5/B/S3/Analytic/PrimeProducts/PrimePrecisionMarginalGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Truncated prime entropy gains q^k binEntropy q, with boundary audits. -/
/- Library-search audit trail (2026-08-25):
   * Exact D5 name searches found residual entropy contraction but no truncation gain theorem.
   * D5 body searches for mapped `Nat.min` laws and `q ^ k * binEntropy q` found no match.
   * Blueprint formula searches found no entropy statement for a truncated prime-exponent PMF.
   * Pinned Mathlib supplies `Real.binEntropy`, its continuity and maximum, and `PMF.map_apply`.
   * Lean core and the other pinned packages contain no packaged geometric truncation entropy law.
   The existing residual theorem has no public `H(T_k) + R_k = H(V)` bridge, so this proof
   computes the entropy of the actual pushforward law without reproving residual contraction. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.PrimeProducts.PrimePrecisionMarginalGain

open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open Filter MeasureTheory Set

/-- The depth-`precision` prime-exponent readout, merging all values at least `precision`. -/
def primeTruncatedReadout (precision value : Nat) : Nat :=
  min value precision

/-- The law of the depth-`precision` readout of the canonical prime-exponent channel. -/
def primeTruncatedReadoutLaw
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) : PMF Nat :=
  (primeExponentPMF s hs p).map (primeTruncatedReadout precision)

/-- The Shannon entropy in nats of the depth-`precision` prime-exponent readout. -/
def primeTruncatedReadoutEntropy
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) : Real :=
  countableEntropy (primeTruncatedReadoutLaw s hs p precision)

private theorem prime_truncated_readout_zero (value : Nat) :
    primeTruncatedReadout 0 value = 0 := by
  simp [primeTruncatedReadout]

private theorem prime_truncated_readout_of_le {precision value : Nat}
    (hvalue : value <= precision) :
    primeTruncatedReadout precision value = value := by
  simp [primeTruncatedReadout, hvalue]

private lemma primeExponentPMF_apply_power
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (value : Nat) :
    pmfReal (primeExponentPMF s hs p) value =
      (1 - primeEvidence s p) * primeEvidence s p ^ value := by
  rw [primeExponentPMF_apply]
  simp only [primeEvidence]
  congr 1
  rw [<- Real.rpow_natCast, <- Real.rpow_mul (by positivity)]
  congr 1
  ring

private lemma prime_tail_mass
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    ((primeExponentPMF s hs p).toMeasure (Set.Ici precision)).toReal =
      primeEvidence s p ^ precision := by
  rw [primeExponentPMF_eq_map]
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
  change ((zetaDist s hs).toMeasure
    {value : Nat | precision <= value.factorization p.1}).toReal = _
  rw [measure_factorization_ge s hs p.1 precision p.2]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]
  simp only [primeEvidence]
  rw [<- Real.rpow_natCast, <- Real.rpow_mul (by positivity)]
  congr 1
  ring

private lemma prime_truncated_mass_of_lt
    (s : Real) (hs : 1 < s) (p : Nat.Primes) {precision value : Nat}
    (hvalue : value < precision) :
    pmfReal (primeTruncatedReadoutLaw s hs p precision) value =
      (1 - primeEvidence s p) * primeEvidence s p ^ value := by
  rw [pmfReal, <- PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rw [primeTruncatedReadoutLaw,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
  have hpreimage :
      primeTruncatedReadout precision ⁻¹' ({value} : Set Nat) = {value} := by
    ext candidate
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hreadout
      simp only [primeTruncatedReadout] at hreadout
      omega
    · intro hcandidate
      subst candidate
      simp [primeTruncatedReadout, Nat.le_of_lt hvalue]
  rw [hpreimage, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  exact primeExponentPMF_apply_power s hs p value

private lemma prime_truncated_mass_at_precision
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    pmfReal (primeTruncatedReadoutLaw s hs p precision) precision =
      primeEvidence s p ^ precision := by
  rw [pmfReal, <- PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rw [primeTruncatedReadoutLaw,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
  have hpreimage :
      primeTruncatedReadout precision ⁻¹' ({precision} : Set Nat) = Set.Ici precision := by
    ext value
    simp [primeTruncatedReadout]
  rw [hpreimage]
  exact prime_tail_mass s hs p precision

private lemma prime_truncated_mass_of_lt_value
    (s : Real) (hs : 1 < s) (p : Nat.Primes) {precision value : Nat}
    (hprecision : precision < value) :
    pmfReal (primeTruncatedReadoutLaw s hs p precision) value = 0 := by
  rw [pmfReal, <- PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rw [primeTruncatedReadoutLaw,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
  have hpreimage :
      primeTruncatedReadout precision ⁻¹' ({value} : Set Nat) = ∅ := by
    ext candidate
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    change min candidate precision = value ↔ False
    constructor
    · exact fun h => (ne_of_lt
        ((Nat.min_le_right candidate precision).trans_lt hprecision)) h
    · exact False.elim
  rw [hpreimage, measure_empty, ENNReal.toReal_zero]

private lemma prime_truncated_entropy_formula
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    primeTruncatedReadoutEntropy s hs p precision =
      (∑ value ∈ Finset.range precision,
        Real.negMulLog
          ((1 - primeEvidence s p) * primeEvidence s p ^ value)) +
        Real.negMulLog (primeEvidence s p ^ precision) := by
  rw [primeTruncatedReadoutEntropy, countableEntropy]
  rw [tsum_eq_sum (s := Finset.range (precision + 1))]
  · rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro value hvalue
      rw [prime_truncated_mass_of_lt s hs p (Finset.mem_range.mp hvalue)]
    · rw [prime_truncated_mass_at_precision]
  · intro value hvalue
    rw [Finset.mem_range, not_lt] at hvalue
    rw [prime_truncated_mass_of_lt_value s hs p (by omega)]
    simp

/-- One added prime-exponent precision layer gains exactly `q ^ k * h_2(q)` nats. -/
theorem prime_precision_marginal_gain
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (k : Nat) :
    primeTruncatedReadoutEntropy s hs p (k + 1) -
        primeTruncatedReadoutEntropy s hs p k =
      primeEvidence s p ^ k * Real.binEntropy (primeEvidence s p) := by
  rw [prime_truncated_entropy_formula, prime_truncated_entropy_formula]
  rw [Finset.sum_range_succ, pow_succ]
  rw [Real.negMulLog_mul, Real.negMulLog_mul]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

#print axioms prime_precision_marginal_gain

/-- At depth zero, the first precision layer gains the full binary entropy. -/
theorem first_prime_precision_gain
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    primeTruncatedReadoutEntropy s hs p 1 -
        primeTruncatedReadoutEntropy s hs p 0 =
      Real.binEntropy (primeEvidence s p) := by
  simpa using prime_precision_marginal_gain s hs p 0

#print axioms first_prime_precision_gain

/-- Binary entropy tends to zero at both endpoints, hence also from inside `[0, 1]`. -/
theorem binary_entropy_boundary_limits :
    Tendsto Real.binEntropy (nhds 0) (nhds 0) ∧
      Tendsto Real.binEntropy (nhds 1) (nhds 0) := by
  constructor
  · have h :=
      (Real.binEntropy_continuous.continuousAt : ContinuousAt Real.binEntropy 0)
    change Tendsto Real.binEntropy (nhds 0) (nhds (Real.binEntropy 0)) at h
    simpa using h
  · have h :=
      (Real.binEntropy_continuous.continuousAt : ContinuousAt Real.binEntropy 1)
    change Tendsto Real.binEntropy (nhds 1) (nhds (Real.binEntropy 1)) at h
    simpa using h

#print axioms binary_entropy_boundary_limits

/-- Binary entropy takes its global maximum `log 2` exactly at one half. -/
theorem binary_entropy_half_maximum :
    Real.binEntropy (1 / 2 : Real) = Real.log 2 ∧
      ∀ q : Real, Real.binEntropy q ≤ Real.log 2 := by
  constructor
  · simp [one_div]
  · exact fun _ => Real.binEntropy_le_log_two

#print axioms binary_entropy_half_maximum

end D5.S3.Analytic.PrimeProducts.PrimePrecisionMarginalGain
