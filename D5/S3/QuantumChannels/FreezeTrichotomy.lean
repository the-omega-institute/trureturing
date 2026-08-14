/- GID: D5/S3/QuantumChannels/FreezeTrichotomy
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/FreezeTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The freeze-deposit sign follows the critical inverse-temperature trichotomy. -/

import D5.S3.QuantumChannels.DecoherenceFreeze

namespace D5.S3.QuantumChannels.DecoherenceFreeze

/-!
# Freeze-deposit trichotomy

The imported positive branch and the zero and negative branches below display the full sign
trichotomy, so no duplicate combined theorem is added. No topological convergence theorem is
proved; only the finite upper bound is included. The pinned mathlib has no unprimed
`div_lt_iff` or `div_lt_div_iff`, and searches found no `strictMonoOn_const_sub_div` or
`strictMono_const_sub_div`; the proofs use the positivity-indexed division lemmas directly.
-/

/-- The freeze deposit vanishes exactly at the critical inverse temperature. -/
theorem decoherence_freeze_eq_zero_iff_at_critical
    {beta entropyTax passiveEnergy : ℝ}
    (hbeta : 0 < beta) (henergy : 0 < passiveEnergy) :
    freezeDeposit beta entropyTax passiveEnergy = 0 ↔
      beta = criticalInverseTemperature entropyTax passiveEnergy := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  rw [freezeDeposit, criticalInverseTemperature, sub_eq_zero]
  constructor
  · intro h
    apply (eq_div_iff henergy.ne').2
    have hcross := (div_eq_iff hbeta.ne').1 h.symm
    simpa [mul_comm] using hcross.symm
  · intro h
    apply (eq_div_iff hbeta.ne').2
    have hcross := (eq_div_iff henergy.ne').1 h
    simpa [mul_comm] using hcross

/-- The freeze deposit is negative exactly below the critical inverse temperature. -/
theorem decoherence_freeze_neg_iff_below_critical
    {beta entropyTax passiveEnergy : ℝ}
    (hbeta : 0 < beta) (henergy : 0 < passiveEnergy) :
    freezeDeposit beta entropyTax passiveEnergy < 0 ↔
      beta < criticalInverseTemperature entropyTax passiveEnergy := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  rw [freezeDeposit, criticalInverseTemperature, sub_neg, lt_div_iff₀ hbeta,
    lt_div_iff₀ henergy]
  simp [mul_comm]

/-- A positive entropy tax makes the freeze deposit strictly increase between positive betas. -/
theorem freeze_deposit_strictly_increases
    {beta1 beta2 entropyTax passiveEnergy : ℝ}
    (hbeta1 : 0 < beta1) (hbeta12 : beta1 < beta2) (htax : 0 < entropyTax) :
    freezeDeposit beta1 entropyTax passiveEnergy <
      freezeDeposit beta2 entropyTax passiveEnergy := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  change passiveEnergy - entropyTax / beta1 < passiveEnergy - entropyTax / beta2
  rw [sub_lt_sub_iff_left, div_lt_div_iff₀ (hbeta1.trans hbeta12) hbeta1]
  exact mul_lt_mul_of_pos_left hbeta12 htax

/-- For positive beta and a nonnegative entropy tax, the deposit is at most the energy shift. -/
theorem freeze_deposit_le_passive_energy
    {beta entropyTax passiveEnergy : ℝ}
    (hbeta : 0 < beta) (htax : 0 ≤ entropyTax) :
    freezeDeposit beta entropyTax passiveEnergy ≤ passiveEnergy := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  rw [freezeDeposit]
  exact sub_le_self _ (div_nonneg htax hbeta.le)

#print axioms decoherence_freeze_eq_zero_iff_at_critical
#print axioms decoherence_freeze_neg_iff_below_critical
#print axioms freeze_deposit_strictly_increases
#print axioms freeze_deposit_le_passive_energy

end D5.S3.QuantumChannels.DecoherenceFreeze
