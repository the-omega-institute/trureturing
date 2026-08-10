/- GID: D5/S3/QuantumChannels/DecoherenceFreeze
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/DecoherenceFreeze
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The decoherence-freeze deposit ΔE_pass − ΔS/β is positive exactly when the inverse temperature β exceeds the critical value ΔS/ΔE_pass. -/

import Mathlib

namespace D5.S3.QuantumChannels.DecoherenceFreeze

/-- The decoherence-freeze deposit `ΔE_pass − ΔS/β`: passive energy shift minus temperature-scaled entropy. -/
noncomputable def freezeDeposit (beta entropyTax passiveEnergy : ℝ) : ℝ :=
  passiveEnergy - entropyTax / beta

/-- The critical inverse temperature `β_c = ΔS/ΔE_pass`. -/
noncomputable def criticalInverseTemperature (entropyTax passiveEnergy : ℝ) : ℝ :=
  entropyTax / passiveEnergy

/-- Freeze criterion: with positive temperature `β` and positive passive-energy shift, the freeze deposit
is positive exactly when `β` exceeds the critical inverse temperature `β_c = ΔS/ΔE_pass`. -/
theorem decoherence_freeze_iff_above_critical {beta entropyTax passiveEnergy : ℝ}
    (hbeta : 0 < beta) (henergy : 0 < passiveEnergy) :
    0 < freezeDeposit beta entropyTax passiveEnergy ↔
      criticalInverseTemperature entropyTax passiveEnergy < beta := by
  rw [freezeDeposit, criticalInverseTemperature, sub_pos, div_lt_iff₀ hbeta, div_lt_iff₀ henergy]
  simp [mul_comm]

end D5.S3.QuantumChannels.DecoherenceFreeze
