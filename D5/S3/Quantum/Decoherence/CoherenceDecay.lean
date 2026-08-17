/- GID: D5/S3/Quantum/Decoherence/CoherenceDecay
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/CoherenceDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict phase damping sends equal-superposition coherence to zero. -/

import D5.S3.Quantum.QubitWitnesses

namespace D5.S3.Quantum.Decoherence.CoherenceDecay

open D5.S3.Quantum.QubitWitnesses
open Filter Topology

/-- If the retention coefficient is strictly below one, the off-diagonal entry
of the iterated equal-superposition state converges to zero. -/
theorem equal_superposition_coherence_tendsto_zero
    (c : DampingCoefficient) (hCoefficient : (c : Real) < 1) :
    Tendsto
      (fun N : Nat => phaseDampingIterate c N equalSuperpositionDensity 0 1)
      atTop (nhds 0) := by
  have hNorm : ‖(((c : Real) : Complex))‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg c.property.1]
    exact hCoefficient
  have hPow :
      Tendsto (fun N : Nat => (((c : Real) : Complex) ^ N)) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hNorm
  have hScaled :
      Tendsto (fun N : Nat => (1 : Complex) / 2 * (((c : Real) : Complex) ^ N))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hPow
  apply hScaled.congr'
  filter_upwards [] with N
  exact (equal_superposition_phase_damping_certificate c N).2.2.1.symm

end D5.S3.Quantum.Decoherence.CoherenceDecay
