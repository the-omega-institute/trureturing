# Recovery of the equal-weight independent-set state

## Abstract

One adjacent marginal determines the cyclic independent-set witness

**Theorem 1.1 (The observed 11 entry forces hard-core support).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.support_of_pairGram_corner_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.support_of_pairGram_corner_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a cyclic amplitude at length n ≥ 7, the 11,11 entry of the first adjacent Gram matrix is the sum of squared moduli over words starting with 11. A zero sum forces each such amplitude to vanish. Rotating any adjacent occupied pair into the observed position then forces its word amplitude to vanish, including when the pair straddles the seam.

**Theorem 1.2 (The adjacent Gram matrix determines the shifted energy).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.shiftedEnergy_eq_observed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.shiftedEnergy_eq_observed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Lesanovsky (2012). *Liquid ground state, gap and excited states of a strongly correlated spin chain*. DOI: [10.1103/PhysRevLett.108.105301](https://doi.org/10.1103/PhysRevLett.108.105301). URL: <https://arxiv.org/abs/1110.1815v1>.

*Commentary.*

For n ≥ 7, assume cyclicity and independent-set support. On supported words, the projected flip, half-weight hop and number terms have the compressed move weights. Cyclicity makes every edge expectation equal to the first one. The shifted energy is n times the squared amplitude mass plus n times that first-edge expectation. The Gram trace gives the mass, while its entries give the flip, hop and number contributions.

**Theorem 1.3 (The fixed witness is determined among cyclic amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.eq_constant_same_norm_of_pairGram_eq_indicator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.eq_constant_same_norm_of_pairGram_eq_indicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Lesanovsky (2012). *Liquid ground state, gap and excited states of a strongly correlated spin chain*. DOI: [10.1103/PhysRevLett.108.105301](https://doi.org/10.1103/PhysRevLett.108.105301). URL: <https://arxiv.org/abs/1110.1815v1>.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

At each length n ≥ 7, let the target amplitude be a on the independent sets of the cycle and zero on the other words. Any cyclic complex amplitude with the same raw adjacent two-site Gram matrix is constant on the independent sets and zero elsewhere. Its constant c satisfies |c|² = |a|², giving recovery up to unit phase for every nonzero a and forcing the zero competitor when a = 0.

The observed 11,11 entry first gives support. The target has zero shifted Dirichlet energy. The shared Gram matrix transfers that energy value to the competitor, so deletion connectivity forces its supported amplitudes to equal its empty-word amplitude. The common Gram trace then fixes the modulus.

Lesanovsky, arXiv:1110.1815v1, equations (1)–(2) and pages 2–3, gives the unique ground state of the periodic constrained parent and its equal weights at z = 1. The adjacent-marginal determination uses the hop term and the observation identity above. Critch and Morton give the broader generic periodic reconstruction question, which remains open across all lengths.

**Theorem 1.4 (Recovery in the periodic bond-two trace image).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.traceWord_eq_unit_of_rawTwo_eq_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.traceWord_eq_unit_of_rawTwo_eq_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

A periodic binary bond-two trace tensor is cyclic by the trace identity. The two explicit rank-one cores realize the independent-set indicator, and the periodic raw two-site matrix is its adjacent Gram matrix. At every n ≥ 7, any periodic core with that same raw matrix therefore has full amplitudes equal to the witness amplitudes times a single scalar of squared modulus one.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.eq_constant_same_norm_of_pairGram_eq_indicator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.shiftedEnergy_eq_observed`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.support_of_pairGram_corner_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness.traceWord_eq_unit_of_rawTwo_eq_witness`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](PeriodicMPSTwoSiteAmbiguity.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy](PeriodicMPSUniformHardCoreEnergy.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude](PeriodicMPSUniformHardCoreWitnessAmplitude.md)
