# Generic one-site ambiguity in the compact periodic MPS projector space

## Abstract

Generic one-site ambiguity in the compact periodic MPS projector space

**Definition 1.1 (Single-site observation).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.oneSiteObservation`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.oneSiteObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Trace out the second site in the adjacent-pair partial trace of the full projector.

**Theorem 1.2 (Trace one on the compact closure).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.trace_oneSiteObservation_of_mem_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.trace_oneSiteObservation_of_mem_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an actual projector, the one-site trace before normalization is the total squared amplitude mass. Division by that positive mass gives trace one. This identity extends to the projector closure by continuity.

**Theorem 1.3 (Actual collisions arbitrarily close in the one-site fiber).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.generic_projector_one_site_ambiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.generic_projector_one_site_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every ring length at least four, work in the relative Euclidean topology on the closure of the trace-one projectors of actual periodic binary bond-two complex matrix product states. The nonzero locus of the normalized adjacent-pair commutator is nonempty, open and dense there. Each actual point of that locus lies in the relative closure of distinct actual projectors with its single-site observation.

The commutator is continuous and homogeneous of degree two in the adjacent-pair matrix. Projecting the dense raw amplitude locus preserves nonvanishing and approximates every actual projector, so its image is dense in the compact closure.

Apply the collective physical rotation to any core that presents the target. Equality of the raw one-site matrices preserves the trace and hence the positive squared amplitude mass. Every point of the curve therefore gives an actual normalized projector with the same single-site density. The raw adjacent-pair matrix differs arbitrarily near the target parameter. The common normalization preserves this difference, which distinguishes the full projectors.

Critch and Morton give the periodic trace parametrization and formulate the periodic marginal reconstruction problem in Conjecture 10, SIGMA 10 (2014), 095. The declaration here proves the single-site insufficiency bound in the trace-one projector formulation.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.generic_projector_one_site_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.oneSiteObservation`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity.trace_oneSiteObservation_of_mem_closure`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization](PeriodicMPSUniformHardCoreLocalization.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity](../PeriodicMPSOneSiteAmbiguity.md)
