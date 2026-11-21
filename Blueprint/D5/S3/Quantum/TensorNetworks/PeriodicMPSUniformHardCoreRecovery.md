# Two-site reconstruction near the cyclic independent-set state

## Abstract

Two-site reconstruction near the cyclic independent-set state

**Theorem 1.1 (Generic reconstruction in an actual-state neighborhood).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery.exists_generic_actual_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery.exists_generic_actual_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* Igor Lesanovsky (2012). *Liquid ground state, gap and excited states of a strongly correlated spin chain*. DOI: [10.1103/PhysRevLett.108.105301](https://doi.org/10.1103/PhysRevLett.108.105301). URL: <https://arxiv.org/abs/1110.1815v1>.

*Commentary.*

For each ring length n ≥ 7, the normalized projector of the equal-weight cyclic independent-set state lies in a relatively Euclidean-open neighborhood in the actual periodic binary bond-two projector image. This neighborhood contains a relatively open dense set of targets. For each such target, equality of the trace-one first adjacent two-site marginals with any actual projector of that length forces equality of the full projectors. Equality of projectors identifies the same ray, or the same unit-mass amplitude up to phase.

The witness marginal has a singleton fiber even in the compact closure of the actual projector image. Compactness and a determinant-pencil decoder force all actual competitors with sufficiently nearby observations into the four-complex-dimensional ordinary trace chart. Seven regular real readouts leave one real coordinate. Along that coordinate, the real 00,01 coherence has a strict analytic fold, with curvature certified by the shifted hard-core energy.

Two analytic paths share the seven regular readouts and the fold coherence. The normalized 11,11 population separates them at fourth order with a nonzero coefficient of sign (−1)^(n−1). A length recurrence lifts the checked transfer-coefficient identities to every n ≥ 7. Analyticity makes the coincidence set of the two branches nowhere dense, and localization transfers singleton fibers to the actual projector image.

Lesanovsky supplies the periodic constrained ground-state model and its equal weights at fugacity one. Critch and Morton formulate the broader marginal reconstruction question in Conjecture 10. Density here is relative to the specified neighborhood for each length.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery.exists_generic_actual_reconstruction`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation](PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingCertificate](PeriodicMPS/PeriodicMPSUniformHardCoreLeadingCertificate.md)
