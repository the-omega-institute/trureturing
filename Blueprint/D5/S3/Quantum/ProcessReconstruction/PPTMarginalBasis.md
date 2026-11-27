# Process tomography with arbitrary PPT marginals

## Abstract

Marginal-dependent reconstruction bounds for square PPT probes in any basis.

**Theorem 1.1 (A basis-independent physical upper bound).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_weighted_ppt_of_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_weighted_ppt_of_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

Changing the basis of the reference register conjugates both channel outputs by the same unitary. This preserves their Hilbert–Schmidt distance, the input Choi distance and the exact minimum over channel pairs. Diagonalizing a positive definite reference marginal yields a bound in terms of its eigenvalues on the original probe.

**Theorem 1.2 (Loss of identifiability at a singular marginal).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_zero_gain_of_singular_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_zero_gain_of_singular_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

A kernel direction in the reference marginal creates a zero realignment direction for a square positive probe. The physical minimum is attained by two distinct completely positive trace-preserving maps, whose outputs on that probe coincide.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_weighted_ppt_of_posDef`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.exists_cptp_pair_zero_gain_of_singular_marginal`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain](PPTOperationalGain.md)
