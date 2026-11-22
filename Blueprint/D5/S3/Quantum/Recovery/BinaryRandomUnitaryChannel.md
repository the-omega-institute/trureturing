# Canonical fidelity of a binary random-unitary channel

## Abstract

Canonical overlap and actual CPTP realization of binary random-unitary channels.

**Theorem 1.1 (Normalized untouched reference).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew S. Fletcher; Peter W. Shor; Moe Z. Win (2007). *Optimum Quantum Error Recovery Using Semidefinite Programming*. DOI: [10.1103/PhysRevA.75.012338](https://doi.org/10.1103/PhysRevA.75.012338). URL: <https://arxiv.org/abs/quant-ph/0606035v1>.

*Commentary.*

For every positive code dimension d, the canonical rank-one vector state has trace one. Tracing out the first, system factor leaves I/d on the second, reference factor.

**Theorem 1.2 (Canonical Kraus trace identity).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_overlap_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_overlap_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew S. Fletcher; Peter W. Shor; Moe Z. Win (2007). *Optimum Quantum Error Recovery Using Semidefinite Programming*. DOI: [10.1103/PhysRevA.75.012338](https://doi.org/10.1103/PhysRevA.75.012338). URL: <https://arxiv.org/abs/quant-ph/0606035v1>.

*Commentary.*

On a nonzero code, the first-factor Kraus map tensored with the identity acts on the canonical rank-one state. Each overlap amplitude is the Kraus trace divided by d. The overlap is the sum of squared moduli, with the reference left untouched and without rescaling the output trace.

**Theorem 1.3 (Actual binary CPTP channel).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binaryChannel_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binaryChannel_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew S. Fletcher; Peter W. Shor; Moe Z. Win (2007). *Optimum Quantum Error Recovery Using Semidefinite Programming*. DOI: [10.1103/PhysRevA.75.012338](https://doi.org/10.1103/PhysRevA.75.012338). URL: <https://arxiv.org/abs/quant-ph/0606035v1>.

*Commentary.*

For real nonnegative weights p and q summing to one, square-root-weighted unitary Kraus matrices define a CPTP channel. Its action on every code matrix X is p UXU† + q VXV†.

**Theorem 1.4 (Trace score after an actual CPTP decoder).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binary_score_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binary_score_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew S. Fletcher; Peter W. Shor; Moe Z. Win (2007). *Optimum Quantum Error Recovery Using Semidefinite Programming*. DOI: [10.1103/PhysRevA.75.012338](https://doi.org/10.1103/PhysRevA.75.012338). URL: <https://arxiv.org/abs/quant-ph/0606035v1>.

*Commentary.*

For d positive, an actual CPTP decoder D with Kraus matrices Kₐ acts after the binary channel. The score is the sum over a of p|tr(KₐU)|² + q|tr(KₐV)|² divided by d². The Kraus action hypothesis holds on every code matrix.

**Theorem 1.5 (One diagonal unitary bounds every decoder).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.diagonal_binary_unitary_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.diagonal_binary_unitary_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew S. Fletcher; Peter W. Shor; Moe Z. Win (2007). *Optimum Quantum Error Recovery Using Semidefinite Programming*. DOI: [10.1103/PhysRevA.75.012338](https://doi.org/10.1103/PhysRevA.75.012338). URL: <https://arxiv.org/abs/quant-ph/0606035v1>.

*Commentary.*

When the branches are the identity and a diagonal unitary, completeness of an arbitrary decoder bounds the norm of each vector of diagonal Kraus entries by one. The scalar optimizer realizes the resulting bound as a diagonal unitary CPTP channel.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binaryChannel_action`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.binary_score_kraus`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_overlap_kraus`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.canonical_reference`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel.diagonal_binary_unitary_optimal`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore](../QuantumChannels/MayerKnillInfidelityScalingCore.md)
- Dependency: [D5/S3/Quantum/Recovery/BinaryUnitaryOptimization](BinaryUnitaryOptimization.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../../QuantumBounds/PeritoTsirelson.md)
