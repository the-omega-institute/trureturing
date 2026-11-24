# Monotonicity of diagonal discord in finite dimensions

## Abstract

Diagonal discord decreases under every local quantum channel on the measured subsystem that preserves classical–quantum states. Both optimized entropy gains are attained.

Conjecture 1 of Liu, Takagi and Lloyd asserts monotonicity under every local discord-nongenerating channel on the measured qubit. It appears in journal Section 3.2.2, p. 9, and arXiv v2 Section III.B.2, p. 6. The definitions in equations (2) and (8) include all rank-one eigenbasis measurements within degenerate eigenspaces.

**Definition 1.1 (Projective pinching).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pinch`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pinch` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

Pinching is the completely positive trace-preserving map obtained by forgetting the outcome of a complete projective measurement.

**Theorem 1.2 (Support of the pinched state).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.supportContained_pinch`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.supportContained_pinch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

A vector annihilated by the pinched state makes the sum of nonnegative compressed quadratic forms zero. Each term then vanishes, and completeness of the projections puts the vector in the nullspace of the input.

**Theorem 1.3 (Entropy gain of pinching).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.finiteTraceLogRelativeEntropy_pinch`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.finiteTraceLogRelativeEntropy_pinch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The relative entropy from a state to its pinching equals the gain in von Neumann entropy. Input support is contained in the pinched support, so the finite trace-log expression applies to singular states.

**Theorem 1.4 (Relative entropy at a fixed reference).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.extendedQuantumRelativeEntropy_pinch_pythagoras`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.extendedQuantumRelativeEntropy_pinch_pythagoras` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

For a reference fixed by the pinching and containing the input support, the divergence to that reference splits into the pinching gain and the divergence from the pinched state to the reference. The output support condition follows from data processing. The logarithm of the fixed reference commutes with the projections, so the trace cross term is unchanged. This is the fixed-projective case of Gour, Marvian and Spekkens, arXiv:0901.0943v2, Theorem 3, equations (9)–(15).

**Definition 1.5 (Local basis projections).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localPVM`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localPVM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

Each projection onto a column of the measured-side unitary is tensored with the identity on the second subsystem.

**Definition 1.6 (Local channel).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

Tensoring the measured-side Kraus operators with the second identity defines the extension of the channel to the joint state.

**Theorem 1.7 (Joint Kraus action).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The joint channel applies the Kraus sum with each operator acting on the first factor and the identity acting on the second.

**Theorem 1.8 (Locality and the marginal).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.marginalRight_localChannel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.marginalRight_localChannel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

Tracing out the second factor after the local action gives the same first marginal as applying the measured-side channel after the trace.

**Definition 1.9 (Eligible eigenbases).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.Eligible`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.Eligible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

A basis is eligible when the actual first marginal is diagonal in it.

**Definition 1.10 (Classical–quantum states).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.IsCQ`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.IsCQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

A state is classical–quantum when it is fixed by some rank-one local pinching. Its off-diagonal first-coordinate blocks vanish in that basis.

**Definition 1.11 (Preservation of classical–quantum states).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.PreservesCQ`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.PreservesCQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

Every classical–quantum input is sent to a classical–quantum output.

**Definition 1.12 (Entropy gain in one basis).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.basisGain`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.basisGain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The gain is the entropy of the pinched joint state minus the input entropy.

**Definition 1.13 (Diagonal discord).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord`

*Formalization.* `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Acknowledgement.* Xueyuan Hu; Heng Fan (2016). *Extracting quantum coherence via steering*. DOI: [10.1038/srep34380](https://doi.org/10.1038/srep34380). URL: <https://arxiv.org/abs/1508.01978v2>.

*Commentary.*

The quantity is the infimum of the entropy gain over eligible bases. Hu and Fan's Eq. (6), arXiv v2, p. 2, gives the same quantity by taking relative entropy in their B-side measurement-induced disturbance, swapping A and B, and converting bits to nats. Their Theorem 1, Eq. (8), bounds steering-induced coherence by that disturbance.

**Theorem 1.14 (Transfer with a nonnegative residual).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pointwise_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pointwise_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

For every eligible input basis, send the pinched input through the channel to obtain a classical–quantum reference. Its first marginal equals the actual output marginal, so a classical basis for the reference is eligible for the output. The gain in this output basis plus the nonnegative relative entropy from the pinched output to the reference is bounded by the input gain. Data processing gives the upper bound after the fixed-reference decomposition.

**Theorem 1.15 (Monotonicity of the optimized gain).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The pointwise transfer bounds the output infimum by every eligible input value. Taking the input infimum proves monotonicity for all joint states and all local channels preserving classical–quantum states.

**Theorem 1.16 (Existence of a minimizing eigenbasis).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

The eligible eigenbases form a nonempty closed subset of the compact unitary group. The entropy gain is continuous by the functional calculus of the continuous scalar function minus x log x, including at zero.

**Theorem 1.17 (Comparison of attained minima).**

Lean statement: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zi-Wen Liu; Ryuji Takagi; Seth Lloyd (2019). *Diagonal quantum discord*. DOI: [10.1088/1751-8121/ab0774](https://doi.org/10.1088/1751-8121/ab0774). URL: <https://arxiv.org/abs/1708.09076v2>.

*Commentary.*

There are eligible minimizing eigenbases for the input and output, and the minimum output gain is at most the minimum input gain. The comparison holds in arbitrary finite dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.Eligible`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.IsCQ`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.PreservesCQ`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.basisGain`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_attained`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.diagonalDiscord_localChannel_mono_attained`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.extendedQuantumRelativeEntropy_pinch_pythagoras`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.finiteTraceLogRelativeEntropy_pinch`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localChannel_apply`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.localPVM`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.marginalRight_localChannel`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pinch`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.pointwise_transfer`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity.supportContained_pinch`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTrace/Isometries](../PartialTrace/Isometries.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](../../Measurement/Auric/CoordinatePinching.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../../RandomCircuits/HaarTwoCopyTwirl.md)
