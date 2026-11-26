# Direct Bell-kernel recovery

## Abstract

Conjugate reshaping of a Bell-complement kernel family gives Kraus operators for exact recovery.

**Definition 1.1 (Kraus amplification).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.amplifyKraus`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.amplifyKraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Amplification on the second factor is the sum of congruences by the reference identity tensored with the input Kraus operators. When the Kraus family represents a channel, the sum agrees entrywise with applying the channel to each reference block.

**Definition 1.2 (Recovery Kraus operators).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.bellRecoveryKraus`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.bellRecoveryKraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a vector vⱼ indexed by A × B, the recovery operator has entry at (a, b) equal to the conjugate of vⱼ(a, b) divided by √|A|.

**Theorem 1.3 (Exact scalar recovery from the kernel projection).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.direct_bell_kernel_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.direct_bell_kernel_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be the normalized Bell projector and B₀ the Kraus amplification of I − P. Suppose the outer products of vⱼ sum to Q, the projection onto the kernel of B₀. The reshaped recovery operators have effect Trₐ(Q)/d ≤ I. Their sum of congruences is completely positive.

Each input Kraus operator, when composed with each recovery operator, is a scalar times the identity. This follows because pulling a kernel vector back through an amplified input Kraus operator puts it in the Bell line. The sum of squared scalar moduli is Tr(QX₀)/d², where X₀ is the amplified Bell projector. Thus the composite acts by this nonnegative real scalar on every input matrix.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.amplifyKraus`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.bellRecoveryKraus`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.direct_bell_kernel_recovery`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransformer](../../Lieb/SupportPerspectiveTransformer.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction](../../ProcessReconstruction/LiuWildChoiObstruction.md)
