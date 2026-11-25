# Ordinary Petz recovery after binary projective measurement

## Abstract

Ordinary Petz recovery after computational-basis measurement exceeds coefficient five on faithful qubit states.

**Definition 1.1 (The coefficient-five estimate).**

Lean statement: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.claim`

*Formalization.* `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix the computational-basis measurement on a qubit. Its completely positive trace-preserving action retains exactly the diagonal of the input. For two positive-definite input states, write Δ for the finite trace-log Umegaki relative entropy before measurement minus the same relative entropy after measurement. The claim bounds the squared full trace norm of the ordinary Petz recovery error by 5Δ whenever Δ is positive.

**Theorem 1.2 (Uniform estimates for the faithful family).**

Lean statement: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.family_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.family_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take 0 < x ≤ 1/100. The input has diagonal (1/10, 9/10) and both off-diagonal entries −x/3. The reference has eigenvalues 1−x⁴ and x⁴ and eigenvectors proportional to (1, x³) and (−x³, 1), respectively. Both inputs and both measured outputs are positive definite.

Let q₀ and q₁ be the measured probabilities of the reference and let S be its positive square root. The reference output has full support, so the completed Petz channel acts on every matrix X by S diag(X₀₀/q₀, X₁₁/q₁) S. The diagonal projection is its own trace adjoint, and the recovery maps the measured reference back to the reference.

The loss satisfies x²/5 < Δ < (12141/10000)x². Expanding the input and output trace-log expressions in their spectral bases cancels the dominant reference logarithm. The remaining terms are bounded using the binary entropy derivative and elementary logarithm inequalities. The squared full trace norm of the recovery error is greater than (152/25)x². The error is traceless and real symmetric, so its squared norm is four times the sum of the squares of its first diagonal and off-diagonal entries.

**Definition 1.3 (Rational sequence with vanishing loss and commutator).**

Lean statement: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.counterexamples`

*Formalization.* `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.counterexamples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set x = 1/(n + 100) for natural n. Both matrices have rational entries. Every pair has positive loss and squared recovery error strictly above five times that loss. The loss tends to zero by its quadratic upper bound. The maximum operator norm of the two measurement projector commutators tends to zero by its cubic upper bound.

**Theorem 1.4 (A rational counterexample).**

Lean statement: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set x = 1/100, so the reference eigenvalue x⁴ is 1/100000000 and the rotation parameter x³ is 1/1000000. Both state matrices have rational entries. The loss is positive, and five times its upper bound is strictly below the lower bound on the squared recovery error.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.claim`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.counterexamples`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.family_bounds`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzBinaryProjectiveOverFive.result`
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](../Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](../Information/QubitNormalFormState.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](../Measurement/Auric/CoordinatePinching.md)
- Dependency: [D5/S3/Quantum/Recovery/ReferencePetzChannel](ReferencePetzChannel.md)
