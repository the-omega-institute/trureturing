# Finite sign twirls and entropy gaps

## Abstract

The subentropy increase under coordinate block pinching is nonnegative and convex.

**Definition 1.1 (Independent block signs).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.blockSign`

*Formalization.* `D5/S3/Quantum/Subentropy/PinchingGap.blockSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean function on the classical index set chooses a sign −1 or +1 independently for each block.

**Definition 1.2 (Diagonal sign action).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.signUnitary`

*Formalization.* `D5/S3/Quantum/Subentropy/PinchingGap.signUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal matrix U_s multiplies every coordinate (x,b) by the sign assigned to x. Both U_s*U_s and U_sU_s* equal the identity.

**Definition 1.3 (Exact block pinching).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.signTwirl`

*Formalization.* `D5/S3/Quantum/Subentropy/PinchingGap.signTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assign a sign ±1 independently to each classical block x. The diagonal matrix U_s acts by that sign throughout the block. It is self-adjoint and unitary. For every complex matrix A on X×B, the uniform average of U_s A U_s* over all sign choices is exactly blockPinch(A). The identity does not require positivity or trace normalization.

For entries in the same block the product of the signs is one. For entries in distinct blocks, flipping the sign of the first block pairs summands with their negatives. This finite involution argument covers empty coordinate spaces as well.

**Definition 1.4 (The pointwise entropy defect).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.signOrbitEntropyGap`

*Formalization.* `D5/S3/Quantum/Subentropy/PinchingGap.signOrbitEntropyGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let q(A,z)=Re⟨z,Az⟩/2. Matrix linearity and the sign-twirl identity give q(blockPinch(A),z)=av_s q(U_s A U_s*,z). Therefore η(q(blockPinch(A),z))−av_s η(q(U_s A U_s*,z)) is exactly the finite entropy Jensen gap of the actual sign orbit. For positive semidefinite A, every orbit readout is nonnegative, so this pointwise defect is nonnegative.

The common Gaussian representation identifies the integral of this defect with Q(blockPinch(A))−Q(A) on positive trace-one matrices: every sign conjugate has the same subentropy and the same fixed Gaussian baseline. Joint convexity of the scalar Jensen gap therefore proves convexity of the actual subentropy pinching gap.

**Theorem 1.5 (Concavity of matrix subentropy).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.matrix_subentropy_concave`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/PinchingGap.matrix_subentropy_concave` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any finite nonempty matrix coordinate space, matrixSubentropy is concave on positive semidefinite trace-one matrices. The quadratic Gaussian readout is matrix-linear and nonnegative. Pointwise concavity of η, integrability from the Gaussian representation, and cancellation of the common dimension baseline give the inequality.

**Theorem 1.6 (Convexity and nonnegativity of the subentropy gap).**

Lean statement: `D5/S3/Quantum/Subentropy/PinchingGap.actual_pinching_gap_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/PinchingGap.actual_pinching_gap_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty coordinate spaces, the map A↦Q(blockPinch(A))−Q(A) is convex on the positive trace-one state space and is nonnegative there. The statement uses the determinant-integral matrixSubentropy itself. It follows by integrating the pointwise finite Jensen-gap laws and cancelling the common coordinate baseline in the Gaussian representation.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.actual_pinching_gap_laws`
- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.blockSign`
- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.matrix_subentropy_concave`
- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.signOrbitEntropyGap`
- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.signTwirl`
- Truth anchor: `D5/S3/Quantum/Subentropy/PinchingGap.signUnitary`
- Dependency: [D5/S3/Quantum/Subentropy/ClassicalQuantumGram](ClassicalQuantumGram.md)
- Dependency: [D5/S3/Quantum/Subentropy/EntropyJensenGap](EntropyJensenGap.md)
- Dependency: [D5/S3/Quantum/Subentropy/GaussianMatrix](GaussianMatrix.md)
