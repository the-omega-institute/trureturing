# Signed Gaussian candidates at the radial square

## Abstract

Holomorphy of the signed candidates on the original radial disk

**Definition 1.1 (Common radial radius).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex u and v, the real radius sourceRadius(u,v) is min(1 − ‖u‖, 1 − ‖v‖).

**Theorem 1.2 (The original source bounds).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex u, v and z, ‖z‖ < sourceRadius(u,v) holds exactly when ‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1.

**Theorem 1.3 (Positive radius).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex u and v with ‖u‖ < 1 and ‖v‖ < 1, 0 < sourceRadius(u,v), so the open radial disk contains zero.

**Theorem 1.4 (Unit upper bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex u and v, sourceRadius(u,v) ≤ 1.

**Definition 1.5 (The signed candidate selector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.signedCandidate`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.signedCandidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Booleans square, e and f and complex u, v and r, signedCandidate(square,e,f,u,v,r) selects the signed candidateT(e,f,u,v,r) when square is true and the signed candidateJ(e,f,u,v,r) when it is false. The selector and the two source labels are passed through in the same order as in kernelMode.

**Theorem 1.6 (Analyticity on the original radial disk).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Booleans square, e and f and complex u and v, the function z ↦ signedCandidate(square,e,f,u,v,z²) is complex analytic at every point of the open ball about zero of radius sourceRadius(u,v).

At such a point, ‖z²‖ ≤ ‖z‖ keeps the source sums and the period correction in their differentiability domains. The T denominator E is nonzero using √‖z²‖ = ‖z‖. For J, the original source factors b(u) and b(v) and the sum W(e,u,z²) + W(f,v,z²) are nonzero there. The quotient and product rules give complex differentiability on the open ball, hence analyticity.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.signedCandidate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource](../Signed/CandidateSource.md)
