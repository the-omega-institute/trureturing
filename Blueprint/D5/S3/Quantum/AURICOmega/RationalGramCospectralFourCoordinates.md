# The common four-coordinate criterion

## Abstract

Four-coordinate realizability of cospectral rational unit Gram matrices.

**Theorem 1.1 (The exact four-coordinate criterion for both families).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates.four_coordinate_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates.four_coordinate_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational t, either matrix is realizable in four rational coordinates exactly when t is one half or the following two arithmetic conditions hold. One plus four times t must be a rational square, and double the difference between one and twice t must be a sum of two rational squares.

Away from the two singular endpoints, a square Gram factor forces the common determinant to be a square. Dividing by the square of the repeated eigenvalue gives the first condition. When it holds away from the endpoints, the forms are rationally congruent. After aligning two unit axes, the remaining directions require the second condition. A pair of orthogonal vectors in two coordinates gives the converse. At t equal to minus one quarter both forms require five coordinates. At t equal to one half the paired-edge matrix requires four and the triangle-block matrix two.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates.four_coordinate_criterion`
- Dependency: [D5/S3/Quantum/AURICOmega/RationalGramCospectral](RationalGramCospectral.md)
