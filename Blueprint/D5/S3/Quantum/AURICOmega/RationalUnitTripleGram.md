# Three unit vectors in five rational coordinates

## Abstract

Rational realization of a three-point unit Gram matrix in five coordinates.

**Theorem 1.1 (A three-square criterion).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be rational numbers with squares at most one, and let c be rational. The three prescribed inner products a, b and c are realizable by unit vectors in five rational coordinates exactly when their unit-diagonal Gram determinant is a sum of three rational squares.

Align the first unit vector with a coordinate axis by a rational isometry. The remaining four coordinates of the two other vectors form a pair of quaternions. The Gram determinant is the sum of the three squared imaginary coordinates of their relative product. Conversely, four squares construct the first quaternion and the three-square decomposition specifies the imaginary coordinates of the relative product. Inverting the first quaternion reconstructs the second. When the first residual vanishes, the determinant condition forces the residual inner product to vanish.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple`
- Dependency: [D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex](../../Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.md)
