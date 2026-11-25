# Three unit vectors in five rational coordinates

## Abstract

Rational realization of a three-point unit Gram matrix in five coordinates.

**Theorem 1.1 (A three-square criterion).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple` (`✓ std3`). ∎

*Citation.* John L. Hunsucker (1971). *Primitive representation of a binary quadratic form as a sum of four squares*. DOI: [10.4064/aa-19-4-321-325](https://doi.org/10.4064/aa-19-4-321-325). URL: <https://doi.org/10.4064/aa-19-4-321-325>.

*Commentary.*

Let a and b be rational numbers with squares at most one, and let c be rational. The three prescribed inner products a, b and c are realizable by unit vectors in five rational coordinates exactly when their unit-diagonal Gram determinant is a sum of three rational squares. Both bounds are needed. At (a,b,c) = (2,1,2) or (1,2,2) the determinant is zero, yet two unit vectors cannot have inner product two.

Align the first unit vector with a coordinate axis by a rational isometry. The remaining four coordinates of the two other vectors form a pair of quaternions. Clear their denominators and use the OmegaMath integer Gram identity. Dividing its three imaginary coordinates by the product of the two denominators gives the three rational squares. Conversely, four squares construct the first quaternion and the three-square decomposition specifies the imaginary coordinates of the relative product. Inverting the conjugate of the first quaternion reconstructs the second. When the first residual vanishes, the determinant condition forces the residual inner product to vanish.

For positive determinant the residual binary quadratic form is the rational version of the four-linear-square criterion attributed to Mordell in Hunsucker, Section 1. The rational proof also treats determinant zero.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple`
- Dependency: [D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex](../../Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.md)
- Dependency: [D5/S3/Quantum/AURICOmega/OmegaShadowBridge](OmegaShadowBridge.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary](../Entanglement/Marginals/FibRationalBoundary.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint](../Entanglement/Marginals/RationalQubitMixedEndpoint.md)
