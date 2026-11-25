# Regular simplices on rational unit spheres

## Abstract

The arithmetic classification of regular simplices on rational unit spheres.

**Theorem 1.1 (A square criterion for rational regular simplex vertices).**

Lean statement: `D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.rational_unit_simplex_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.rational_unit_simplex_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott Duke Kominers (2026). *Squared edge lengths of regular simplices with rational vertices*. DOI: [10.48550/arXiv.2605.12268](https://doi.org/10.48550/arXiv.2605.12268). URL: <https://arxiv.org/abs/2605.12268v1>.

*Commentary.*

Let n be positive. The rational unit sphere in n coordinates contains n+1 distinct points with a common pairwise inner product if and only if the odd member of the pair n, n+1 is a square. This is the unit-circumradius specialization of Kominers's squared-edge-length classification.

The square Gram matrix of all n+1 points is singular, forcing the common off-diagonal entry to be minus one divided by n. The Gram determinant of the first n columns is a rational square. Removing square factors gives the parity-dependent condition.

Center the coordinate basis in n+1 dimensions. For odd square n, a rational similarity on pairs of coordinates gives the required lengths. For even n with n+1 square, n is divisible by four and the all-ones normal can be normalized rationally. Quaternion multiplication on blocks of four coordinates supplies the remaining similarity. A rational reflection takes the unit normal to a coordinate axis, which can then be dropped.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.rational_unit_simplex_iff`
