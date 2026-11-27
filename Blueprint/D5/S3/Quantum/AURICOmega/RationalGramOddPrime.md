# Seven coordinates for a rank-four unit Gram matrix

## Abstract

An odd-prime obstruction to rational Gram realization in six coordinates.

**Definition 1.1 (The prescribed Gram entries).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.hasUnitGram`

*Formalization.* `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.hasUnitGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are one. The upper-triangular entries in row order are −1/3, −1/2, −1/2, 1/6, 1/6, and 1/4.

**Theorem 1.2 (Exactly seven coordinates are necessary and sufficient).**

Lean statement: `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.realizable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.realizable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four rational unit vectors with the prescribed Gram entries exist in n coordinates exactly when n is at least seven.

An invertible rational change of basis makes their Gram form diagonal with entries 1, 2, 3, and 3. In six coordinates, rational reflections align the first three vectors with an explicit frame. The last vector must then express three as six times a rational square plus two rational squares. After denominators are cleared, reduction modulo three forces both unweighted coordinates to be divisible by three. Divide the equation by three and reduce again to force the same divisibility for the remaining coordinate and the denominator. Descent rules out a positive denominator.

In seven coordinates, four orthogonal vectors with squared lengths 1, 2, 3, and 3 give an explicit realization after the inverse change of basis. Padding with zero coordinates preserves the Gram entries in every larger dimension.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.hasUnitGram`
- Truth anchor: `D5/S3/Quantum/AURICOmega/RationalGramOddPrime.realizable_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex](../../Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.md)
