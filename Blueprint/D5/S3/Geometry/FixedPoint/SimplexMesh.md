# Dominant lattice cells constrain coordinate minima

## Abstract

Dominant lattice cells constrain coordinate minima.

**Theorem 1.1 (Dominant lattice cells constrain coordinate minima).**

Lean statement: `D5/S3/Geometry/FixedPoint/SimplexMesh.size_bound_key`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FixedPoint/SimplexMesh.size_bound_key` (`✓ std3`). ∎

*Citation.* Math_XMUM (2025). *Brouwer fixed-point theorem via Scarf's lemma*. URL: <https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb>.

*Commentary.*

For positive n and l, lattice points are nonnegative integer coordinates indexed by Fin n, bounded by l and summing to l. For each selected index, compare that coordinate first, then break ties by the lexicographic order of the complete lattice tuple. A nonempty cell sigma dominant for these exact orders with color set C satisfies l < sum over C of coordinate minima plus |C|.

Assuming the opposite bound, assign one more than each selected coordinate minimum, zero elsewhere, and put the residual mass into coordinate zero. The resulting genuine lattice point contradicts dominance.

The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion.

## References

- Truth anchor: `D5/S3/Geometry/FixedPoint/SimplexMesh.size_bound_key`
- Dependency: [D5/S3/Combinatorics/Scarf/ColorfulCell](../../Combinatorics/Scarf/ColorfulCell.md)
