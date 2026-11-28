# The P48p Paley Norm-Four Certificate

## Abstract

The ternary Paley certificate excludes squared norm four in the odd neighbor of the catalogue lattice P48p.

**Theorem 1.1 (The catalogue odd neighbor has no vector of squared norm four).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.norm_ne_four`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.norm_ne_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. H. Conway and N. J. A. Sloane (1999). *Sphere Packings, Lattices and Groups*. DOI: [10.1007/978-1-4757-6568-7](https://doi.org/10.1007/978-1-4757-6568-7).

*Commentary.*

In the catalogue basis, take the integral rows pairing evenly with the first frame vector and adjoin half of that frame vector. The theorem excludes squared norm four for every row in this odd neighbor, using the rational extension of the catalogue Gram form. Conway and Sloane’s Sphere Packings, Lattices and Groups provides lattice background. The Gram matrix and the group generators used to build the frame come from the GRAM and GROUP_GENERATORS sections of the Nebe–Sloane P48p entry (https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/P48p.html).

A vector of squared norm four would have integral half-frame pairings with square sum twelve. Their residue modulo three is nonzero, since an all-zero residue would make the square sum divisible by nine. It has Hamming weight at most twelve and lies in the ternary syndrome kernel. Its two signed chart halves form a Paley graph pair. Since the Paley matrix squares to the identity over the ternary field, the lighter half can be taken as a nonzero input of weight at most six. The checked small-support bound forces the two weights to sum to more than twelve.

The existence of an extremal vertex operator algebra of central charge 48 remains an open problem.

**Theorem 1.2 (Every anchored weight-six input has total weight above twelve).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.anchored_weight_six_sparse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.anchored_weight_six_sparse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight-preserving projective action sends three occupied directions to infinity, zero and one. An overall sign sets the coefficient at infinity to one. The two other anchors have four sign pairs. Choose three distinct slopes from the remaining 21 and give each one of two signs. This gives 4 × 1330 × 8 = 42,560 anchored inputs, where 1330 is the number of three-element subsets of 21 slopes.

The kernel checks the branches by anchor sign pair, first chosen slope and its sign. For each input, the checker sums the six character contributions in each output coordinate modulo three and stops at the seventh nonzero coordinate. The soundness proof relates those sums to multiplication by the Paley matrix, yielding output weight at least seven. The input has weight six, so the total exceeds twelve. The checks for weights one through five complete the small-support bound.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.anchored_weight_six_sparse`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseWeightSix.norm_ne_four`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48pPaleySparseCheck](P48pPaleySparseCheck.md)
