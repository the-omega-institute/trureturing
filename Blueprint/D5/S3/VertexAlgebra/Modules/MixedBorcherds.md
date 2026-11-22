# Finite mixed Borcherds identities

## Abstract

MixedBorcherds

Let A, C and B be integer-indexed complex bilinear actions of V on U, Y and X, respectively. Let I be an integer-indexed family of complex bilinear maps from U and Y to X. For every a in V, u in U, y in Y and m, q, r in ℤ, the input Borcherds A C B I requires three separately finite supports in the natural summation index k. The iterate applies I at m + q − k to A at r + k acting on (a, u), and to y, with weight binomial(m, k). The first ordered product applies B at m + r − k to a and I at q + k applied to (u, y). The second applies I at q + r − k to u and C at m + k applied to (a, y). Both ordered products carry the weight (−1)^k binomial(r, k), and the second also carries ε(r) = (−1)^r. The iterate sum equals the first ordered sum minus the second.

**Theorem 1.1 (Transport through three action intertwinings).**

Lean statement: `D5/S3/VertexAlgebra/Modules/MixedBorcherds.project`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/MixedBorcherds.project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Borcherds A C B I and complex-linear maps f from V′ to V, g from U′ to U, j from Y′ to Y and p from X to X′. The three intertwinings are g(A′_n(a, u)) = A_n(f(a), g(u)), j(C′_n(a, y)) = C_n(f(a), j(y)) and p(B_n(f(a), x)) = B′_n(a, p(x)), each for every integer n and the indicated inputs.

The projected family I′_n(u, y) = p(I_n(g(u), j(y))) satisfies Borcherds A′ C′ B′ I′. Each new summand is p applied to the matching original summand evaluated at (f(a), g(u), j(y)). Since p maps zero to zero, each support stays finite. Linearity carries the three finite sums and their difference to X′.

**Theorem 1.2 (Integer change of origin in the physical mode coset).**

Lean statement: `D5/S3/VertexAlgebra/Modules/MixedBorcherds.reindex_physical`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Modules/MixedBorcherds.reindex_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex-indexed family F, shiftedModes F σ reads the physical mode F(σ + n) at the integer label n. If that family satisfies Borcherds A C B, then shiftedModes F (σ + d) satisfies the same identity for every integer d. The two origins label the same physical coset because the new label n reads the old label d + n. Apply the original identity at (m, d + q, r). This aligns the three summand families pointwise with the new ones at (m, q, r), carrying all three finite supports and the sum identity. The actions A, C and B and the summation index k retain their original indices.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Modules/MixedBorcherds.project`
- Truth anchor: `D5/S3/VertexAlgebra/Modules/MixedBorcherds.reindex_physical`
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
