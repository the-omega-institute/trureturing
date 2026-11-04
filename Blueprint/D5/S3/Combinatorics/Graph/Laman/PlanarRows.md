# PlanarRows

## Abstract

Independent rows, perturbations along a moment curve, and all induced-subset sparsity bounds.

**Theorem 1.1 (The row space as a span).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.range_dualMap_eq_span_image_dualBasis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.range_dualMap_eq_span_image_dualBasis` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For a commutative semiring, real or otherwise, modules M,N, a basis b of N with a finite decidable index type, and a linear map f from M to N, the range of the dual map is the span of f.dualMap applied to the dual basis.

**Theorem 1.2 (Evaluating the determinant polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.eval_det_X_add_C`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.eval_det_X_add_C` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any commutative ring, finite decidable matrix index type, square matrices A,B and scalar t, evaluating det(X times A.map(C)+B.map(C)) at t gives det(t times A+B).

**Theorem 1.3 (The moment-curve difference determinant).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.det_powerDifferences`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.det_powerDifferences` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every commutative ring, natural n and vector v indexed by Fin(n+1), the determinant of the n by n matrix with entry v(i+1)^(j+1)-v(0)^(j+1) equals the product of v(j)-v(i) over all i<j. A cofactor expansion of the Vandermonde evaluation matrix gives the identity, including n=0.

**Definition 1.4 (Row independence).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.EdgeSetRowIndependent`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/PlanarRows.EdgeSetRowIndependent` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every V,d,G,p and set I of actual edges of G, row independence means linear independence of the real-valued velocity functionals indexed by I.

**Definition 1.5 (Rows as dual vectors).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph and placement, rigidityRow p e is the real linear functional obtained by composing the rigidity map with the coordinate projection at the actual edge e.

**Theorem 1.6 (The function and dual formulations agree).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.edgeSetRowIndependent_iff_linearIndepOn_rigidityRow` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph, placement and set of actual edges, linear independence of their velocity functions is equivalent to linear independence of the corresponding dual vectors.

**Theorem 1.7 (Factoring a lifted edge row).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow_lift_eq_funLeft_dualMap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow_lift_eq_funLeft_dualMap` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any map phi from V to W, graphs Gprime,H, compatible placements pprime,pext with pext(phi(v))=pprime(v), and an actual Gprime edge whose mapped unordered pair is an H edge, the H row equals the Gprime row pulled back through restriction of velocities along phi. Injectivity of phi is not a premise.

**Theorem 1.8 (Pulling independence back to an induced graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.linearIndependent_rigidityRow_of_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.linearIndependent_rigidityRow_of_lift` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any phi, compatible placements, arbitrary indexing family of Gprime edges and proofs that their lifts are H edges, linear independence of the lifted H rows implies linear independence of the original Gprime rows. Factoring through the dual of velocity restriction proves the implication.

**Theorem 1.9 (Row span and transpose range).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.span_range_rigidityRow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.span_range_rigidityRow` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any graph with finitely many edges and any real placement, the span of all rigidity rows equals the range of the rigidity map dual.

**Theorem 1.10 (Rank upper bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityMap_finrank_range_le_of_affinelySpanning`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityMap_finrank_range_le_of_affinelySpanning` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite enumeration of V and placement p affinely spanning the real d-dimensional Euclidean space, rank(RigidityMap)+d(d+1)/2<=d card(V). The trivial-motion kernel lower bound and rank-nullity give the inequality.

**Theorem 1.11 (Selecting an independent edge set).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite enumeration of V, graph G and planar placement p with 2 card(V)<=rank(RigidityMap)+3, there is a set I of actual G edges of cardinality 2 card(V)-3 whose rows at p are independent. Extend an independent subset to a spanning row family, identify its cardinality with the row rank, and take a subset of the required size.

**Theorem 1.12 (Affine spanning while preserving an open property).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_affinelySpanning_of_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_affinelySpanning_of_eventually` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite V, dimension d, placement pzero and property P holding throughout some neighborhood of pzero, there exists p satisfying P such that its restriction to every vertex set S with card(S)>=d+1 affinely spans the whole Euclidean space. Assign distinct real parameters to the vertices and perturb along the moment curve. For each injective (d+1)-tuple, a determinant polynomial has nonzero top coefficient, so only finitely many perturbation values fail. A finite union of those exceptional sets leaves a value in the required neighborhood.

**Theorem 1.13 (Every induced planar sparsity bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.isSparse_of_edgeSetRowIndependent_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarRows.isSparse_of_edgeSetRowIndependent_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any vertex type, graph G, planar placement p affinely spanning on every vertex subset of cardinality at least three, and row-independent set I of actual G edges, the graph fromEdgeSet(image val I) is (2,3)-sparse. For a two-vertex subset, simplicity gives at most one edge. For every larger finite subset, factor the lifted rows through velocity restriction, retain independence, and combine their number with the restricted rigidity rank upper bound. The conclusion quantifies over every eligible finite subset.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.EdgeSetRowIndependent`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.det_powerDifferences`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.eval_det_X_add_C`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_affinelySpanning_of_eventually`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.isSparse_of_edgeSetRowIndependent_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.linearIndependent_rigidityRow_of_lift`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.range_dualMap_eq_span_image_dualBasis`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityMap_finrank_range_le_of_affinelySpanning`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.rigidityRow_lift_eq_funLeft_dualMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarRows.span_range_rigidityRow`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/TrivialMotions](TrivialMotions.md)
