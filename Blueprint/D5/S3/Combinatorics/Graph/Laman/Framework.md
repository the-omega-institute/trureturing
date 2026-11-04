# Framework

## Abstract

Real placements and true edge inner-product rigidity maps on arbitrary vertex types.

**Definition 1.1 (Real placements).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.Framework`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.Framework` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any vertex type V in any universe and natural dimension d, Framework V d is the function space V to EuclideanSpace over the real numbers indexed by Fin d. A placement may identify vertices.

**Theorem 1.2 (Dimension of the placement space).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.finrank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.finrank` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite enumeration of V, the real dimension of Framework V d is card(V) times d.

**Definition 1.3 (A linear edge row).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every placement p, vertices u,v and velocity x, edgeRow p u v evaluated at x is the real inner product of p(u)-p(v) with x(u)-x(v). The row is linear in x.

**Theorem 1.4 (Evaluation of a row).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every V,d,p,u,v,x, the edge-row evaluation is exactly the inner product of the two differences.

**Theorem 1.5 (Orientation independence).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every placement and endpoint pair, interchanging both endpoints leaves the row unchanged, since both differences change sign.

**Definition 1.6 (The rigidity map).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every simple graph G and placement p, RigidityMap is a real linear map from all vertex velocities to the family of row values indexed by the unordered edges of G. Orientation independence makes the unordered-edge definition well defined.

**Theorem 1.7 (An explicit edge component).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph, placement p, velocity x, and edge with endpoints u,v, its rigidity-map component is the real inner product of p(u)-p(v) with x(u)-x(v).

**Theorem 1.8 (Continuity in the placement).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.continuous_rigidityMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.continuous_rigidityMap_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Fix any graph, velocity and edge. The corresponding rigidity component is continuous in the placement for the product topology.

**Theorem 1.9 (Adding edges shrinks the kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every pair G<=Gprime of simple graphs on the same V and every placement, the rigidity kernel for Gprime is contained in that for G. With finite V, this gives monotonicity of the kernel-dimension bound and of existence of a rigid placement.

**Definition 1.10 (The finite-dimensional kernel condition).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For finite V, this predicate means that the real kernel dimension is at most d(d+1)/2. In the plane the bound is three. Affine spanning is a hypothesis of the trivial-motion dimension theorem, rather than a hypothesis of this definition.

**Definition 1.11 (Existence of a rigid placement).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigid`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigid` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For finite V, this predicate means that at least one placement satisfies the kernel bound. It carries no algebraic-independence or injectivity premise and does not assert a statement about every placement or about finite local motions. Adding edges preserves this property.

**Theorem 1.12 (Rigidity is open).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.eventually` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite V, graph G and placement p at which the kernel bound holds, that bound holds throughout some neighborhood of p. A nonzero maximal minor persists under continuous changes of the placement.

**Definition 1.13 (An injective witness for induction).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For finite V, the strengthened predicate asks for an injective placement satisfying the same kernel bound. Forgetting injectivity gives IsGenericallyRigid. Graph isomorphisms transport the placement and its velocities, preserving kernel dimension and injectivity.

**Theorem 1.14 (The two-vertex seed).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every natural d, the complete graph on Fin 2 has an injective rigid placement in dimension d+1. Put its vertices at zero and the first coordinate vector. The single nonzero row gives the required dimension bound. In dimension two this includes the two-vertex base case.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.Framework`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.continuous_rigidityMap_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.eventually`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.finrank`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/SparseSets](SparseSets.md)
