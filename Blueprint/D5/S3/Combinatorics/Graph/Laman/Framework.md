# Frameworks and rigidity rows

## Abstract

Real finite-dimensional frameworks and their edge rigidity maps.

**Definition 1.1 (Framework placements).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.Framework`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.Framework` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A framework on V in dimension d is a placement V to EuclideanSpace ℝ (Fin d).

**Definition 1.2 (An edge row).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

The row for an ordered pair u,v evaluates a motion x by the real inner product of the placement difference and motion difference.

**Theorem 1.3 (Edge-row evaluation).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Evaluating edgeRow p u v at x gives the real inner product of the two differences.

**Theorem 1.4 (Edge-row orientation symmetry).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Swapping the endpoints leaves the edge row unchanged because both differences change sign.

**Definition 1.5 (The rigidity map).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For a graph G and placement p, the rigidity map sends a motion to the family of edge-row values indexed by G.edgeSet.

**Theorem 1.6 (Rigidity-map evaluation).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

At an explicit edge s(u,v), the rigidity map component is the real inner product of placement and motion differences.

**Theorem 1.7 (Continuity of a rigidity component).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.continuous_rigidityMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.continuous_rigidityMap_apply` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For a fixed motion and edge, the rigidity-map component is continuous as a function of the placement.

**Theorem 1.8 (Kernel monotonicity under edge inclusion).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Adding graph edges can only shrink the rigidity-map kernel.

**Theorem 1.9 (Range rank bounded by edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_finrank_range_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_finrank_range_le` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For a finite vertex type, the real finrank of the rigidity-map range is at most the number of graph edges.

**Definition 1.10 (Infinitesimal rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A finite graph is infinitesimally rigid at p when the real kernel of its rigidity map has finrank at most d(d+1)/2.

**Definition 1.11 (Generic rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigid`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigid` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A finite graph is generically rigid in dimension d when some placement is infinitesimally rigid.

**Definition 1.12 (Injectively generically rigid graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A finite graph is injectively generically rigid in dimension d when it has an infinitesimally rigid placement that is injective.

**Theorem 1.13 (The two-vertex injective base).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

The complete graph on two vertices has an injectively generically rigid placement in every positive dimension.

**Theorem 1.14 (The two-vertex base).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigid` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

The complete graph on two vertices is generically rigid in every dimension.

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
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_finrank_range_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_ker_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.top_fin_two_isGenericallyRigidInj`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/SparseSets](SparseSets.md)
