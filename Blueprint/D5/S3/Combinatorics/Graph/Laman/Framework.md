# Frameworks and rigidity rows

## Abstract

Real finite-dimensional frameworks and their edge rigidity maps.

**Definition 1.1 (Framework placements).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.Framework`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.Framework` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A framework on V in dimension d is a placement V → EuclideanSpace ℝ (Fin d).

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

Evaluating edgeRow p u v at x gives ⟪p u − p v, x u − x v⟫ over ℝ.

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

At an explicit edge s(u,v), the rigidity map component is the inner product ⟪p u − p v, p' u − p' v⟫ over ℝ.

**Definition 1.7 (Infinitesimal rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A finite graph is infinitesimally rigid at p when the real kernel of its rigidity map has finrank at most d(d+1)/2.

**Definition 1.8 (Injectively generically rigid graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A finite graph is injectively generically rigid in dimension d when it has an infinitesimally rigid placement that is injective.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.Framework`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.IsGenericallyRigidInj`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.IsInfinitesimallyRigid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.RigidityMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.edgeRow_symm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Framework.rigidityMap_apply`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/SparseSets](SparseSets.md)
