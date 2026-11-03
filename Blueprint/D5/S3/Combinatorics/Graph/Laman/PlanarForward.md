# PlanarForward

## Abstract

Every finite Laman graph has a real planar rigid placement, including the two-vertex case.

**Theorem 1.1 (From Laman counts to a rigid placement).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarForward.isGenericallyRigid_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarForward.isGenericallyRigid_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite vertex type V in any universe and every simple graph G with the Laman property, there exists a real planar placement p whose rigidity kernel has dimension at most three. No construction history is supplied. Strong induction on card(V) maintains the stronger existence of an injective rigid placement. At cardinality two the graph is complete. Above two, the reverse decomposition supplies a degree-two deletion or degree-three deletion with an actual safe bridge edge. The smaller Laman graph is rigid by induction; geometric Type I or Type II preservation and the exact reconstruction isomorphism recover G. Tightness excludes cardinalities zero and one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarForward.isGenericallyRigid_two`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/HennebergRigidity](HennebergRigidity.md)
