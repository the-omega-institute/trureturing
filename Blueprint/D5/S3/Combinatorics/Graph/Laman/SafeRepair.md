# Safe nonedge repair by tight blockers

## Abstract

Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.

**Theorem 1.1 (The three-neighbor obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.no_isTightOn_excluding_three_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.no_isTightOn_excluding_three_neighbors` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

In a (2,3)-sparse graph, no tight set excluding v contains three distinct neighbors a,b,c of v. Inserting v adds one vertex and at least three distinct actual edges, contradicting sparsity.

**Theorem 1.2 (One blocked pair).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_one_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_one_pair` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A tight blocker for one neighbor pair, together with actual edges for the other two pairs, produces a tight set containing all three neighbors and excluding the removed vertex. The three-neighbor obstruction rules this out. Every adjacency and membership assumption in the Lean statement is used in that construction.

**Theorem 1.3 (Two blocked pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_two_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_two_pair` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Two tight pair blockers and the actual remaining pair edge cannot coexist around three distinct neighbors. If their intersection is large, tight union applies. In the remaining singleton-intersection case, the third pair edge supplies the missing bonus edge.

**Theorem 1.4 (Three blocked pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_three_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_three_pair` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Three tight pair blockers cannot coexist around three distinct neighbors. Pairwise intersections and tight union or bonus-edge closure construct a forbidden tight set containing all three neighbors. The small-intersection cases are handled within the same actual finite sets.

**Theorem 1.5 (The pair dispatcher).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.False_of_pairwise_blocker_or_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.False_of_pairwise_blocker_or_edge` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For each of the three neighbor pairs, assume either the actual pair edge exists or a tight blocker excludes the removed vertex and contains that pair. Exhausting the edge/blocker choices gives a contradiction using the one-, two-, or three-blocker construction and the all-edges obstruction.

**Theorem 1.6 (Extracting a genuine tight blocker).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.typeII_reverse_blocker`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.typeII_reverse_blocker` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For distinct nonadjacent old neighbors x,y of v, form the induced graph after deleting v and add the bridge xy. If that graph fails (2,3)-sparsity, a violating finite subset transports back to a tight subset of the original graph containing x and y and excluding v. Deleting the one added bridge and squeezing with the original sparsity bound establishes exact tightness.

**Theorem 1.7 (A safe reverse move).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.exists_typeI_or_typeII_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SafeRepair.exists_typeI_or_typeII_reverse` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Every finite (2,3)-sparse graph with an edge has a degree-one, degree-two, or degree-three reverse decomposition. In the degree-three case there are three distinct old neighbors and a genuinely nonadjacent pair whose bridge can safely be inserted after vertex deletion. If every nonedge pair were unsafe, blocker extraction and the pair dispatcher would contradict sparsity. This supplies a safe repair without a decomposition hypothesis.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.False_of_pairwise_blocker_or_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_one_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_three_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.contradiction_two_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.exists_typeI_or_typeII_reverse`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.no_isTightOn_excluding_three_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SafeRepair.typeII_reverse_blocker`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/SparseSets](SparseSets.md)
