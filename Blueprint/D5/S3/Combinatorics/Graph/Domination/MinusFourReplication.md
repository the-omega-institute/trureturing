# Weighted ordinary domination under hub replication

## Abstract

The hub and pendant choices give an exact generating evaluation for every finite graph and every copy count. Throughout, V is an arbitrary finite vertex type supplied with Fintype and DecidableEq instances.

**Definition 1.1 (Cardinality-weighted ordinary domination).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.evaluation`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.evaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph H and integer x, evaluation(H,x) is the sum of x raised to the cardinality of S over the existing finite family domSets(H). Ordinary domination means that every vertex is selected or has a selected neighbor. The selected subset itself need not be connected.

**Theorem 1.2 (The complete two-case weighted identity).**

$$\forall (H:\operatorname{SimpleGraph}\left(V\right)), \forall (U:\operatorname{Finset}\left(V\right)), \forall (r:\mathbb{N}), \forall (x:\mathbb{Z}), \operatorname{evaluation}\left(\operatorname{replicated}\left(H, U, r\right), x\right) = x \cdot (1 + x) \cdot (\sum_{S\in\operatorname{partialSets}\left(H, U\right)} x^{\operatorname{card}\left(S\right)})^{r} + x \cdot \operatorname{evaluation}\left(H, x\right)^{r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.replicated_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V, graph H, attachment set U, nonnegative copy count r and integer x, evaluation(replicated(H,U,r),x) equals x(1+x) times the r-th power of the weighted partial-family sum, plus x times evaluation(H,x) to the r-th power. The existing hubEquiv parametrizes the hub-containing sets by a pendant bit and one partial set per copy. The existing omittedEquiv parametrizes the other sets by one full dominating set per copy. These are disjoint exhaustive cases. In each inverse map, assemble_card adds the copy cardinalities and the two bits. Powers therefore multiply, and Fintype.sum_pow sums independent choices. This uses the actual configuration equivalences; a formula about average cardinalities alone would not suffice.

**Theorem 1.3 (An actual internal leaf closes the partial family).**

$$\forall (H:\operatorname{SimpleGraph}\left(V\right)), \forall (v:V), \forall (w:V), ((\operatorname{Leaf}\left(H, w\right)) \land (\operatorname{Adj}\left(H, w, v\right))) \Rightarrow (\forall (r:\mathbb{N}), \forall (x:\mathbb{Z}), \operatorname{evaluation}\left(\operatorname{replicated}\left(H, \left\{v\right\}, r\right), x\right) = x \cdot (x + 2) \cdot \operatorname{evaluation}\left(H, x\right)^{r})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.support_replication_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose w is a degree-one vertex of H adjacent to v. A set dominating outside the singleton v must dominate w. The existing leaf_dominated_iff forces w or v to be selected, so v is internally dominated too. Thus partialSets(H,{v}) equals domSets(H), and the weighted identity becomes x(x+2) times evaluation(H,x) to the r-th power. This statement holds also at r=0, when the construction consists of the hub and pendant.

**Theorem 1.4 (Paths through each copy support).**

$$\forall (H:\operatorname{SimpleGraph}\left(V\right)), \forall (v:V), \forall (r:\mathbb{N}), (\operatorname{Connected}\left(H\right)) \Rightarrow (\operatorname{Connected}\left(\operatorname{replicated}\left(H, \left\{v\right\}, r\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.support_replication_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any connected H, support v and nonnegative r, the replicated graph is connected. A copied vertex has an H-path to its own copy of v. That copy has an edge to the hub, and the pendant has its hub edge. Mapping the H-path through the copy embedding gives actual reachability. For zero copies the hub and pendant still form one connected edge.

At x equal to minus four the support identity is eight times the r-th power of the base evaluation. A zero base value gives zero whenever r is positive. For r=0 the value is eight, so positivity of the copy count is essential to a root-family application. The weighted factorization is a repository derivation from existing finite-family interfaces; it carries no claim of literature priority.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.evaluation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.replicated_evaluation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.support_replication_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.support_replication_evaluation`
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication](../LocalDominatingStemBoundReplication.md)
