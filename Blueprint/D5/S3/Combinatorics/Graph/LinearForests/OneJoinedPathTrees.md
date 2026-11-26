# One-joined path trees

## Abstract

Classification of finite trees formed by one-joining arbitrarily labelled paths.

**Definition 1.1 (Labelled path blocks and their joins).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.LabeledChain`

*Formalization.* `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.LabeledChain` (`✓ std3`).

*Citation.* Daniel Pinzon; Daniel Pragel; Joshua Roberts (2025). *Algebraic Structures on Graphs Joined by Edges*. URL: <https://arxiv.org/abs/2409.02355v2>.

*Commentary.*

The block map partitions the input vertices into k + 1 nonempty fibres. Each fibre has a path-graph isomorphism and a freely chosen bijection from its labels. The only cross-block adjacencies join the largest label of block i to label 1 of block i + 1.

Lean numbers labels from zero. If p is a block's path coordinate map and l its label map, the relabelling permutation is l inverse composed with p. Conversely a permutation determines l by composing p with its inverse. For a local zero-based label j, add one and the sum of the preceding block orders to obtain its global label. This gives the successive right-label shifts in the cited definition.

**Theorem 1.2 (The spine-cut classification).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{Finite}\left(V\right)], (\operatorname{IsTree}\left(G\right)) \Rightarrow (\forall m \in Nat,\; ((m = 1) \lor (m = 2)) \Rightarrow (\forall b \in Bool,\; (\operatorname{OneJoined}\left(G, m, b\right)) \Leftrightarrow (\operatorname{SpineCut}\left(G, m, b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.oneJoined_iff_spineCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Pinzon; Daniel Pragel; Joshua Roberts; Zack Marshall; Olivia Strain (2026). *Monoid Representation of the Determinants of the Adjacency Matrices of 1-joined Path Graphs*. URL: <https://arxiv.org/abs/2611.34794v1>.

*Commentary.*

Let G be a finite simple tree. Its connectedness supplies a vertex. OneJoined means that G admits a labelled chain with each block of order at least m. When b is true it requires at least one join. When b is false it permits one block.

SpineCut means that some simple path in the input tree carries a set C of edges. Write d for the degree in G and c for incidence in C. For minimum order two, the conditions at every vertex are c ≤ 1 and 1 ≤ d − c ≤ 2. For minimum order one, they are 0 ≤ d − c ≤ 2 and c = 2 implies d = 2. On a simple path there are at most two incidences at any vertex. When b is true, C must be nonempty.

The two-vertex minimum is the original operand domain. Section 3 discusses the singleton, whose one vertex carries both joining labels. The registered minimum-one extension and the zero-join closures are included in the same equivalence.

Forward, the actual interblock joins are carried by a simple tree path. After deleting them the residual degree is the intrablock path degree. The original degree is exactly residual degree plus cut incidence. Reverse, order the residual components along the projected path and assign the joining labels in each component.

**Theorem 1.3 (The actual joins certify a spine cut).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{Finite}\left(V\right)], (\operatorname{IsTree}\left(G\right)) \Rightarrow (\forall k \in Nat,\; \forall m \in Nat,\; \forall L \in \operatorname{LabeledChain}\left(G, k\right),\; (\forall i \in \operatorname{Fin}\left(k + 1\right),\; m \le \operatorname{length}\left(L, i\right) + 1) \Rightarrow ((\operatorname{OnSpine}\left(G, \operatorname{joinEdges}\left(L\right)\right)) \land (((0 < k) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{joinEdges}\left(L\right)\right))) \land (\forall x \in V,\; \operatorname{ResidualVertexCondition}\left(G, \operatorname{joinEdges}\left(L\right), m, x\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.joinEdges_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Pinzon; Daniel Pragel; Joshua Roberts; Zack Marshall; Olivia Strain (2026). *Monoid Representation of the Determinants of the Adjacency Matrices of 1-joined Path Graphs*. URL: <https://arxiv.org/abs/2611.34794v1>.

*Commentary.*

For a given labelled chain, joinEdges consists of its actual interblock edges. The path from the first block to the last must cross each consecutive boundary. Uniqueness of the crossing edge puts every join on that path.

**Theorem 1.4 (Exact reconstruction of a prescribed cut).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall [\operatorname{Finite}\left(V\right)], (\operatorname{IsTree}\left(G\right)) \Rightarrow (\forall m \in Nat,\; ((m = 1) \lor (m = 2)) \Rightarrow (\forall C \in \operatorname{Set}\left(\operatorname{Sym2}\left(V\right)\right),\; ((\operatorname{OnSpine}\left(G, C\right)) \land (\forall x \in V,\; \operatorname{ResidualVertexCondition}\left(G, C, m, x\right))) \Rightarrow (\exists k \in Nat,\; \exists L \in \operatorname{LabeledChain}\left(G, k\right),\; (\operatorname{joinEdges}\left(L\right) = C) \land (((0 < k) \Leftrightarrow (\operatorname{Nonempty}\left(C\right))) \land (\forall i \in \operatorname{Fin}\left(k + 1\right),\; m \le \operatorname{length}\left(L, i\right) + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.realizes_spine_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Pinzon; Daniel Pragel; Joshua Roberts; Zack Marshall; Olivia Strain (2026). *Monoid Representation of the Determinants of the Adjacency Matrices of 1-joined Path Graphs*. URL: <https://arxiv.org/abs/2611.34794v1>.

*Commentary.*

For every qualifying C, each block is exactly a component of the graph after deleting C, and the crossing edges are exactly C. The number k counts joins. It is positive exactly when C is nonempty. The residual degree condition is equivalent to the original criterion by the exact degree decomposition.

Incoming and outgoing endpoints in a block determine labels 1 and the largest label. In a nonsingleton the local incidence test makes the two prescribed vertices distinct whenever both are present. The singleton uses its only label for both.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.LabeledChain`
- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.joinEdges_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.oneJoined_iff_spineCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.realizes_spine_cut`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts](TreePathCuts.md)
