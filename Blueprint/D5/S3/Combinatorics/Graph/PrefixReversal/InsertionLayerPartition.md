# Complete Insertion-Layer Partition

## Abstract

Over a directed base distinct from its reverse, every actual configuration in the complete insertion layer belongs to exactly one independently specified positive directed child domain.

Configuration(m) is the permutation type of Fin(m+1). The label v(i) occupies position i, and configurationCycle(v) is its full tuple modulo rotation. Cycle identifies rotations and retains the direction of the list. For a finite label set S, erase(S,C) restricts the actual directed circle C to labels outside S. Deletion of x restricts to labels different from x.

Layer(S,P,v) means erase(S,configurationCycle(v)) equals P or reverse(P). ChildCircle(S,x,P) is the subtype of directed circles D that have no repeated labels, contain a label y exactly when y is outside S, satisfy erase(S,D)=D, and satisfy delete(x,D)=P. The deletion equality fixes the positive direction of the child. For such a subtype element D, ChildDomain(D,v) means Layer(S,D.val,v). These objects are defined from complete native configurations and actual deletion, before choosing any path or graph.

**Theorem 1.1 (Every Full Residual Has an Actual Native Supplier).**

$$\forall m \in \mathrm{Nat},\; \forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall D \in \mathrm{Cycle}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall hn \in \mathrm{Nodup}\left(D\right),\; \forall hm \in \left(\forall y \in \mathrm{Fin}\left(m + 1\right),\; y \in D \Leftrightarrow \left(\neg y \in S\right)\right),\; \exists v \in \mathrm{Configuration}\left(m\right),\; \mathrm{erase}\left(S, \mathrm{configurationCycle}\left(v\right)\right) = D$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.nativeResidual_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, every finite selected set S and every directed residual D on Fin(m+1), assume D has no repeated labels and y belongs to D exactly when y is outside S. There is an actual Configuration(m) whose restriction outside S is precisely D. Choose a representative list of D and prepend the labels of S once. The two lists are disjoint; their concatenation contains every native label exactly once. Its list get-equivalence gives a permutation of Fin(m+1). Filtering out S recovers the complete original representative of D.

**Theorem 1.2 (The Complete Independent Child Partition).**

$$\forall m \in \mathrm{Nat},\; \forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall x \in \mathrm{Fin}\left(m + 1\right),\; \forall P \in \mathrm{Cycle}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall hP \in P \ne \mathrm{reverse}\left(P\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{Layer}\left(\mathrm{insert}\left(x, S\right), P, v\right) \Leftrightarrow \left(\exists D \in \mathrm{ChildCircle}\left(S, x, P\right),\; \mathrm{ChildDomain}\left(D, v\right) \land \left(\forall E \in \mathrm{ChildCircle}\left(S, x, P\right),\; (\mathrm{ChildDomain}\left(E, v\right)) \Rightarrow (E = D)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.insertionLayer_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, selected set S, label x, directed base P different from its reverse, and actual native configuration v, membership in Layer(insert(x,S),P) is equivalent to membership in exactly one independently admissible ChildCircle(S,x,P) supplier domain. Erase S from the actual configuration. Deleting x from that residual gives P or reverse(P); reverse the whole residual in the latter case to obtain a positive child. Its support is exactly the labels outside S and it has no duplicates. Two positive children sharing a native vertex must coincide: opposite residual orientations would imply P=reverse(P). The formula expresses the unique existential as existence together with equality of every other child whose full independent supplier domain contains the same v.

**Definition 1.3 (The Actual Partition Equivalence).**

$$\forall m \in \mathrm{Nat},\; \forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall x \in \mathrm{Fin}\left(m + 1\right),\; \forall P \in \mathrm{Cycle}\left(\mathrm{Fin}\left(m + 1\right)\right),\; \forall hP \in P \ne \mathrm{reverse}\left(P\right),\; \mathrm{insertionLayerEquiv}\left(hP\right): \mathrm{Equiv}\left(\{v: \mathrm{Configuration}\left(m\right) \mid \mathrm{Layer}\left(\mathrm{insert}\left(x, S\right), P, v\right)\}, (\Sigma D: \mathrm{ChildCircle}\left(S, x, P\right), \{v: \mathrm{Configuration}\left(m\right) \mid \mathrm{ChildDomain}\left(D, v\right)\})\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.insertionLayerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a directed base P distinct from its reverse, insertionLayerEquiv(hP) is an equivalence from the entire native parent layer to the dependent sum of the independently defined child domains. The forward map chooses the unique positive child of the actual native vertex and keeps that vertex. The inverse forgets the child index and keeps the vertex. The partition proves the two inverse laws. The displayed brace expressions are subtypes, and Sigma is the dependent sum over ChildCircle. No graph, path, Hamilton cycle or recursive spanning construction is an input or conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.insertionLayerEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.insertionLayer_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition.nativeResidual_surjective`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](../PrefixReversalZeroStarComplement.md)
