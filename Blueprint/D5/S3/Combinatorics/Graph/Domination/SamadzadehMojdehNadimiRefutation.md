# Five paired coalition parts in the height-five binary tree

## Abstract

The perfect binary tree of height five has a paired coalition partition with five parts. Odd part sizes exclude paired domination of individual parts, while four explicit perfect matchings certify their unions. Thus its paired coalition number is at least five, contradicting the value three in Conjecture 1.

**Definition 1.1 (The perfect binary tree).**

$$\forall (h : \mathbb{N}), \operatorname{perfectBinaryTree}\left(h\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\operatorname{fun} (x : \operatorname{Fin}\left(2^{h + 1} - 1\right)) \mapsto (\operatorname{fun} (y : \operatorname{Fin}\left(2^{h + 1} - 1\right)) \mapsto (\operatorname{val}\left(y\right) + 1 = 2 \cdot (\operatorname{val}\left(x\right) + 1)) \lor (\operatorname{val}\left(y\right) + 1 = 2 \cdot (\operatorname{val}\left(x\right) + 1) + 1)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.perfectBinaryTree` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Section 4.2, p. 9: "A perfect binary tree is a binary tree in which all leaves have same distance to the root vertex." "Given a perfect binary tree T, we call the distance between root vertex and each leaf, height of T." "If T has height h, then we denote it by T(h)." The root has depth zero. The vertex i : Fin (2^(h+1) - 1) has heap label i.val+1. The two children of label r have labels 2r and 2r+1. SimpleGraph.fromRel symmetrizes this relation and excludes loops; the resulting tree has all leaves at depth h. Subtraction in the vertex count is natural subtraction.

**Definition 1.2 (Paired dominating sets).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), (\operatorname{IsPairedDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{SimpleGraph}.\operatorname{IsDominating}\left(G, S\right)) \land (\exists (M : G.\operatorname{Subgraph}), (M.\operatorname{verts} = S) \land (M.\operatorname{IsMatching})))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPairedDominating` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Section 1, p. 2: "A paired dominating set of a graph G = (V, E) is a dominating set S ⊆ V such that the induced subgraph G[S] contains a perfect matching." SimpleGraph.IsDominating says that every vertex belongs to S or has a neighbour in S. A subgraph M of G with M.verts = S and M.IsMatching has exactly one neighbour at every vertex in S, so it is a perfect matching in G[S]. The graph and set parameters range over an arbitrary vertex type.

**Definition 1.3 (Paired coalitions).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (A : \operatorname{Set}\left(V\right)), \forall (B : \operatorname{Set}\left(V\right)), (\operatorname{IsPairedCoalition}\left(G, A, B\right)) \Leftrightarrow ((\operatorname{Disjoint}\left(A, B\right)) \land ((\neg (\operatorname{IsPairedDominating}\left(G, A\right))) \land ((\neg (\operatorname{IsPairedDominating}\left(G, B\right))) \land (\operatorname{IsPairedDominating}\left(G, (A \cup B)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPairedCoalition` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Definition 1.1, p. 2: "A paired coalition in a graph G consists of two disjoint sets of vertices V₁ and V₂, neither of which is a paired dominating set but whose union V₁ ∪ V₂ is a paired dominating set." The sets A and B represent V₁ and V₂. All four requirements appear in the predicate.

**Definition 1.4 (Paired coalition partitions).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (pi : \operatorname{Finset}\left(\operatorname{Set}\left(V\right)\right)), (\operatorname{IsPCPartition}\left(G, pi\right)) \Leftrightarrow ((\forall (A : \operatorname{Set}\left(V\right)), (A \in pi) \Rightarrow (A.\operatorname{Nonempty})) \land (((pi : \operatorname{Set}\left(\operatorname{Set}\left(V\right)\right)).\operatorname{PairwiseDisjoint}\left(id\right)) \land ((\forall (v : V), \exists (A : \operatorname{Set}\left(V\right)), (A \in pi) \land (v \in A)) \land (\forall (A : \operatorname{Set}\left(V\right)), (A \in pi) \Rightarrow ((\neg (\operatorname{IsPairedDominating}\left(G, A\right))) \land (\exists (B : \operatorname{Set}\left(V\right)), (B \in pi) \land ((\neg (B = A)) \land (\operatorname{IsPairedCoalition}\left(G, A, B\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPCPartition` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Definition 1.2, p. 2: "A paired coalition partition, abbreviated pc-partition, in a graph G is a vertex partition π = {V₁, V₂, . . . , Vₖ} such that every set Vᵢ of π is not a paired dominating set but forms a paired coalition with another set Vⱼ in π." The finset π consists of nonempty, pairwise disjoint sets covering all vertices. Each member has a distinct partner in the same finset. Coercing π to a set preserves its members; id is the identity map on its sets.

**Definition 1.5 (The paired coalition number).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{pcNumber}\left(G\right) = \operatorname{sSup}\left(\{k : \mathbb{N} \mid \exists (pi : \operatorname{Finset}\left(\operatorname{Set}\left(V\right)\right)), (\operatorname{IsPCPartition}\left(G, pi\right)) \land (pi.\operatorname{card} = k)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.pcNumber` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Definition 1.2, p. 2: "The paired coalition number PC(G) equals the maximum order k of a pc-partition of G, and a pc-partition of G having order PC(G) is called a PC(G)-partition." The following paragraph says: "As we will see later, not every graph G admits a pc-partition. In such situations we will say that PC(G) = 0." The natural-number supremum is over attained finset cardinalities, with sSup of the empty set equal to zero. For a finite graph these cardinalities are bounded, so this is the stated maximum. No decidability or finiteness assumption is needed to form the expression.

**Definition 1.6 (Conjecture 1).**

$$(claim) \Leftrightarrow (\forall (h : \mathbb{N}), (1 \le h) \Rightarrow (\operatorname{pcNumber}\left(\operatorname{perfectBinaryTree}\left(h\right)\right) = (\operatorname{if} h = 2 \operatorname{then} 5 \operatorname{else} (\operatorname{if} \operatorname{Odd}\left(h\right) \operatorname{then} 3 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.claim` (`✓ std3`).

*Citation.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Conjecture 1, Section 4.2, p. 12: "If T(h) is a perfect binary tree with height h, then PC(T(h)) = 5 if h = 2; 3 if h is odd; 0 otherwise." The three alternatives are printed as a cases display. The statement ranges over every positive natural height h, with the height-two case tested first. In particular the odd-height clause gives PC(T(5)) = 3.

**Theorem 1.7 (The conjecture is false).**

$$\neg (\forall (h : \mathbb{N}), (1 \le h) \Rightarrow (\operatorname{pcNumber}\left(\operatorname{perfectBinaryTree}\left(h\right)\right) = (\operatorname{if} h = 2 \operatorname{then} 5 \operatorname{else} (\operatorname{if} \operatorname{Odd}\left(h\right) \operatorname{then} 3 \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi (2024). *Paired coalition in graphs*. DOI: [10.1080/09728600.2024.2389070](https://doi.org/10.1080/09728600.2024.2389070). URL: <https://arxiv.org/abs/2402.10842v4>.

*Commentary.*

Use heap labels 1 through 63, and R = {1,8,9,10,11,12,13,14,15}. Put A = ⋃ over r in R of {r,2r,2r+1}, and Bⱼ = {4r+j : r in R} for j = 0,1,2,3. These five disjoint sets cover all vertices and have sizes 27,9,9,9,9. A perfect matching has even vertex cardinality, so no individual part is paired dominating. A dominates the tree. For j = 0,1, match r to 2r+1 and 2r to 4r+j in each seven-vertex block; for j = 2,3, match r to 2r and 2r+1 to 4r+j. These matchings cover each A ∪ Bⱼ exactly. Hence each Bⱼ has partner A, and A has partner B₀. The resulting partition has order five. Its order belongs to the bounded set defining pcNumber, so 5 ≤ pcNumber (perfectBinaryTree 5), contradicting the conjectured value three. Only this height-five lower bound and the displayed negation are established here; the exact value and a uniform family remain separate questions. The same lower bound contradicts Lemma 4.10, p. 9, which states PC(T(h)) ≤ 4 for h ≥ 3. The authors' final remark on p. 12 seeks to exclude order four, which does not exclude order five. No conclusion is drawn here about the independent path, cycle or other tree results.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPCPartition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPairedCoalition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.IsPairedDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.pcNumber`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.perfectBinaryTree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
