# Rooted decomposition and the connected minus-four family

## Abstract

A rooted-component decomposition gives a general weighted domination identity. Its checked application to the published graph, followed by support replication, gives connected graphs of unbounded order with root minus four.

**Definition 1.1 (Ordinary domination evaluation).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.evaluation`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.evaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite vertex type V with Fintype and DecidableEq instances, evaluation(H,x) sums x to the cardinality of S over all ordinary dominating subsets S of H, each counted once. The subsets need not be connected.

**Definition 1.2 (Arbitrary finite rooted decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.Decomposition`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.Decomposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains natural numbers n, k and m, a size for every branch in Fin m, a graph on Fin n with decidable adjacency, and a vertex equivalence from Fin k disjoint union the dependent branch types. Each branch has a root, an internal leaf and a finite set of incident core vertices. The leaf has exactly the root as its global neighbor, the root is adjacent to that leaf, every nonroot branch vertex has only internal neighbors, and every core vertex has exactly its internal core neighbors and the incident branch roots as neighbors. All dimensions are arbitrary; no size bound, weight or source edge list occurs in this interface. The local graph laws are explicit input obligations.

**Definition 1.3 (The induced branch graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.branchGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.branchGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For decomposition d and branch i, branchGraph(d,i) pulls d.graph back along the branch part of d.labels.

**Definition 1.4 (Internal branch domination).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.localDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.localDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every branch vertex v, either v is in S or there exists w in S adjacent to v in branchGraph(d,i). This is internal ordinary domination, including domination of the branch root.

**Definition 1.5 (Root-conditioned weighted messages).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.message`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.message` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary decomposition d, integer x, branch i and Boolean b, message(d,x,i,b) sums x to the cardinality of S over all subsets S of branch i that internally dominate and whose root membership decides to b. The definition contains no precomputed message values.

**Definition 1.6 (Coverage by core and selected roots).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.coreCovered`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.coreCovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For core subset Z and root-index subset A, every core vertex is selected in Z, adjacent to a core vertex selected in Z, or incident to a root indexed by A.

**Definition 1.7 (Core evaluation of arbitrary message data).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.tableEvaluation`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.tableEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary table mapping each branch and Boolean root state to an integer, tableEvaluation(d,x,table) sums over all core subsets Z and root-index subsets A. A covered pair contributes x to card(Z) times the product over i of table(i,decide(i in A)); an uncovered pair contributes zero.

**Definition 1.8 (The exact branch-message expression).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.stateEvaluation`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.stateEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the same core expression with table(i,b) equal to message(d,x,i,b). Every core subset and root-state subset occurs once.

**Theorem 1.9 (General weighted restriction and reassembly).**

$$\forall (d:Decomposition), \forall (x:\mathbb{Z}), \operatorname{evaluation}\left(\operatorname{graph}\left(d\right), x\right) = \operatorname{stateEvaluation}\left(d, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.reassembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani; Max Griswold (2026). *On the Integer Domination Root Conjecture*. DOI: [10.48550/arXiv.2608.00109](https://doi.org/10.48550/arXiv.2608.00109). URL: <https://arxiv.org/abs/2608.00109v1>.

*Commentary.*

Restrict a subset along the vertex equivalence to a core subset and one local subset per branch. Disjoint assembly and restriction are inverse, and assembly cardinality is the core cardinality plus the sum of local cardinalities. Domination of each branch leaf forces internal domination of its root, while the nonroot-neighbor law handles all other branch vertices. The core-neighbor law gives exactly coreCovered. This yields a bijection between ordinary dominating sets and covered core/root states with internally dominating branch choices. Transport the cardinality weights along this bijection. The pinned Fintype.prod_sum identity factors the independent branch choices, giving exactly stateEvaluation for every d and integer x.

**Theorem 1.10 (Soundness of the message checker).**

$$\forall (d:Decomposition), \forall (x:\mathbb{Z}), \forall (table:\operatorname{Fin}\left(\operatorname{m}\left(d\right)\right) \to Bool \to \mathbb{Z}), (\forall (i:\operatorname{Fin}\left(\operatorname{m}\left(d\right)\right)), \forall (b:Bool), \operatorname{message}\left(d, x, i, b\right) = \operatorname{table}\left(i, b\right)) \Rightarrow ((\operatorname{tableEvaluation}\left(d, x, table\right) = 0) \Rightarrow (\operatorname{evaluation}\left(\operatorname{graph}\left(d\right), x\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.zero_of_messages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani; Max Griswold (2026). *On the Integer Domination Root Conjecture*. DOI: [10.48550/arXiv.2608.00109](https://doi.org/10.48550/arXiv.2608.00109). URL: <https://arxiv.org/abs/2608.00109v1>.

*Commentary.*

The inputs are an arbitrary d, integer x and table. The first premise requires every entry to equal the exact message for that same d, weight and root state; the second requires the covered core expression for the same table to vanish. Substitute the first premise into the general reassembly identity and then use the second. Both premises are checked in the live application below. This theorem does not assume the graph's evaluation is zero.

**Theorem 1.11 (The complete connected unbounded-order event).**

$$\forall (N:\mathbb{N}), \exists (n:\mathbb{N}), (N < n) \land (\exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Connected}\left(G\right)) \land (\sum_{S\in\operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result` (`✓ std3`). ∎

*Resolves.* `Problems/alikhani-griswold-2026-connected-minus-four-family` (proved) by `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alikhani-griswold-2026-connected-minus-four-family","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani; Max Griswold (2026). *On the Integer Domination Root Conjecture*. DOI: [10.48550/arXiv.2608.00109](https://doi.org/10.48550/arXiv.2608.00109). URL: <https://arxiv.org/abs/2608.00109v1>.

*Commentary.*

The application supplies the published 33-vertex graph with its actual 36 edges. Its core is the four-cycle on labels zero through three; branch sizes are 2,2,2,2,6,3,3,9. The vertex equivalence and all local graph laws are checked as input fields of this particular decomposition. At weight minus four, the selected-root message vector is 12,12,12,12,972,-36,-36,-20736 and the omitted-root vector is -4,-4,-4,-4,-1024,16,16,5888. The exact message equalities and covered core cancellation are kernel decisions passed directly to zero_of_messages. They are not retained as separate positive finite theorems. The original ConsecutiveCycleSumsGraph.connected_of_predecessor supplier proves base connectedness from the decreasing parent map on the full vertex set; the pinned induced-universe isomorphism transports its conclusion to the base graph. Vertex five has sole neighbor four. Use N+1 copies of the base, connect their supports four to a hub, and add one hub pendant. The existing replication equivalences and leaf domination identity give evaluation x(x+2) times the base evaluation to the power N+1. At minus four this is zero, and copied paths through the support prove connectedness. The order is 33(N+1)+2, which exceeds N. A finite vertex equivalence gives the exact graph on Fin n.

The source question is Section 4 item 3 of Alikhani and Griswold, arXiv:2608.00109v1. The base graph and its reported finite root are prior art. The graph data and proofs here are independently written with attribution. The general weighted composition and its family application are repository derivations, without a worldwide priority claim. The conclusion uses ordinary domination and requires only graph connectedness; it imposes no degree, cyclomatic number or connected-subset condition. No smallest-order or other-root claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.Decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.branchGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.coreCovered`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.evaluation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.localDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.message`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.reassembly`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.stateEvaluation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.tableEvaluation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.zero_of_messages`
- Dependency: [D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsGraph](../../CycleSums/ConsecutiveCycleSumsGraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication](../LocalDominatingStemBoundReplication.md)
