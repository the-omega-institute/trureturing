# Eight component messages and the four-cycle cancellation

## Abstract

The component calculation uses subsets of at most nine vertices and a separate four-core/eight-root expression.

**Definition 1.1 (Sizes of the actual components).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchSize`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After deleting core vertices 0,1,2,3, the consecutive component sizes are 2,2,2,2,6,3,3,9. Their starting labels are 4,6,8,10,12,18,21,24.

**Definition 1.2 (Starting labels).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchStart`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each component interval begins at the specified published root label. Together the intervals contain exactly labels 4 through 32.

**Definition 1.3 (Local labels mapped to the source).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchLabel`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local vertex v in component i is sent to branchStart(i)+v in Fin 33. A finite bound proves this label is in range.

**Definition 1.4 (Actual internal component edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph of a component is the comap of the actual source graph along branchLabel. Its edges come from the published edge list, including the nine-vertex component at root 24.

**Definition 1.5 (The component root).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.root`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first local label, zero, is the component root in each of the eight intervals.

**Definition 1.6 (Ordinary domination internal to a component).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.localDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.localDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every local vertex belongs to S or has a branchGraph neighbor in S. All vertices, including the root, are required to be internally dominated.

**Definition 1.7 (Root-conditioned weighted sums).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.message`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.message` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each component and Boolean b, sum the cardinality weight at minus four over its internally dominating subsets whose root membership is b. Each sum ranges over at most 512 subsets. The root-selected values are 12,12,12,12,972,minus 36,minus 36,minus 20736. The root-omitted values are minus 4,minus 4,minus 4,minus 4,minus 1024,16,16,5888. These finite sums are computed by Lean kernel decision, using no native certificate.

**Definition 1.8 (The exact core-to-root incidences).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.rootNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.rootNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root neighbor sets in the core are {0},{2},{2},{2},{0,1},{1,2},{2,3},{3}, in component order.

**Definition 1.9 (Ordinary domination of the core).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.coreCovered`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.coreCovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A chosen core set Z and chosen root-index set A cover a core vertex when it belongs to Z, has a selected core neighbor along an actual source edge, or is adjacent to a selected component root.

**Definition 1.10 (The finite core expression).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.stateEvaluation`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.stateEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all 16 core subsets Z and all 256 root selections A, retain the term exactly when coreCovered holds. Multiply the core cardinality weight by the eight matching component messages. The product-sum expression has 4096 core/root cases; it does not enumerate all subsets of the 33-vertex graph.

**Theorem 1.11 (Reduction through the exact weighted bridge).**

$$(\operatorname{evaluation}\left(sourceGraph, (-4)\right) = stateEvaluation) \Rightarrow (\forall (N:\mathbb{N}), \exists (n:\mathbb{N}), (N < n) \land (\exists (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Connected}\left(G\right)) \land (\sum_{S\in\operatorname{domSets}\left(G\right)} (-4)^{\operatorname{card}\left(S\right)} = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.result_of_reassembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that evaluation(sourceGraph,minus four) equals stateEvaluation. Substitution of the kernel-verified local messages into this state expression gives zero by kernel finite decision. The source family reduction then gives connected graphs on Fin n of unbounded order with vanishing ordinary domination sum. The premise is the exact global restriction/reassembly bridge, including domination and cardinality weights. The conditional theorem does not supply that bridge.

Each component root has an internal leaf. Domination of that leaf forces either the root or its leaf to be selected, so external core help cannot enlarge the internally dominating family. MinusFourReassembly supplies the exact restriction/union correspondence: each source dominating set occurs once, and its cardinality is the sum of the core and component cardinalities. The conditional reduction separates this combinatorial bridge from the small finite arithmetic computations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchLabel`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchSize`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.branchStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.coreCovered`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.localDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.message`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.result_of_reassembly`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.root`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.rootNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.stateEvaluation`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/MinusFourFamily](MinusFourFamily.md)
