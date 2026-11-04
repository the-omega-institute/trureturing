# Counting based labelled closed runs

## Abstract

Boolean labelled closed runs of the original four-state partial automaton are counted by powers of its transfer matrix, uniformly at every positive length.

**Definition 1.1 (The live-state embedding).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.liveState`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.liveState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map liveState : Fin 4 → Fin 5 is Fin.castSucc. It sends 0,1,2,3 to the same four values in the original DFA; state 4 is the absorbing rejection state.

**Definition 1.2 (Based Boolean labelled closed runs).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.ClosedRun`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.ClosedRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N, ClosedRun N is the subtype of pairs (labels,q), with labels : Fin N → Bool and q : Fin 4, satisfying machine.evalFrom (liveState q) (List.ofFn labels) = liveState q. The positions and initial state are labelled; there is no quotient by rotations. Distinct Boolean labels remain distinct even when their transitions have identical source and target.

**Theorem 1.3 (The uniform cardinality and trace identity).**

$$\forall (N : \mathbb{N}), 0 < N \Rightarrow (\operatorname{card}\left(\operatorname{ClosedRun}\left(N\right)\right) : \mathbb{Q}) = \operatorname{trace}\left(\operatorname{transfer}^{N}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.closed_run_card_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive N the rational coercion of the number of ClosedRun N equals tr(transfer^N). The transfer matrix is the original matrix with rows (1,1,0,0), (1,0,1,0), (0,0,0,1), (0,2,0,0). Its multiplicity-two entry counts both Boolean labels on the transition from state 3 to state 1. Splitting a word at its first letter and summing over live intermediate states expresses its endpoint indicator as a path-weight sum. Rejection is absorbing and contributes zero to every live endpoint. The generic integer sum_pathWeight theorem from CycleItalianDominationRecurrence identifies the resulting sum with a matrix power. Summing diagonal entries closes the runs, and matrix coefficient-map lemmas transport the integer identity to Q.

The theorem concerns actual evaluation of the existing DFA and the independently specified transfer matrix. Identifying these runs with visible subsets of an Andrasfai graph, and the graph-index-one correction, require separate counting correspondences.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.ClosedRun`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.closed_run_card_eq_trace`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting.liveState`
- Dependency: [D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence](../CycleItalianDominationRecurrence.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage](AndrasfaiLanguage.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer](AndrasfaiTransfer.md)
