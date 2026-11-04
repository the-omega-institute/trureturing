# Enumeration prerequisites for the original identity

## Abstract

An explicit finite equivalence counts labelled periodic avoiding words by transfer traces.

Write P(N) for the subtype of labels : Fin N → Bool satisfying AndrasfaiLanguage.PeriodicAvoidance (List.ofFn labels). PeriodicAvoidance excludes the complete forbidden family from every finite repetition of the word. Positions have a fixed labelled origin. ClosedRun(N) retains a Boolean labelling and a live starting state in Fin 4 whose Fin.castSucc image closes under the original five-state DFA evaluation.

**Definition 1.1 (The finite equivalence of words and closed lifts).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.periodicWordEquivClosedRun`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.periodicWordEquivClosedRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N with N mod 3 nonzero, periodicWordEquivClosedRun N is an equivalence P(N) ≃ ClosedRun(N). The forgetful map sends a closed run to its unchanged labels. The existing exists_unique_closed_run theorem proves periodic avoidance and uniqueness. Conversely, a nonrejecting Fin 5 state has value below four and hence has a unique preimage in Fin 4 under Fin.castSucc. Equality of labels and uniqueness of the closed starting state prove injectivity; this preimage construction proves surjectivity.

**Theorem 1.2 (Uniform periodic-word cardinality).**

$$\forall (N : \mathbb{N}), \left(0 < N \land \operatorname{mod}\left(N, 3\right) \ne 0\right) \Rightarrow (\operatorname{card}\left(\operatorname{P}\left(N\right)\right) : \mathbb{Q}) = \operatorname{trace}\left(\operatorname{transfer}^{N}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.periodic_word_card_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite equivalence transports cardinality to the existing AndrasfaiCounting.closed_run_card_eq_trace theorem. The latter already preserves both Boolean labels on a shared transition. This theorem counts words only; identifying those words with actual original-host visible subsets is a separate obligation. At lengths 3m+2 with m positive, applying this count to the original graph requires a separate equivalence between its actual visible subsets and these periodic words.

The periodic-word count is a prerequisite for the original all-labelled-subset generating identity. No graph of index zero, quotient by rotations, maximality condition, independent-set substitution or eventual-only interpretation is introduced. The full original graph-count correspondence and formal power-series identity remain outside these results.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.periodicWordEquivClosedRun`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.periodic_word_card_eq_trace`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiCounting](AndrasfaiCounting.md)
