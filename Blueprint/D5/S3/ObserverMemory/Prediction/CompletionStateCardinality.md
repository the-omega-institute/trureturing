# Completion State Cardinality

## Abstract

A surjective refinement map makes completed-state cardinality monotone.

**Theorem 1.1 (Completion state cardinality is monotone under refinement).**

$$\forall Fine, Coarse,\ [\operatorname{Fintype} Fine] [\operatorname{Fintype} Coarse],\ forget: Fine \to Coarse,\ \operatorname{Surjective}\left(forget\right) \Rightarrow \operatorname{card}(Coarse) \leq \operatorname{card}(Fine).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/CompletionStateCardinality.completion_state_cardinality_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Fine and Coarse be finite completed-state carriers. If a forgetting map sends Fine surjectively onto Coarse, then the number of coarse states is at most the number of refined states.

Pinned Mathlib and Loogle returned the exact declaration Fintype.card_le_of_surjective, which is imported and applied directly. Repository searches found uses inside entropy and fusion bounds but no standalone completed-state refinement declaration. LeanSearch returned HTTP 405 and 422 and supplied no additional result.

The theorem records only the finite cardinal consequence of the surjective refinement map. It assumes no entropy, probability, metric, dynamics, or strict decrease.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/CompletionStateCardinality.completion_state_cardinality_mono`
