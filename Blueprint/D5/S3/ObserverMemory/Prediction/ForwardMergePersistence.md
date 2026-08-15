# Forward Merge Persistence

## Abstract

States merged by a deterministic update have identical future states and readouts.

**Theorem 1.1 (Merged states have identical futures).**

$$\forall State, Output,\ F: State \to State, q: State \to Output,\ \forall y, y', t\in\mathbb{N},\ F^{t}(y) = F^{t}(y') \Rightarrow \forall r\in\mathbb{N},\ (F^{t+r}(y) = F^{t+r}(y') \land q(F^{t+r}(y)) = q(F^{t+r}(y'))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ForwardMergePersistence.forward_merge_persistence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a deterministic self-map, q any readout, and y and y' two states. If the states agree after t updates, then applying the same further r updates preserves their equality. Applying q to that common future state gives identical future readouts.

The pinned library search found Function.iterate_add_apply as the exact decomposition of an iterate at t+r; the proof imports and applies it. Loogle found that declaration by name but no theorem matching the full persistent-equality shape. LeanSearch returned nearby iterate and fixed-point lemmas, but no exact result. A repository search found no declaration with the same hypothesis and conclusion.

The theorem is general in the state and output types. It does not require finiteness or injectivity, and it makes no converse claim. A constant Boolean update supplies a checked witness in which two distinct initial states satisfy the merge hypothesis.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ForwardMergePersistence.forward_merge_persistence`
