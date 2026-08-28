# Prediction Partition Stability

## Abstract

A prediction partition unchanged by one extra readout is unchanged at every depth.

**Theorem 1.1 (A one-step stable prediction partition is permanently stable).**

$$\forall Y, O: \operatorname{Type},\ F: Y \to Y, q: Y \to O, m\in \mathbb{N},\ (\forall y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m+1, y\right) = \operatorname{ReadoutWord}\left(F, q, m+1, y'\right)) \implies \left((\forall y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \Rightarrow \operatorname{ReadoutWord}\left(F, q, m, F(y)\right) = \operatorname{ReadoutWord}\left(F, q, m, F(y')\right)) \land (\forall r\in \mathbb{N}, y, y',\ \operatorname{ReadoutWord}\left(F, q, m+r, y\right) = \operatorname{ReadoutWord}\left(F, q, m+r, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/PredictionPartitionStability.prediction_partition_stable_forever` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a self-map F and readout q, ReadoutWord(F,q,m,y) records the readouts of y at update times zero through m. The hypothesis says that equality of these words is exactly the same relation at depths m and m+1.

The first conjunct proves that this depth-m relation is preserved when both states are updated by F. Iterating that congruence makes every later readout agree, while truncation gives the reverse implication. Thus the relation at every depth m+r equals the relation at depth m.

Repository search found the exact finite-word definition but no theorem containing both conclusions. Pinned Mathlib and Loogle found Function.iterate_add_apply, which the proof applies to shift readout coordinates. LeanSearch's shaped endpoint returned HTTP 404 and supplied no result.

The theorem is general in both types and does not require finiteness. A constant Boolean readout gives a checked witness that the stabilization hypothesis is satisfiable on a nontrivial state carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/PredictionPartitionStability.prediction_partition_stable_forever`
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](ConditionalEntropyStability.md)
