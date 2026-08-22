# One-Step Permanent Stability

## Abstract

A prediction partition stable for one step remains stable at every later depth.

**Theorem 1.1 (One stable step makes every later prediction relation equal).**

$$\forall Y, O,\ F: Y \to Y, q: Y \to O, m\in \mathbb{N},\ (\forall y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m+1, y\right) = \operatorname{ReadoutWord}\left(F, q, m+1, y'\right)) \implies \left((\forall y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \Rightarrow \operatorname{ReadoutWord}\left(F, q, m, F(y)\right) = \operatorname{ReadoutWord}\left(F, q, m, F(y')\right)) \land (\forall r\in \mathbb{N}, y, y',\ \operatorname{ReadoutWord}\left(F, q, m+r, y\right) = \operatorname{ReadoutWord}\left(F, q, m+r, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability.one_step_stability_is_permanent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a self-map F and readout q, ReadoutWord(F,q,m,y) records the readouts of y at update times zero through m. The premise states that equality of words at depths m and m+1 defines the same relation on states.

The first public conjunct says that the depth-m relation is preserved by updating both states. The second says, for every natural offset r, that equality at depth m+r is equivalent to equality at depth m.

Repository search found prediction_partition_stable_forever with exactly this premise and both conclusions. The Lean wrapper imports and applies that declaration directly, without introducing another prediction-word or relation primitive.

The imported module also compiles a constant Boolean readout witness for the premise, so the hypothesis is satisfiable on an inhabited, nontrivial state carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability.one_step_stability_is_permanent`
- Dependency: [D5/S3/ObserverMemory/Prediction/PredictionPartitionStability](../Prediction/PredictionPartitionStability.md)
