# Finite-History Permanent Stability

## Abstract

A finite-history relation stable at one consecutive depth remains permanently stable.

**Theorem 1.1 (One stable depth makes all later history relations equal).**

$$\forall Y, O,\ F: Y \to Y, q: Y \to O, m\in \mathbb{N},\ (\forall y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m+1, y\right) = \operatorname{ReadoutWord}\left(F, q, m+1, y'\right)) \implies (\forall r\in \mathbb{N}, y, y',\ \operatorname{ReadoutWord}\left(F, q, m, y\right) = \operatorname{ReadoutWord}\left(F, q, m, y'\right) \iff \operatorname{ReadoutWord}\left(F, q, m+r, y\right) = \operatorname{ReadoutWord}\left(F, q, m+r, y'\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/FiniteHistoryPermanentStability.finite_history_relation_stable_forever` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a self-map and q a readout. ReadoutWord(F,q,m,y) is the finite observation history of y through update depth m, so equality of such words constructs the source relation directly.

If equality at depth m is equivalent to equality at depth m+1, then for every natural offset r, equality at depth m is equivalent to equality at depth m+r.

The exact repository theorem one_step_stability_is_permanent uses the same history words and premise. The Lean theorem applies its all-later-depth component directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/FiniteHistoryPermanentStability.finite_history_relation_stable_forever`
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability](OneStepPermanentStability.md)
