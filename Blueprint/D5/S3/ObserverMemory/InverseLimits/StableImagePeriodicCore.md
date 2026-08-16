# Stable Image Periodic Core

## Abstract

Iterated images of a finite self-map decrease and stabilize at its periodic core.

**Theorem 1.1 (Finite iterate images stabilize at the periodic core).**

$$\forall Y, [\operatorname{Fintype} Y],\ F: Y \to Y,\ (\forall m, n\in \mathbb{N},\ m \leq n \Rightarrow \operatorname{ncard}(\operatorname{range}(F^{n})) \leq \operatorname{ncard}(\operatorname{range}(F^{m}))) \land (\forall t\in \mathbb{N},\ \operatorname{card}(Y) \leq t \Rightarrow \operatorname{range}(F^{t}) = \operatorname{periodicPts}(F)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore.iterate_range_card_antitone_and_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state carrier and F a self-map. The cardinality of the range of the n-th iterate is antitone in n.

Once n reaches the number of states, the range of the n-th iterate is exactly the set of periodic points of F. Thus the decreasing image capacity stabilizes at the cardinality of the periodic core.

The proof combines Mathlib's finite pigeonhole theorem with its periodic-point range and iterate lemmas. Pinned-Mathlib, Loogle, GitHub Lean-code, repository, and receipt searches found no equal or stronger stable-image declaration. LeanSearch's API endpoint returned HTTP 404 and supplied no search conclusion.

This closes the monotonicity and periodic-core stabilization of the first capacity sequence in the source atom. It does not claim the second quotient-capacity sequence or the linearized rank clause.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore.iterate_range_card_antitone_and_stable`
