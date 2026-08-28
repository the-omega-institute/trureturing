# Predictive-State Unifilar Update

## Abstract

Complete future laws induce an almost-sure single-valued predictive-state update.

**Theorem 1.1 (The complete-future-law quotient has a unifilar update).**

$$\forall History \in Type, Symbol \in Type, K \in History \to \operatorname{ProbabilityMeasure}\left(Nat \to Symbol\right), extend \in History \to \left(Symbol \to History\right),\; \left(\left(\operatorname{MeasurableSpace}\left(Symbol\right) \land \left(\operatorname{MeasurableSingletonClass}\left(Symbol\right) \land \operatorname{Countable}\left(Symbol\right)\right)\right) \land \left(\forall h \in History, a \in Symbol,\; 0 < \operatorname{toMeasure}\left(K\left(h\right)\right)\left(\operatorname{setOf}\left(\Lambda x, x\left(0\right) = a\right)\right) \Rightarrow \operatorname{toMeasure}\left(K\left(extend\left(h, a\right)\right)\right) = \operatorname{scale}\left(\operatorname{inverse}\left(\operatorname{toMeasure}\left(K\left(h\right)\right)\left(\operatorname{setOf}\left(\Lambda x, x\left(0\right) = a\right)\right)\right), \operatorname{map}\left(\Lambda x n, x\left(n + 1\right), \operatorname{restrict}\left(\operatorname{toMeasure}\left(K\left(h\right)\right), \operatorname{setOf}\left(\Lambda x, x\left(0\right) = a\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists T \in \operatorname{Quotient}\left(\operatorname{ker}\left(K\right)\right) \to \left(Symbol \to \operatorname{Quotient}\left(\operatorname{ker}\left(K\right)\right)\right),\; \left(\forall h \in History, a \in Symbol,\; 0 < \operatorname{toMeasure}\left(K\left(h\right)\right)\left(\operatorname{setOf}\left(\Lambda x, x\left(0\right) = a\right)\right) \Rightarrow T\left(\operatorname{quotientClass}\left(K, h\right), a\right) = \operatorname{quotientClass}\left(K, extend\left(h, a\right)\right)\right) \land \left(\forall h \in History,\; \operatorname{AlmostEverywhere}\left(\operatorname{map}\left(\Lambda x, x\left(0\right), \operatorname{toMeasure}\left(K\left(h\right)\right)\right), \Lambda a, T\left(\operatorname{quotientClass}\left(K, h\right), a\right) = \operatorname{quotientClass}\left(K, extend\left(h, a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.unifilar_predictive_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each history is assigned a probability measure on infinite symbol streams. Histories with the same full measure define one predictive state.

For a positive first-symbol cylinder, extending the history is required to realize the normalized restriction to that cylinder, pushed forward by the tail map. This is the public process consistency premise.

The constructed quotient update sends every positive symbol to the class of the extended history. Countability of the symbol carrier then turns that pointwise rule into the displayed almost-everywhere next-symbol statement.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.unifilar_predictive_update`
