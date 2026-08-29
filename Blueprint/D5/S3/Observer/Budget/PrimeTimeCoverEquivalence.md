# Prime-Time Cover Equivalence

## Abstract

A finite observer budget through a fixed time depth is complete exactly when its timed separation sets cover every distinct ordered state pair.

**Definition 1.1 (Timed observer readout).**

Lean statement: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedReadout`

*Formalization.* `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At coordinate (i,n), evaluate observer i on the n-fold update of the state, using the canonical complete itinerary.

**Definition 1.2 (Timed separation set).**

Lean statement: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedSeparationSet`

*Formalization.* `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedSeparationSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named separation set for coordinate (i,n) reuses the canonical observer separation set on the timed readout family.

**Definition 1.3 (Selected prefix coordinates).**

Lean statement: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCoordinates`

*Formalization.* `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite coordinate budget is the product of selected observers with the natural-number range from zero through m.

**Definition 1.4 (Joint prefix readout).**

Lean statement: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixReadout`

*Formalization.* `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent joint readout assembles all selected observer-time coordinates through the fixed depth.

**Definition 1.5 (Time-prefix separation cover).**

Lean statement: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCover`

*Formalization.* `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the union of timed separation sets over every selected observer and every time no greater than m.

**Theorem 1.6 (Timed completeness is prefix coverage).**

$$\forall I \in Type, X \in Type, O \in I \to Type, F \in X \to X, q \in \forall i: I, X \to \operatorname{O}\left(i\right), J \in \operatorname{Finset}\left(I\right), m \in \mathbb{N},\; \operatorname{Injective}\left(\operatorname{timePrefixReadout}\left(F, q, J, m\right)\right) \Leftrightarrow \operatorname{timePrefixCover}\left(F, q, J, m\right) = \operatorname{statePairUniverse}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.prime_time_budget_injective_iff_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the finite-budget cover equivalence to the product of J with the range through m. Product membership is exactly i in J and n at most m, so its coordinate union is the named prefix cover.

No finiteness assumption on states or observer indices is used. At depth zero this recovers the untimed theorem; empty, singleton, identity, constant, and zero-readout cases are checked in Lean.

The source's weighted-cover sentence is programmatic: no timed cost model is asserted here.

## References

- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.prime_time_budget_injective_iff_cover`
- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCoordinates`
- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixCover`
- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timePrefixReadout`
- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedReadout`
- Truth anchor: `D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.timedSeparationSet`
- Dependency: [D5/S3/Observer/Budget/MinimumCompleteSetCover](MinimumCompleteSetCover.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../../ObserverMemory/Prediction/ItineraryCompletion.md)
