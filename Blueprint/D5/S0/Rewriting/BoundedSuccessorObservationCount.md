# Bounded Successor Observation Count

## Abstract

Bounded Successor Observation Count

**Theorem 1.1 (First failure times count the finite observations).**

Lean statement: `D5/S0/Rewriting/BoundedSuccessorObservationCount.bounded_successor_observation_count`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/BoundedSuccessorObservationCount.bounded_successor_observation_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict successor on the finite interval from zero to B first fails from n at time B minus n plus one and remains failed thereafter. Through time h, constant successful readouts give exactly the minimum of B plus one and h plus one observation classes. Arbitrary readouts give at least that many and at most B plus one classes. The first failure times and complete observed futures distinguish all starting states.

## References

- Truth anchor: `D5/S0/Rewriting/BoundedSuccessorObservationCount.bounded_successor_observation_count`
