# Typed Partial DFAO

## Abstract

Partial output automata can be typed over a base automaton with exact transition projection and leading-zero invariance.

**Theorem 1.1 (Successful runs project to the base automaton).**

$$\operatorname{map}(stateType, \operatorname{run}(w)) = \operatorname{baseRun}(w).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TypedPartialDFAO.machine_run_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base automaton marks representation-valid transitions, while the output machine may carry a finer state space.

An exact Option-map equation forces every defined machine transition to project to the prescribed base transition and forbids illegal transitions.

The run theorem lifts that local typing equation to arbitrary input words and keeps leading-zero invariance explicit.

## References

- Truth anchor: `D5/S0/Automata/TypedPartialDFAO.machine_run_type`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
