# DFAO State Lower Bounds

## Abstract

Finite distinguishing continuations give checkable state lower bounds for output automata built on Mathlib DFA.

**Theorem 1.1 (Distinguishing continuations force distinct reached states).**

Lean statement: `D5/S0/Automata/DFAOStateLowerBound.state_lower_bound_of_distinguishing_family`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/DFAOStateLowerBound.state_lower_bound_of_distinguishing_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A DFAO reuses Mathlib's deterministic finite automaton as its transition carrier and adds one output map on states. Correctness may be restricted to an explicitly declared sparse language.

A finite certificate chooses prefixes and a legal pair-specific continuation for every two distinct indices. The target outputs after that common continuation must differ.

If two certified prefixes reached the same machine state, the upstream append evaluation law would force the same final state and output after their shared continuation. Correctness would contradict the certificate, so the reached-state map is injective and the state count is bounded below.

## References

- Truth anchor: `D5/S0/Automata/DFAOStateLowerBound.state_lower_bound_of_distinguishing_family`
