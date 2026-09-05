# Typed Sparse-Sample Identification

## Abstract

Finite typed sample obstructions imply global DFAO state lower bounds.

**Theorem 1.1 (A finite coloring obstruction gives a global state lower bound).**

$$\operatorname{NoSmallModel}(k, S) \land \operatorname{Fits}(M, S) \implies k < \operatorname{card}(State).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TypedSampleIdentification.no_small_model_implies_state_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A labeled sample carries exact words and outputs. A typed sample additionally assigns the legal partial-base state reached by every prefix.

Every fitting typed DFAO colors each sample prefix by the reached machine state. Equal colors automatically preserve terminal outputs, one-symbol transitions, and base-state types.

An injective relabeling sends a machine with at most k states into Fin k. Therefore the nonexistence of a Fin k coloring for any reindexed finite sample excludes every globally correct typed DFAO with at most k states.

## References

- Truth anchor: `D5/S0/Automata/TypedSampleIdentification.no_small_model_implies_state_lower_bound`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
