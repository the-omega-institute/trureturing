# Prefix Coloring Soundness

## Abstract

Every DFAO compatible with a labeled prefix graph induces a transition- and output-consistent state coloring.

**Theorem 1.1 (Uncolorability excludes compatible machines).**

$$\neg \operatorname{Nonempty}(\operatorname{Coloring}(G, S)) \Rightarrow \neg \exists M: \operatorname{Compatible}(M, G).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/PrefixColoringSoundness.no_compatible_machine_of_no_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each prefix node is colored by the machine state reached after reading its stored word.

Mathlib DFA append evaluation proves transition consistency, and compatibility with terminal labels proves output consistency.

Therefore an exact no-coloring certificate is a sound finite lower-bound certificate. The converse coloring-to-machine construction is intentionally deferred.

## References

- Truth anchor: `D5/S0/Automata/PrefixColoringSoundness.no_compatible_machine_of_no_coloring`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
