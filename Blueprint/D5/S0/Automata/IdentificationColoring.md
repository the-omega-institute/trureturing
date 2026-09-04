# Typed DFAO Identification Colorings

## Abstract

A valid prefix-tree coloring is equivalent to a typed partial DFAO together with certified reached states on every sample prefix.

**Theorem 1.1 (Identification certificates are equivalent to realized sample machines).**

$$\operatorname{Nonempty}(\operatorname{Identification}(S, B, C)) \iff \exists M, \operatorname{Nonempty}(\operatorname{PrefixRealization}(S, M)) \land \operatorname{FitsSample}(S, M)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/IdentificationColoring.identification_iff_machine_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An identification contains the finite color assignment, transition table, output labels, base-state types, and a reached-state proof for every prefix occurrence.

The equivalence permits later encoders to target either coloring data or typed-machine realization data while preserving the mathematical existence problem exactly.

## References

- Truth anchor: `D5/S0/Automata/IdentificationColoring.identification_iff_machine_realization`
- Dependency: [D5/S0/Automata/LabeledPrefixTree](LabeledPrefixTree.md)
