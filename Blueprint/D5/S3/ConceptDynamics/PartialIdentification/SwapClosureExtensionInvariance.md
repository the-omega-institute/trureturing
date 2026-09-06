# Swap-Closure Extension Invariance

## Abstract

A replayable finite chain of adjacent parent-independent swaps preserves structural response profiles and every query readout.

One admissible move swaps neighboring nodes whose equations do not read one another. The move records its prefix, pair, suffix, distinctness, and two nonparent certificates.

A typed swap chain is the reflexive-transitive closure of these local moves. Induction composes the state equality supplied by every adjacent swap.

This separates semantic invariance from the remaining combinatorial theorem. Once compatible linear extensions are proved swap-connected, their structural responses and compiled query readouts agree automatically.

**Theorem 1.1 (A finite admissible swap chain preserves evaluation).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.evaluation_invariant_of_swap_chain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.evaluation_invariant_of_swap_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The induction proof composes exact final-state equalities for the recorded local moves.

**Theorem 1.2 (Swap-connected orders have identical response profiles).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.responseProfile_invariant_of_swap_chain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.responseProfile_invariant_of_swap_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluation theorem is applied pointwise to every exogenous state.

**Theorem 1.3 (Swap connectivity discharges global extension invariance).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.extension_invariance_from_swap_connectivity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.extension_invariance_from_swap_connectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any proof that compatible extensions belong to one swap component immediately yields equality of all query readout functions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.evaluation_invariant_of_swap_chain`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.extension_invariance_from_swap_connectivity`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.responseProfile_invariant_of_swap_chain`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance](AdjacentIncomparableSwapInvariance.md)
