# Complexity-Filtered Record Extensions

## Abstract

Finite complexity filters eventually contain every record extension.

**Theorem 1.1 (Complexity filters eventually attain the full extension count).**

$$\exists Qstar, \forall Q \ge Qstar, \operatorname{card}\left(\operatorname{RestrictedExtensions}\left(\{f \mid \operatorname{complexity}\left(f\right) \le Q\}, record, prescribed\right)\right) = \operatorname{card}\left(Y\right)^{\operatorname{card}\left(D\right) - \operatorname{card}\left(record\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Extrema/ComplexityFilteredRecordExtensions.restricted_extension_card_eventually_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite function space D to Y has a maximum complexity value. Choose Qstar as that maximum. Every function then belongs to each complexity filter at level Q at least Qstar.

The filtered candidate set is therefore the full function space. The exact record-extension cardinality theorem then gives card(Y) raised to card(D) minus card(record).

This closes the qualitative part of the source clause: existence of a uniform finite complexity threshold, eventual containment of every record extension, and eventual equality of the restricted-extension cardinality. The source's explicit quantitative threshold bound Q* <= K(R) + (N0-n) ceil(log m) + c log N0 REMAINS OPEN and is not discharged.

The repository and pinned Mathlib were searched before proving. No theorem matching the full statement was found. The proof uses Finset.sup, Finset.le_sup, and record_extension_card.

## References

- Truth anchor: `D5/S0/Diagonal/Extrema/ComplexityFilteredRecordExtensions.restricted_extension_card_eventually_eq`
- Dependency: [D5/S0/Diagonal/RecordExtensionCount](../RecordExtensionCount.md)
