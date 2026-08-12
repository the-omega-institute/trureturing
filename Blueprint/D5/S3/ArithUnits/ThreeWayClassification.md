# Three-Way Classification Is Not Binary

## Abstract

A three-element classification is not equivalent to a two-element residue grading.

**Theorem 1.1 (A three-way classification is not a binary grading).**

$$\neg \operatorname{Nonempty}(\operatorname{Equiv}(\operatorname{Fin}(3), \operatorname{ZMod}(2))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/ThreeWayClassification.three_way_classification_not_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an honest partial closure of the source's non-binary clause. It formalizes only the cardinality obstruction between a three-element classification and the two-element residue grading.

The source's self-description limitations, copying obstruction, fixed-point-count interpretation, and parity-shadow claim remain unresolved and are outside this deposit.

Pinned Mathlib was searched before proving. No exact theorem was found. The Lean declaration is a thin wrapper around Fintype.card_congr and ZMod.card: an equivalence would force the unequal cardinalities three and two to coincide.

## References

- Truth anchor: `D5/S3/ArithUnits/ThreeWayClassification.three_way_classification_not_binary`
