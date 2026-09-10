# Threshold Access

## Abstract

A restricted threshold family is constant above a floor exactly when all admissible charges lie below it.

**Theorem 1.1 (Exact boundary of threshold independence).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_sets_constant_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_sets_constant_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an admissible set, a charge for each item, and a floor in any linearly ordered level type. Every budget above the floor gives the same access set precisely when every admissible item has charge at most the floor. Testing the maximum of the floor and an item's charge establishes necessity. Mathlib's set-separation extensionality establishes sufficiency.

For money, nonmonetary eligibility belongs to the admissible set and payment is a separate input. For scheduling, charges can instead be job durations and the budget a deadline. The theorem assumes no production technology, ownership regime, welfare ordering, or equilibrium.

**Theorem 1.2 (A priced witness strictly enlarges access).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_set_strict_of_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_set_strict_of_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible item whose charge is strictly above the lower budget and at most the upper budget witnesses strict inclusion between the two access sets. This concerns the entire set of accessible choices, not a person's preference or the item's production cost.

## References

- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_set_strict_of_witness`
- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_sets_constant_iff`
