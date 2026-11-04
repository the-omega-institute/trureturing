# Reindexed actual signed laws

## Abstract

Actual proper-slice laws after whole-birth reindexing

**Definition 1.1 (The original decoded measure label).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldIndex`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each row from omega onward, decode with measureIndex of the actual wholeBirth in SignedOrdinalRealization.finalPrefix under CH. Finite rows retain their original labels. The decoded label is at most the new label.

**Definition 1.2 (The decoded coordinate in the same proper slice).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldCoord`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a label in the proper slice, its decoded label remains in that exact slice because it is at most the given label. No additional strict bound on the birth row or later carrier is required.

**Definition 1.3 (Concrete reindexed proper Data).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properData`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every cutoff below omega-one, use the original actual properSlice and properData. I, V and the clopen certificate remain literal originals. Nu reads the original whole sequence at the decoded measure label; J and N read the original tables at that decoded coordinate. Properness and mass are inherited. Zero, finite, omega and successor cutoffs, including successor last rows, are covered.

**Theorem 1.4 (All original signed A through F laws).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properLaws`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decoded coordinate is at most the new coordinate, so every eligible new label is eligible for the original A, C, DJ and F. B uses the same decoded reservoirs; DI and E use the identical I and V. The new OldClass equals the original OldClass at the decoded coordinate. Thus original F applies to every arbitrary all-natural sequence of regular signed norm-preserving lifts, retaining the same regular reference with norm at most one and the same weak convergence filter. No positivity or selected-sequence replacement is made.

**Theorem 1.5 (Every natural entry is the original whole-birth measure).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every born row, every label below omega-one and every natural index, slice_nu identifies the new signed measure with the actual wholeBirth measure at measureIndex. The label need not be below the slice cutoff, and newborn last rows need no later carrier.

**Theorem 1.6 (Compatibility with generic whole-birth reindexing).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_reindexBirth`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_reindexBirth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any delayed support on the same actual carrier, the concrete proper Data nu agrees at every label and natural index with reindexBirth of that same wholeBirth. Its nu is independent of delayedSupport.

The proper-stage adapter uses the same actual finalPrefix and whole-birth measures as SignedOrdinalActualReindex and SignedOrdinalActualG. Its full signed F laws and all-natural-index measure readback can therefore be used with that fixed global eta, universal support launch and successor G.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.nu_reindexBirth`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldCoord`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.oldIndex`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properData`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedLaws.properLaws`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalRealization](SignedOrdinalRealization.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth](SignedOrdinalReindexedBirth.md)
