# Catalog-Wide Fused Counting

## Abstract

One saturated theorem-family scan classifies each ordered state pair.

**Definition 1.1 (Complete state enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.StateEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.StateEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A duplicate-free list is certified to contain every arena state.

**Definition 1.2 (Complete index enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.IndexEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.IndexEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A duplicate-free list is certified to contain every catalog index.

**Definition 1.3 (Canonical finite-index enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.finIndexEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.finIndexEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ascending finite range supplies a complete Fin n enumeration.

**Definition 1.4 (Catalog-wide result).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.FusedCounts`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.FusedCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Full escape, unique counts, and fifteen role bins are accumulated together.

**Definition 1.5 (Derived leave-one-out count).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.without`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.without` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Leave-one-out escape is full plus the selected unique count.

**Definition 1.6 (Zero accumulator).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.zero`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every catalog-wide count starts at zero.

**Definition 1.7 (Four-bit mask signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.maskSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.maskSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Fin 16 mask is decoded in CUT, FLOW, ADMIT, ANCHOR order.

**Definition 1.8 (Nonzero bucket mask).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketMask`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Fin 15 bucket is shifted into the nonzero Fin 16 masks.

**Definition 1.9 (Mask bucket projection).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketOfMask`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketOfMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonzero mask is projected back to its zero-based bucket.

**Definition 1.10 (Bucket role signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.roleSignatureOfBucket`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.roleSignatureOfBucket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bucket names one nonzero four-role signature.

**Definition 1.11 (Selected theorem mask).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.selectedMask`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.selectedMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four primitive-axis disagreements are packed into one mask.

**Definition 1.12 (Saturated disagreement class).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.PairScan`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.PairScan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pair has no disagreement, one indexed disagreement, or at least two.

**Definition 1.13 (Scan after first disagreement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanAfterOne`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanAfterOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remaining indices are inspected only until disagreement two.

**Definition 1.14 (Single theorem-family scan).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanIndices`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair traverses the catalog index enumeration at most once.

**Definition 1.15 (Certified catalog pair scan).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairScan`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairScan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The saturated scan consumes a complete index enumeration.

**Definition 1.16 (Unique-bin increment).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bump`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One singleton disagreement increments its index and exact role bucket.

**Definition 1.17 (One pair transition).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairStep`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Off-diagonal pairs update exactly one classification branch.

**Definition 1.18 (Strict fused census).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.fusedCounts`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.fusedCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A strict nested fold classifies every ordered pair once.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.FusedCounts`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.IndexEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.PairScan`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.StateEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketMask`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bucketOfMask`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.bump`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.finIndexEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.fusedCounts`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.maskSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairScan`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.pairStep`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.roleSignatureOfBucket`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanAfterOne`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.scanIndices`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.selectedMask`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.without`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.zero`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RoleHistogram](../InformationEscape/RoleHistogram.md)
