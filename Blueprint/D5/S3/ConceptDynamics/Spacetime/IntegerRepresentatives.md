# Canonical Integer Representatives

## Abstract

The fixed HF names form a canonical balanced archive in every dimension; the source uses dimension three.

**Definition 1.1 (Signed integer archives use exact HF pair names).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventNames`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventNames` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n, the archive is exactly the Kuratowski pair of each natural index below natAbs n with each fixed positive or negative sign code. The source leaf label is the same index. Time and every Fin d coordinate are zero.

**Definition 1.2 (Typed finite indices name precisely the HF archive).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite product Fin (natAbs n) times Bool is bijective with the subtype of the exact HF event-name set. Pair and sign injectivity make this a faithful presentation of the prescribed names.

**Theorem 1.3 (Positive representatives select exactly positive names).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selection_positive_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selection_positive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n is positive, the selected subtype is precisely the positive-name image; the negative case has the analogous characterization. Zero selects no event.

**Theorem 1.4 (Canonical archives have twice the absolute integer size).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_archive_card`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_archive_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The archive has cardinality 2 times natAbs n in every dimension.

**Theorem 1.5 (The entire archive is current).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_current_card`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_current_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current region also has cardinality 2 times natAbs n.

**Theorem 1.6 (Selection has the absolute integer size).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selected_card`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selected_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign-selected subset has cardinality natAbs n.

**Theorem 1.7 (Canonical signed selections read out to their integer).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every event contributes the fixed sign one or minus one. Summing the selected positive or negative names gives exactly n, and summing both signs over the current archive gives zero background charge.

**Theorem 1.8 (The zero representative is empty).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_zero_empty`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_zero_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero representative has empty archive, current region and selection in every dimension.

**Definition 1.9 (U denotes the literal representative of one).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.U`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U is defined as representative 3 1. The notation i(n) denotes representative 3 n, and emptyRepresentative is representative 3 0. Specializing representative_archive_card and representative_current_card at d=3,n=1 gives size two; specializing representative_selected_card gives size one. These are applications of the general theorems. The source positions are Fin 3 to Int, and consumers in dimension three use representative 3 n and the same general theorems.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.U`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.eventNames`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_archive_card`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_current_card`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selected_card`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_selection_positive_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.representative_zero_empty`
- Dependency: [D5/S0/History/Spacetime/ArchiveCarrier](../../../S0/History/Spacetime/ArchiveCarrier.md)
- Dependency: [D5/S0/History/Spacetime/CoordinateEncoding](../../../S0/History/Spacetime/CoordinateEncoding.md)
- Dependency: [D5/S0/History/Spacetime/HFEncoding](../../../S0/History/Spacetime/HFEncoding.md)
- Dependency: [D5/S0/History/Spacetime/IntegerEncoding](../../../S0/History/Spacetime/IntegerEncoding.md)
- Dependency: [D5/S0/History/Spacetime/SourceTreeEncoding](../../../S0/History/Spacetime/SourceTreeEncoding.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](ComplementCharge.md)
