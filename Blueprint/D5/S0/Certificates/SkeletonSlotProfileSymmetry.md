# SkeletonSlotProfileSymmetry

## Abstract

Exact finite gap constraints and a complete proved renaming cover for the original typed slot semantics.

**Definition 1.1 (relabel).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel`

*Formalization.* `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rename slots while retaining exactly the same Skeleton object.

**Theorem 1.2 (relabel_gap).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_gap`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gap transition rows transform by conjugacy, including all self-loops.

**Theorem 1.3 (relabel_readout).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_readout`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both observed channels transform with the slot names.

**Definition 1.4 (profileCode).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.profileCode`

*Formalization.* `D5/S0/Certificates/SkeletonSlotProfileSymmetry.profileCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A joint output code orders profiles, without identifying equal profiles.

**Definition 1.5 (orderedFive).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive`

*Formalization.* `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sort only the two slots not named by the three distinct-output observations.

**Theorem 1.6 (orderedFive_profiles).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_profiles`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every five-slot realization has an equivalent ordered profile presentation.

**Theorem 1.7 (orderedFive_anchor).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_anchor`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_anchor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output and return of each named anchor are unchanged.

**Definition 1.8 (fiveOutputCases).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases`

*Formalization.* `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three anchored Boolean post-zero outputs and two ordered six-valued extra profiles. The actual digit labels on each extra slot are 1,2,3.

**Theorem 1.9 (fiveOutputCases_card).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_card`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete ordered output enumeration, not a sample-search result.

**Theorem 1.10 (fiveOutputCases_cover).**

Lean statement: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_cover`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Either the extra profiles are already ordered or their interchange is.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_card`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.fiveOutputCases_cover`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_anchor`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.orderedFive_profiles`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.profileCode`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_gap`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotProfileSymmetry.relabel_readout`
- Dependency: [D5/S0/Certificates/SkeletonSlotGapConstraintTransport](SkeletonSlotGapConstraintTransport.md)
