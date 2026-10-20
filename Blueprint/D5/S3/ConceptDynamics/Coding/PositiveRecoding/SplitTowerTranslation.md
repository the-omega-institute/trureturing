# Derive integer-time laws inside the actual recoding constructions

## Abstract

Derive integer-time laws inside the actual recoding constructions.

time is StandardBeamHomeomorphisms.translate with coordinate t+a. On counted histories this has the same defining coordinates as NumberedPositiveInverseLaws.translate. The retained relabel and split forget laws commute with every signed time. The coordinate definitions give the corresponding lift laws, retaining t+1 for outgoing labels and t-1 for incoming labels.

The generic relabel and split laws quantify arbitrary Type* carriers. Relabel homeomorphism laws use discrete topological edge types. Positive laws quantify arbitrary nonnegative rectangular R,S with no period hypothesis. Applying the forward positive time law to the inverse image and canceling the bijection derives inverse time commutation locally.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Remark 1.1 (time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the existing graph-history translation, whose value at t reads the original history at t+a. This fixes the signed convention for all tower laws.

**Remark 1.2 (counted).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.counted`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.counted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the existing counted graph on numbered matrix edges. The adapter connects graph-history translation to the counted path API.

**Remark 1.3 (relabel_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A graph relabel acts coordinatewise, so its history map commutes with every signed translation. The endpoint proofs do not alter time.

**Remark 1.4 (relabel_homeomorph_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_homeomorph_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_homeomorph_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relabel homeomorphism has the same coordinatewise time law under the declared discrete edge topologies.

**Remark 1.5 (relabel_inverse_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_inverse_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_inverse_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse relabel homeomorphism also commutes with every signed translation. This permits both chart maps to pass through a correction.

**Remark 1.6 (outgoing_forget_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.outgoing_forget_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.outgoing_forget_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Outgoing forget applies the coordinatewise edge projection, so it commutes with the original signed translation.

**Remark 1.7 (incoming_forget_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.incoming_forget_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.incoming_forget_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Incoming forget commutes with signed translation by its coordinate projection. No extra centring term is introduced.

**Remark 1.8 (positive_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.positive_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.positive_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The counted positive recoding uses the same offset on its current S half and next R half. It therefore commutes with every signed translation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.counted`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.incoming_forget_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.outgoing_forget_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.positive_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_homeomorph_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_inverse_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.relabel_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation.time`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding](InSplitNumberedRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](../StandardBeamHomeomorphisms.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](../TwoSidedFiniteInduction.md)
