# Unit-factor recodings retain the original parallel-edge rank

## Abstract

Unit-factor recodings retain the original parallel-edge rank.

edgeCast transports literal numbered edges through a matrix equality and preserves source, target and number. rank_identity reuses Finset.orderEmbOfFin_unique and is consumed by both unit-factor ranking proofs. join_right_identity and join_left_identity prove that collapsing the unique identity half-edge leaves the original A-edge number unchanged; they use the existing fiber_number_lt_iff, including empty fibers.

The retained join_left_identity and join_right_identity identify the actual ranked half-edges used by recoding_time. After the two matrix-equality transports, the (A,1) elementary recoding is forward unit time. For every finite dimension n and every nonzero d, relative_time gives the actual primitive d-orbit cardinality in ZMod d. No invertibility, nonempty orbit stratum or three-divisibility hypothesis is added.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Theorem 1.1 (join_right_identity).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_right_identity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_right_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lex ranking really retains the original A-edge number in A*I. Only the identity half-edge is collapsed, including empty fibres.

**Theorem 1.2 (join_left_identity).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_left_identity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_left_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same rank argument for I*A uses the other coordinate of the pair. This is not inferred from the A*I case or from beam-action equality.

**Theorem 1.3 (recoding_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.recoding_time`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.recoding_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual forward convention: the S-half at t joins the R-half at t+1.

**Remark 1.4 (edgeCast).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal transport of numbered edges through an equality of matrices.

**Remark 1.5 (edgeCast_symm_apply).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_symm_apply`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_symm_apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transporting a numbered edge along a matrix equality and back recovers the same edge. This cancels the equality casts around a recoding.

**Remark 1.6 (edgeCast_source).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_source`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport along a matrix equality preserves the source vertex. This keeps castTimed compatible with path incidence.

**Remark 1.7 (edgeCast_target).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_target`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport along a matrix equality preserves the target vertex. No vertex reindexing is hidden in the cast.

**Remark 1.8 (edgeCast_number).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_number`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The underlying edge number is unchanged by matrix-equality transport. This keeps the original ranking in the identity-factor calculations.

**Remark 1.9 (castTimed).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.castTimed`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.castTimed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport every path coordinate along the literal matrix equality. The resulting path equivalence commutes with signed time.

**Remark 1.10 (cast_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_coordinate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each integer coordinate, castTimed is exactly the numbered edge cast. This identifies its action before computing phases.

**Remark 1.11 (cast_gyration).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_gyration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_gyration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrix-equality transport contributes zero gyration on every nonzero primitive stratum. This removes the two literal casts in the time and identity recodings.

**Remark 1.12 (identityEdge).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.identityEdge`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.identityEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is exactly one identity edge at this vertex; its actual number is 0.

**Remark 1.13 (rank_identity).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.rank_identity`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.rank_identity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Consumed rank helper. This is direct reuse of the public finite ordered embedding uniqueness theorem, not a second proof of that library result.

**Remark 1.14 (split_right_identity).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.split_right_identity`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.split_right_identity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Splitting an edge in A times the identity recovers that A edge and the unique identity edge at its target. The original A-edge number is retained.

**Remark 1.15 (relative_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.relative_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.relative_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine original-ranked primitive-orbit sum, at ALL nonzero periods.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.castTimed`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.cast_gyration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_number`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_source`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_symm_apply`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.edgeCast_target`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.identityEdge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_left_identity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.join_right_identity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.rank_identity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.recoding_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.relative_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding.split_right_identity`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport](CountedRelativeGyrationTransport.md)
