# Reindexed whole birth enumerations

## Abstract

Total decoding and faithful whole birth enumerations

**Theorem 1.1 (Every code decodes to its original tag).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.decode_code`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.decode_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity of first-reservation coding makes the inverse on its image exact, including ordinary zero.

**Theorem 1.2 (Colored ordinary indices decode faithfully).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.ordinaryIndex_decode`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.ordinaryIndex_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ordinary label and every ordinal stage, decoding its assigned index returns the same ordinary label. A zero event can carry zero or a hole color, and both decode to ordinary zero.

**Theorem 1.3 (Every tag reads both enumerations at one label).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.event_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.event_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tag and every ordinal stage, the same assigned index returns the original ordinary support or the supplied delayed support, together with the whole signed sequence at the original measure target. Colored ordinary zero events are included at every stage.

**Theorem 1.4 (The common index decodes exactly).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_decode`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every stage, decoding the common support and measure index returns its original tag, including delayed tags and all colored ordinary zero events.

**Theorem 1.5 (Every valid event index is within its stage).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a syntactically valid occurrence of a tag, its common support and measure index is at most the occurrence stage.

**Theorem 1.6 (Every label has cofinal valid indexed occurrences).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each new label and bound, there is a later valid reservation of a tag on the fixed birth row whose common index equals that label. Code-image labels use their original tags; holes and zero use the double reservation coloring of ordinary zero.

**Definition 1.7 (A reindexed whole birth pack).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.reindexBirth`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.reindexBirth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ordinary tags retain the original support enumeration, while delayed tags receive a supplied support family on the same carrier. Every measure value uses the decoded original target label, which is at most the new label. The original ordinary codes prove both enumerations onto. The support family V and clopen table B remain identical to the given whole birth. Choosing a delayed support as a coordinate pullback and proving its event launch identity are separate requirements.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.decode_code`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_decode`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.eventIndex_le`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.event_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.ordinaryIndex_decode`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.reindexBirth`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes](SignedOrdinalReindexCodes.md)
