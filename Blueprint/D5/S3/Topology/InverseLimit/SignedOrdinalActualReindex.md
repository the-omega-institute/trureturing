# Actual support and measure fidelity

## Abstract

Actual selected events at one reindexed label

**Definition 1.1 (The actual omega zero delayed support).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualDelayedSupport`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualDelayedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original omega birth support at zero is pulled back along the literal finalPrefix map from the given row to omega. Surjectivity follows from the same Prefix onto law; no support supplier is assumed.

**Definition 1.2 (Reindexing the identical whole birth).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualBirth`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualBirth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input is exactly wholeBirth of the original fixed run on its finalPrefix carrier. The generic reindexBirth changes U and nu indices while retaining V and B. Delayed U uses the actual omega zero pullback, whereas nu uses measureIndex of this same wholeBirth.

**Definition 1.3 (One label for every actual selected event).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reservation is checked against its actual local delayed semantics. Valid ordinary and delayed branches use the generic eventIndex on their own original whole birth. Every rejected or invalid task instead uses eta zero directly, avoiding hole coloring of fallback events.

**Theorem 1.4 (The actual row is already born).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eventRow_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eventRow_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The packaged row is at most the event stage. The selected target equality pins it to the treatment row of the already selected event.

**Theorem 1.5 (The actual common label is eligible).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original event, eta is at most its stage. Valid tag occurrences use the generic bound; rejected events use zero directly.

**Theorem 1.6 (The actual selected target is fixed).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_target`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the packaged row and its decoded original measure target equal the treatment of the same selected Q and Result. The construction does not select a replacement treatment or Result.

**Theorem 1.7 (All natural indices read the same selected measure).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_measure`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stage and every natural index, the reindexed birth measure at eta is heterogeneously equal to the actual selected Q measure at its actual treatment row and label. Old rows use original whole birth coherence. Self row events use the same newborn Q. This supplies the exact target readback consumed by the same selected Result quantitative_g, for either ordinary or delayed selection, without rebuilding G or its signed endpoint.

**Theorem 1.8 (Every new label has cofinal actual events).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actual_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actual_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every born row, every new Label and every bound, there is a later actual event on that row with eta equal to that Label. The witness is strictly after the row. Generic tag occurrences are converted to actual ordinary execution or, using stable_local and intrinsic_cast, actual eligible delayed execution. Holes and zero use only valid ordinary zero reservations.

**Theorem 1.9 (Every actual newborn support launches at the same eta).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.universal_launch`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.universal_launch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual event and every natural index, newborn V is exactly the inverse image of the reindexed U at its actual row and the same eta used by selected_measure. Self row events use Prepared.launch_eq with the same Q.U and Q.V; old ordinary rows use original birth coherence. Delayed launches use omega zero and literal composition of restrictions. Invalid and rejected tasks retain the original omega zero fallback. This statement covers every stage, including self row events, rather than only cofinal witnesses.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualBirth`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actualDelayedSupport`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.actual_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eta_le`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.eventRow_le`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_measure`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.selected_target`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.universal_launch`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents](SignedOrdinalRealizationEvents.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth](SignedOrdinalReindexedBirth.md)
