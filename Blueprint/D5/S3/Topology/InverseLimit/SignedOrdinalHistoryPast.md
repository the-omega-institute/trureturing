# The exact strict-past proper limit input

## Abstract

The exact strict-past proper limit input

**Theorem 1.1 (Exact earlier carrier readback).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.carrier_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.carrier_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For cutoffs at most omega-one, every carrier of an actual earlier state equals the strict prefix carrier at that same coordinate. Coordinates at most omega use the actual initial invariant; later coordinates use pairwise same-run coherence.

**Theorem 1.2 (Canonical whole old birth).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.bornPack_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.bornPack_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each whole birth is the original Q at its row and equals the transported old birth in every later actual state.

**Theorem 1.3 (Post-run incoming I).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postI_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postI_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any proper cutoff the eligible I equals the actual incoming state I.

**Theorem 1.4 (Post-run incoming J).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postJ_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postJ_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any proper cutoff the eligible J equals the actual incoming state J.

**Theorem 1.5 (Post-run permanent N).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postN_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postN_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original outgoing maximum reservoir equals each eligible incoming oldN. At a successor cutoff the outgoing last-row event is read only after the run is complete.

**Theorem 1.6 (Every proper post-run slice).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postLaws`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original A through F and DI/DJ hold at every proper cutoff. The last row retains its actual whole birth and disjoint reservoirs even though E and F have strictly older row domains.

**Theorem 1.7 (Incoming I readback).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.I_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.I_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every actual earlier state and strictly older row, the strict Data.I equals that state's actual incoming predecessor I.

**Theorem 1.8 (Incoming J readback).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.J_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.J_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a strictly older row and eligible old label, strict Data.J equals the actual incoming predecessor J at that earlier carrier stage.

**Theorem 1.9 (Original eligible A through F on one strict past).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.strictLaws`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.strictLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pairwise coherent family of already constructed states below a proper successor-limit ordinal defines a literal Prefix. Each carrier and restriction is read from a later state of that same past. Each whole birth is its original Q; permanent N is read from the original outgoing maximum event, whose successor arrival lies strictly below the limit. Incoming I and J are read at the carrier stage. Canonical birth and arrival equalities identify A, B, C, E and regular bounded F with actual predecessor evidence, while pairwise coherence gives DI and DJ. No completed-history or future-stage semantic predicate enters these proper-limit input laws.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.I_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.J_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.bornPack_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.carrier_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postI_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postJ_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postLaws`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.postN_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.strictLaws`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalHistoryState](SignedOrdinalHistoryState.md)
