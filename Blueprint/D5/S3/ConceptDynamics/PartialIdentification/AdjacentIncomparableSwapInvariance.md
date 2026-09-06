# Adjacent Incomparable Swap Invariance

## Abstract

Adjacent parent-independent structural updates commute, so changing a compatible total order by one local swap preserves evaluation and readout.

A parent-local equation reads only its certified parent coordinates. Replacing a nonparent coordinate therefore leaves its local value unchanged.

Two distinct nodes with no direct parent edge in either direction write different coordinates and neither equation reads the coordinate written by the other. Their structural updates commute.

The commuting pair may occur after an arbitrary evaluated prefix and before an arbitrary suffix. Swapping the neighboring nodes preserves the complete final state and every readout of that state.

**Theorem 1.1 (Parent-independent local structural updates commute).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.localEvaluateNode_comm_of_no_direct_edges`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.localEvaluateNode_comm_of_no_direct_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reduces each local equation to the same pre-update value and then checks that writes to two distinct coordinates commute.

**Theorem 1.2 (One adjacent incomparable swap preserves structural evaluation).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.parent_local_evaluation_invariant_under_adjacent_swap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.parent_local_evaluation_invariant_under_adjacent_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction transports the commuting pair through an arbitrary evaluated prefix. The common suffix is then run from equal intermediate states.

**Theorem 1.3 (Every final-state readout is invariant under the swap).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.readout_invariant_under_adjacent_swap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.readout_invariant_under_adjacent_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying an arbitrary readout to the equal final states supplies the local query-invariance certificate needed by causal-order LP compilation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.localEvaluateNode_comm_of_no_direct_edges`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.parent_local_evaluation_invariant_under_adjacent_swap`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AdjacentIncomparableSwapInvariance.readout_invariant_under_adjacent_swap`
