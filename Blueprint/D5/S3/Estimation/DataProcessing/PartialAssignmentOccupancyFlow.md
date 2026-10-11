# Partial assignment occupancy flows and terminal laws

## Abstract

Partial assignment occupancy flows and terminal laws.

**Theorem 1.1 (Every incoming last coordinate).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.incomingAppend_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.incomingAppend_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state is a dependent function assigning either no value or one actual letter to each coordinate in a fixed finite nonempty named set. Capacities lie between reciprocal alphabet cardinality and one. The alphabets are finite and nonempty and can have different sizes. Erasure discards the read order and preserves all coordinate identities and obtained values. Its rank is the number of assigned coordinates, equal to the history length. Each history arriving at a state has a unique last coordinate. The bijection partitions its entire history fiber over every assigned coordinate and the history fiber of the state with that coordinate deleted. Distinct orders can therefore merge at one state.

**Theorem 1.2 (Literal incoming conservation).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_incoming`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_incoming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing ordered node, selection and result masses on the erasure fibers gives the occupancy variables. The last-coordinate partition turns the sum of child node masses into the sum of result flows from all deleted parents. Summing the remaining ordered-flow constraints gives root mass one, outgoing conservation, result normalization, nonnegativity and the original coordinate cap. Occupancy feasibility assumes these literal equations and does not assume an ordered lifting witness.

**Theorem 1.3 (Constructive inverse on every mass).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.lift_all_masses`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.lift_all_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a positive node the global scheduler row is selection mass divided by node mass. At a positive selection the result row is result mass divided by selection mass. Null nodes use a uniform row on the actual unread coordinates, and null selections use the uniform row on their own alphabet. The lower capacity bound makes these fallback rows lawful. Weighted row identities hold also at zero denominators. Ordered masses are built recursively from these rows. Induction on rank, using all deleted parents and incoming conservation, recovers every node mass. The weighted identities then recover every selection and result mass, including null branches.

**Theorem 1.4 (Equality of occupancy flows).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Aggregating the constructed ordered flow gives the original occupancy flow in all three variable families. The inverse preserves the entire finite flow, rather than only a terminal statistic.

**Theorem 1.5 (Fresh lawful archive realization).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.realize_occupancy_state_strategy`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.realize_occupancy_state_strategy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed ordered flow is supplied to the ordered archive realization theorem. Its separate fresh scheduling and result table innovations retain every completed block, reveal current scheduling before the result, and check the conditional cap on that complete accessible archive. On this same actual carrier, literal erased-state node, selection and result events have exactly the prescribed masses. The complete pre-schedule archive F gives the scheduler kernel one_Node times sigma; the archive G, which also discloses the current scheduler innovation, gives the result kernel one_Selection times q. Both identities hold almost everywhere. At a complete assignment the node mass is the entire named terminal joint law. This construction uses cap-only rectangular row pasting: arbitrary legal rows at different histories must be independently selectable.

**Theorem 1.6 (Actual disjoint state events).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_event_masses`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_event_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal node event fixes the erased assignment of the actual history. Selection also fixes the named coordinate; result also fixes its actual letter in the dependent alphabet. Each event is the disjoint union of its ordered-history fibers on the canonical fresh archive. Finite disjoint probability sums and the all-mass inverse give respectively M(a), F(a,i) and F(a,i,x), including zero-mass states and edges.

**Theorem 1.7 (Scheduling under the complete F archive).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_scheduler_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_scheduler_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before schedule disclosure, F retains all past scheduler and result innovation blocks. Independence of the next block and its scheduler marginal give the ordered scheduler conditional expectation. The weighted ordered row equals node mass times the global erased-state row. A positive mass permits cancellation; a zero mass makes its actual event null and permits almost-everywhere replacement. Summing disjoint history fibers gives E[one_Selection | F] = one_Node times sigma. This is a property of the new reverse realization, not of every original archive strategy.

**Theorem 1.8 (Results under the complete G archive).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_result_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_result_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

G retains all previous innovation blocks and the full currently disclosed scheduler table, while the current result innovation stays fresh. The existing ordered full-G conditional result theorem is reused directly. Selection mass times its ordered row equals selection mass times the global q row. Cancellation on positive selections and null-event replacement on zero selections allow finite fiber aggregation, giving E[one_Result | G] = one_Selection times q almost everywhere. Unused auxiliary table cells need not agree pointwise across erased histories.

**Theorem 1.9 (Exact terminal law set).**

Lean statement: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.occupancy_terminal_law_range`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.occupancy_terminal_law_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of terminal occupancy laws equals archiveTerminalLaws, the existing set of terminal laws of legal actual archived strategies. The forward statement also applies to an original strategy on an arbitrary probability space with arbitrary additional retained records. No finite-history restriction is imposed on that original archive. The compression preserves terminal joint laws, including correlations, but does not preserve original read-order distributions or auxiliary-record joint laws. Source compatibility, permissions or costs that depend on order require additional state information; the cap-only assumption does not remove those restrictions. The finite state space can still grow exponentially, so existence of this exact representation supplies no low-cost extraction or solution claim.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_incoming`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_lift`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.incomingAppend_bijective`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.lift_all_masses`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.occupancy_terminal_law_range`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.realize_occupancy_state_strategy`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_event_masses`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_result_kernel`
- Truth anchor: `D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_scheduler_kernel`
- Dependency: [D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization](OrderedCoordinateFlowRealization.md)
