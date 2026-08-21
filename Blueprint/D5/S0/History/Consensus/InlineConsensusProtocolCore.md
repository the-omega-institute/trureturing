# Inline Consensus Protocol Core

## Abstract

Finite protocol observations, digest-valued goal artifacts, implementation-aware dispatch plans, and fail-closed routers.

**Definition 1.1 (Carrier completion observations).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.CompletionObservation`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.CompletionObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CompletionObservation has three constructors: codex records five Boolean fields for carrier exit, result artifact, envelope, verdict, and sentinel; nyxid records three Boolean fields for terminal status, envelope, and verdict; and subagent records Boolean envelope and verdict fields.

**Definition 1.2 (Goal artifacts carry seven optional digests).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.GoalArtifact`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.GoalArtifact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GoalArtifact has seven fields: rawUserInput, normalizedGoal, constraints, successCriteria, iterationQuestion, harness, and revisions. Each field has type Option GoalArtifactDigest, and GoalArtifactDigest has the two distinct constructors digestA and digestB; these fields are not Booleans.

GoalArtifact.Complete checks that all seven options are present. GoalArtifactSnapshot.ContainsComplete additionally requires the snapshot's artifact to equal the shared artifact and its visibleFields to equal Finset.univ.

**Definition 1.3 (Dispatch plans carry layout proofs).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.DispatchPlan`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.DispatchPlan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A DispatchPlan stores a thinking-seat assignment, one implementation carrier, a review-seat assignment, and a termination-seat assignment. It carries a MultiSeatLayout proof for each of the three multi-seat assignments, not for the single implementation carrier. Each layout gives isolatedTokenSubagent and nyxidOracle exactly one seat and gives abstain no seat.

**Definition 1.4 (Thinking results are classified fail closed).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.thinkingSituation`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.thinkingSituation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

thinkingSituation returns singlePerspective if any report is presented as consensus. Otherwise it returns unanimousActionable only when all six verdicts propose the same recorded plan, and compatiblePlans only when all six plans are present, pairwise compatible, not all equal, and no verdict rejects or abstains. Every remaining input returns boundedStall.

**Definition 1.5 (Review routing has reject precedence).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.reviewRouter`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.reviewRouter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

reviewRouter returns fix when any of the three review verdicts is reject. With no reject it returns done when any verdict is approve, and otherwise returns userDecisionOrBoundedPass.

**Definition 1.6 (Termination routing requires an exact roster).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusProtocolCore.terminationRouter`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusProtocolCore.terminationRouter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

terminationRouter rejects a non-exact roster as rejectFakeConsensus. For an exact roster it returns permitClaim when all three results are satisfied, continueAgainstGap when some result is unsatisfied but not all are satisfied, and escalateEvidenceGap otherwise.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.CompletionObservation`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.DispatchPlan`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.GoalArtifact`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.reviewRouter`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.terminationRouter`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolCore.thinkingSituation`
