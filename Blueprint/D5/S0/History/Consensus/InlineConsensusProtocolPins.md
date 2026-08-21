# Inline Consensus Protocol Pins

## Abstract

Concrete dispatch and goal-artifact fixtures pin initial-plan compatibility, identity-sensitive snapshots, and every indexed protocol clause.

**Theorem 1.1 (The protocol initial plan is compatible).**

$$\operatorname{InitialPlanCompatible}\left(protocolEligibility, protocolDispatchPlan\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.protocol_initial_plan_is_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

protocolDispatchPlan assigns an implementation carrier as well as the three multi-seat functions. This theorem proves that every carrier returned by its carrierAt function is legal for that stage and role and is accepted by protocolEligibility.

**Theorem 1.2 (A mismatched initial plan is rejected).**

$$\operatorname{mismatchedImplementationEligibility}\left(implementationWorker, implementation, codexCli\right) = false\\ \land \operatorname{mismatchedImplementationEligibility}\left(implementationWorker, implementation, nyxidOracle\right) = true\\ \land \neg\operatorname{InitialPlanCompatible}\left(mismatchedImplementationEligibility, protocolDispatchPlan\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.mismatched_initial_plan_is_rejected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the implementationWorker/implementation position, the mismatched eligibility function rejects codexCli and accepts nyxidOracle. Because protocolDispatchPlan assigns codexCli there, the same theorem's third conjunct proves that this eligibility function and plan are not InitialPlanCompatible.

**Theorem 1.3 (Two distinct complete goal artifacts exist).**

$$\exists first, second: GoalArtifact,\ first.Complete \land second.Complete \land first \neq second$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.two_distinct_complete_goal_artifacts_exist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witnesses are protocolGoalArtifact, whose seven optional digest fields contain digestA, and protocolAlternateGoalArtifact, whose rawUserInput contains digestB. Both satisfy GoalArtifact.Complete, but the artifacts are unequal. The theorem is existential and does not classify all complete artifacts.

**Theorem 1.4 (The complete goal snapshot is accepted).**

$$GoalArtifactSnapshot.\operatorname{ContainsComplete}\left(protocolGoalArtifact, \langle protocolGoalArtifact, Finset.univ\rangle\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.complete_goal_snapshot_is_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The snapshot contains protocolGoalArtifact itself and exposes Finset.univ. The theorem proves ContainsComplete for that shared artifact and exactly that full snapshot.

**Theorem 1.5 (A full snapshot with the wrong artifact is rejected).**

$$\neg GoalArtifactSnapshot.\operatorname{ContainsComplete}\left(protocolGoalArtifact, \langle protocolAlternateGoalArtifact, Finset.univ\rangle\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.full_snapshot_with_wrong_artifact_is_rejected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Although the snapshot exposes Finset.univ and its alternate artifact is complete, ContainsComplete also requires artifact identity with the shared protocolGoalArtifact. The alternate rawUserInput digest makes that equality false.

**Theorem 1.6 (Empty visible fields are rejected).**

$$\neg GoalArtifactSnapshot.\operatorname{ContainsComplete}\left(protocolGoalArtifact, \langle protocolGoalArtifact, \varnothing\rangle\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.empty_visible_fields_are_rejected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This snapshot carries the correct complete artifact but has no visible fields. It is rejected because ContainsComplete requires visibleFields to equal Finset.univ.

**Theorem 1.7 (The required inline-consensus fixture suite is pinned).**

$$\forall clause,\ \operatorname{ClauseObject}\left(clause\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RequiredFixtureSuite unfolds to forall clause, ClauseObject clause. ClauseId has ten constructors, and every ClauseObject branch contains the full semantic conjunction for that indexed protocol clause.

The proof supplies every conjunct and now consumes the stage-successor, carrier-selection, initial-plan, fallback, run, router, artifact, permit, and budget theorems used by the ten cases. It also discharges the remaining layout and transition-preservation obligations locally; those local proofs are not additional public declarations.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.complete_goal_snapshot_is_accepted`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.empty_visible_fields_are_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.full_snapshot_with_wrong_artifact_is_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.mismatched_initial_plan_is_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.protocol_initial_plan_is_compatible`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.required_fixture_suite_is_pinned`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.two_distinct_complete_goal_artifacts_exist`
- Dependency: [D5/S0/History/Consensus/InlineConsensusProtocolFixtures](InlineConsensusProtocolFixtures.md)
