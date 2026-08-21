# Inline Consensus Protocol Pins

## Abstract

Concrete fixtures pin selector-backed worker-mode routing, recoverable permit freshness, identity-sensitive snapshots, and model-indexed clause coverage.

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

**Theorem 1.7 (Worker-mode advance consumes selection and availability evidence).**

$$\forall model,\ \operatorname{WorkerModeAdvanceConsumesSelection}\left(model\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.worker_mode_advance_consumes_selector_and_availability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

WorkerModeAdvanceConsumesSelection model quantifies over an advance from chooseWorkerMode to thinkingPanelWorkers. Every such model.transition yields a carrier selected by model.fallbackSelector from workerModeEligibility and the empty tried set, together with evidence that the selected carrier is available and is not abstain.

The theorem does not say that an advance exists for every configuration; it extracts the three pieces of evidence from an advance transition that already exists.

**Theorem 1.8 (Before-launch fallback and empty-history abstention are pinned).**

$$\operatorname{ConcreteChooseWorkerModeRouting}\left(inlineConsensusModel\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.concrete_choose_worker_mode_routing_is_pinned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ConcreteChooseWorkerModeRouting inlineConsensusModel first records that nyxidOnlyAvailable rejects codexCli, accepts nyxidOracle, and makes the model's fallbackSelector choose nyxidOracle from an empty tried set.

Its final conjunct supplies an abstain transition at chooseWorkerMode for the noWorkerAvailable configuration. The resulting state is abstained, its attemptedFlights set is empty, and workerAttemptHistory for that abstain event is the empty list. This is a before-launch pin, not a claim about a later failed flight.

**Theorem 1.9 (Stale-permit rejection and fresh reevaluation are pinned).**

$$\operatorname{ConcretePermitRecovery}\left(inlineConsensusModel\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.stale_permit_cannot_finish_and_fresh_evaluation_is_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ConcretePermitRecovery inlineConsensusModel supplies a reevaluated state for the named permitInvalidatedState. It states that this state has no terminationExit, does not satisfy FinishPrecondition, and has an outgoing terminationGate transition using freshTerminationObservation.

The fixture defines permitInvalidatedState with recordEvent after an intervening flight failure, and intervening_failure_clears_current_permit separately proves that invalidating ProtocolStep. The recovery theorem does not claim that the fresh evaluation's result is permitClaim.

**Theorem 1.10 (The inline-consensus model models every clause).**

$$\forall clause,\ \operatorname{ModelsClause}\left(inlineConsensusModel, clause\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusProtocolPins.inline_consensus_model_models_every_clause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem states forall clause, ModelsClause inlineConsensusModel clause. ClauseId has ten constructors, and ModelsClause is a function of the governing model whose branches state the corresponding indexed protocol obligations.

For inlineConsensusModel the ten branches include the stage algebra, selector and dispatch obligations, retry commitments, completion evidence, absorbing abstention, isolation and artifact conditions, the S7 independence contrast, model-routed transition witnesses, termination safety and freshness, and shared-budget bounds. This theorem is clause coverage for this concrete model; it does not assert ModelsClause for every InlineConsensusModel.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.complete_goal_snapshot_is_accepted`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.concrete_choose_worker_mode_routing_is_pinned`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.empty_visible_fields_are_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.full_snapshot_with_wrong_artifact_is_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.inline_consensus_model_models_every_clause`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.mismatched_initial_plan_is_rejected`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.protocol_initial_plan_is_compatible`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.stale_permit_cannot_finish_and_fresh_evaluation_is_reachable`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.two_distinct_complete_goal_artifacts_exist`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusProtocolPins.worker_mode_advance_consumes_selector_and_availability`
- Dependency: [D5/S0/History/Consensus/InlineConsensusProtocolFixtures](InlineConsensusProtocolFixtures.md)
