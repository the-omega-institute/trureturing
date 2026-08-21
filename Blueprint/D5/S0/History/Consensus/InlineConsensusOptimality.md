# Inline Consensus Optimality

## Abstract

Carrier selection identifies every available priority minimum, configurations certify their initial dispatch plans, and model transitions are derived from protocol steps.

**Theorem 1.1 (Carrier selection is available and identifies every priority minimum).**

$$\forall eligible, tried,\ \operatorname{Nonempty}\left(\operatorname{eligibleUntried}\left(eligible, tried\right)\right) \Rightarrow \operatorname{selectCarrier}\left(eligible, tried\right) \in \operatorname{eligibleUntried}\left(eligible, tried\right)\\ \land \forall other,\ other \in \operatorname{eligibleUntried}\left(eligible, tried\right) \Rightarrow (\forall carrier,\ carrier \in \operatorname{eligibleUntried}\left(eligible, tried\right) \Rightarrow \operatorname{priorityRank}\left(other\right) \le \operatorname{priorityRank}\left(carrier\right)) \Rightarrow other = \operatorname{selectCarrier}\left(eligible, tried\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusOptimality.selectCarrier_is_unique_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever the eligible carriers not yet tried form a nonempty finite set, selectCarrier belongs to that set. Any other available carrier whose priority rank is no greater than every available carrier's rank must equal the selected carrier.

The result is conditional on a nonempty eligible-untried set. It does not say that a worker carrier is always available, and the separate exhaustion row selects abstain when that set is empty.

**Theorem 1.2 (Single-perspective consensus is rejected).**

$$\operatorname{designRouter}\left(singlePerspective\right) = rejectFakeConsensus$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusOptimality.design_router_rejects_single_perspective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singlePerspective row of designRouter returns rejectFakeConsensus. This equation states one router row; it does not supply an independent design hazard predicate or a design-router maximality theorem.

**Definition 1.3 (Protocol configurations certify their initial plans).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusOptimality.ProtocolConfig`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusOptimality.ProtocolConfig` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ProtocolConfig stores worker-mode eligibility, stage-and-role eligibility, retry-budget functions, a DispatchPlan, a GoalArtifact, the shared-pass budget and its owner-authorization flag, and the initial isolation status. Its initialPlanCompatible field is a proof of InitialPlanCompatible eligible dispatchPlan, so plan compatibility is part of every configuration value.

**Theorem 1.4 (A legal untried role has an eligible planned carrier or selects abstain).**

$$\forall model, config, state, role,\ \operatorname{LegalAt}\left(role, state.stage\right) \Rightarrow \operatorname{triedAt}\left(state, state.stage, role\right) = \varnothing \Rightarrow ((\exists carrier,\ \operatorname{InitiallyAssigned}\left(config, state, role, carrier\right) \land \operatorname{CarrierLegalAt}\left(state.stage, role, carrier\right) \land config.eligible(state.stage, role, carrier) = true) \lor model.fallbackSelector(config.eligible(state.stage, role), \operatorname{triedAt}\left(state, state.stage, role\right)) = abstain)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusOptimality.legal_worker_stage_initially_progresses_or_abstains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a role legal at the state's stage, if no carrier has yet been tried for that role, the conclusion is a disjunction: either some carrier is the initially assigned, stage-legal, eligible carrier, or the model's fallbackSelector on the same eligibility and tried set returns abstain.

The proof uses DispatchPlan.carrierAt for the legal role and the configuration's initialPlanCompatible proof to establish the existential left disjunct. It does not claim progress for a role that is illegal at the current stage.

**Definition 1.5 (The model transition is derived from ProtocolStep).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusOptimality.transition`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusOptimality.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

InlineConsensusModel.transition model is definitionally ProtocolStep model. It therefore accepts a ProtocolConfig, source state, Event, and final state, and the relation is parameterized by that governing model. The relevant action, authorization, and routing branches consume the model's dispatch, completion, selector, stage, and router projections.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.ProtocolConfig`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.design_router_rejects_single_perspective`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.legal_worker_stage_initially_progresses_or_abstains`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.selectCarrier_is_unique_minimum`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.transition`
- Dependency: [D5/S0/History/Consensus/InlineConsensusProtocolCore](InlineConsensusProtocolCore.md)
