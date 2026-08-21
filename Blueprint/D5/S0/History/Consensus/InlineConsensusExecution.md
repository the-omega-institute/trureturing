# Inline Consensus Execution

## Abstract

Uniform independence separates a correlated carrier pair from constant pairs; event-fresh permits and recorded worker attempts govern finite executions.

**Theorem 1.1 (Constant conclusion pairs are uniformly independent).**

$$ConstantConclusionsAreIndependent$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.constant_conclusions_are_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ConstantConclusionsAreIndependent is the proposition that for every two Boolean values, the two constant conclusion functions satisfy UniformIndependent. The theorem proves that proposition for all four pairs; it does not claim independence for arbitrary conclusion functions.

**Theorem 1.2 (The heterogeneous correlated pair violates independence).**

$$\neg \operatorname{UniformIndependent}\left(\operatorname{correlatedConclusion}\left(codexCli\right), \operatorname{correlatedConclusion}\left(nyxidOracle\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.heterogeneous_correlated_conclusions_are_not_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem refutes UniformIndependent for the concrete codexCli and nyxidOracle correlatedConclusion functions. Each function returns its latent Boolean world, so each true count and the joint true count are one, while the uniform two-world equation would require two to equal one.

Thus the differently labelled carrier pair is proved dependent in this model. The preceding theorem supplies the contrasting degenerate case: every pair of constant conclusion functions satisfies the same independence equation.

**Theorem 1.3 (Every event clears a carried permit).**

$$\forall model, config, start, final, event,\ start.terminationExit = \operatorname{some}\left(permitClaim\right) \Rightarrow \operatorname{ProtocolStep}\left(model, config, start, event, final\right) \Rightarrow final.terminationExit \neq \operatorname{some}\left(permitClaim\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.every_protocol_event_clears_carried_permit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any governing model and any ProtocolStep, a permitClaim carried in the source state's terminationExit cannot remain as permitClaim in the final state. The proof unfolds recordEvent, whose carried-permit branch clears both the exit and its permit epoch.

**Theorem 1.4 (Carried-permit invalidation is recoverable).**

$$\forall model,\ \operatorname{RecoverablePermitInvalidation}\left(model\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.carried_permit_invalidation_is_recoverable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RecoverablePermitInvalidation model quantifies over a carried permit and an invalidating model.transition. Given the stated budget, well-formedness, live and isolation state, current done review, authorized fresh observation, and remaining-pass hypotheses, it concludes that a fresh terminationGate model.transition from the invalidated state has some reevaluated target.

The theorem is conditional on every premise in that predicate. It proves reachability of a fresh evaluation, not that the evaluation necessarily returns permitClaim.

**Theorem 1.5 (A fix prevents the repaired state from being finish-ready).**

$$\forall model, config, start, attempted, repaired,\ \operatorname{ProtocolStep}\left(model, config, start, \operatorname{boundedPass}\left(start.stage, fixPass, attempted\right), repaired\right) \Rightarrow \neg\operatorname{FinishPrecondition}\left(repaired\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.no_stale_termination_permit_after_fix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every model, configuration, source state, and attempted-flight set, a fix-pass ProtocolStep produces a repaired state that does not satisfy FinishPrecondition. This is the negation of the complete finish-readiness conjunction; it does not assert which individual conjunct fails.

**Theorem 1.6 (Termination evaluation requires a current done review).**

$$\forall model, config, state, attempted, final,\ \operatorname{ProtocolStep}\left(model, config, state, \operatorname{boundedPass}\left(state.stage, terminationGate, attempted\right), final\right) \Rightarrow state.reviewExit = \operatorname{some}\left(done\right) \land state.reviewEpoch = \operatorname{some}\left(state.artifactEpoch\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.termination_gate_requires_current_done_review` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A termination-gate transition can be taken only when its source state records a done review whose epoch equals that state's artifact epoch. The conclusion constrains the source state; it does not by itself state which termination exit the resulting state records.

**Theorem 1.7 (The termination router is sound, maximal, unique, and strictly bracketed).**

$$\operatorname{Sound}\left(inlineConsensusModel, optimalTerminationRule\right)\\ \land (\forall rule,\ \operatorname{Sound}\left(inlineConsensusModel, rule\right) \Rightarrow \operatorname{RuleLE}\left(rule, optimalTerminationRule\right))\\ \land (\forall rule,\ \operatorname{Greatest}\left(inlineConsensusModel, rule\right) \Rightarrow rule = optimalTerminationRule)\\ \land \operatorname{Sound}\left(inlineConsensusModel, alwaysAbstain\right)\\ \land \operatorname{StrictBelow}\left(alwaysAbstain, optimalTerminationRule\right)\\ \land \operatorname{StrictBelow}\left(optimalTerminationRule, majorityAdmit\right)\\ \land \neg\operatorname{Sound}\left(inlineConsensusModel, majorityAdmit\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.termination_router_sound_maximal_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sound inlineConsensusModel means that every admitted observation is free of TerminationHazard inlineConsensusModel. The second conjunct says every rule sound for that model is pointwise below optimalTerminationRule. The third says any Greatest rule for that model equals optimalTerminationRule; it does not assert uniqueness for a weaker or differently defined ordering.

The remaining four conjuncts make both comparisons substantive. alwaysAbstain is sound and lies strictly below optimalTerminationRule, with safeAdmittedObservation witnessing strictness. majorityAdmit is strictly more permissive than optimalTerminationRule but is not sound; hazardousMajorityObservation witnesses both the strict comparison and the soundness failure.

The proof identifies permit observations with an exact roster whose three named results are all satisfied, then uses Mathlib's IsGreatest.unique for the final equality. The proposition is internal to the Lean model and makes no claim about a current or future external plugin version.

**Definition 1.8 (No carrier reopened covers all recorded worker attempts).**

Lean statement: `D5/S0/History/Consensus/InlineConsensusExecution.NoCarrierReopened`

*Formalization.* `D5/S0/History/Consensus/InlineConsensusExecution.NoCarrierReopened` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NoCarrierReopened events is exactly Nodup over workerAttemptHistory events. Event.workerAttemptKeys records the singleton key of a flightFailure, every attempted key carried by an advance, and every attempted key carried by a boundedPass; finish and abstain contribute no keys.

The predicate therefore covers failed flights, successful advances, and bounded passes. It is not the older failure-only property.

**Theorem 1.9 (Maximal runs preserve budgets and have an explicit length bound).**

$$\forall config, run: \operatorname{MaximalRun}\left(inlineConsensusModel, config\right),\ \operatorname{WithinRetryBudgets}\left(config, run.events\right)\\ \land \operatorname{NoCarrierReopened}\left(run.events\right)\\ \land \operatorname{sharedPassCount}\left(run.events\right) \le config.sharedPassBudget\\ \land \operatorname{length}\left(run.events\right) \le \operatorname{explicitRunBound}\left(config\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.every_maximal_run_is_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every MaximalRun of inlineConsensusModel, each flight-failure event has a positive attempt number equal to its configured retry budget. workerAttemptHistory has no duplicate FlightKey across failure, advance, and bounded-pass events; the number of bounded-pass events does not exceed the shared-pass budget; and the event-list length does not exceed explicitRunBound config.

The explicit bound is the cardinality of FlightKey plus seven stage/live credits plus the configured shared-pass budget. The proof derives all four conjuncts from the guarded execution. It makes no terminal-reachability claim: MaximalRun supplies maximality, but the stated conclusion is exactly the retry, uniqueness, shared-pass, and length conjunction above.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.NoCarrierReopened`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.carried_permit_invalidation_is_recoverable`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.constant_conclusions_are_independent`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.every_maximal_run_is_bounded`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.every_protocol_event_clears_carried_permit`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.heterogeneous_correlated_conclusions_are_not_independent`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.no_stale_termination_permit_after_fix`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.termination_gate_requires_current_done_review`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.termination_router_sound_maximal_unique`
- Dependency: [D5/S0/History/Consensus/InlineConsensusOptimality](InlineConsensusOptimality.md)
