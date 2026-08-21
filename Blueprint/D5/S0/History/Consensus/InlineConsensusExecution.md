# Inline Consensus Execution

## Abstract

Executions preserve retry uniqueness and finite budgets, while the optimal termination rule is uniquely greatest and strictly bracketed by concrete competitors.

**Theorem 1.1 (A fix prevents the repaired state from being finish-ready).**

$$\forall config, start, repaired,\ \operatorname{ProtocolStep}\left(config, start, \operatorname{boundedPass}\left(start.stage, fixPass\right), repaired\right) \Rightarrow \neg\operatorname{FinishPrecondition}\left(repaired\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.no_stale_termination_permit_after_fix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fix-pass ProtocolStep, the repaired state does not satisfy FinishPrecondition. This is the negation of the complete finish-readiness conjunction; it does not assert that either termination field is none, and it does not assert that the repaired state has no outgoing finish transition.

**Theorem 1.2 (Termination evaluation requires a current done review).**

$$\forall config, state, final,\ \operatorname{ProtocolStep}\left(config, state, \operatorname{boundedPass}\left(state.stage, terminationGate\right), final\right) \Rightarrow state.reviewExit = \operatorname{some}\left(done\right) \land state.reviewEpoch = \operatorname{some}\left(state.artifactEpoch\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.termination_gate_requires_current_done_review` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A termination-gate transition can be taken only when its source state records a done review whose epoch equals that state's artifact epoch. The conclusion constrains the source state; it does not by itself state which termination exit the resulting state records.

**Theorem 1.3 (The termination router is sound, maximal, unique, and strictly bracketed).**

$$\operatorname{Sound}\left(optimalTerminationRule\right)\\ \land (\forall rule,\ \operatorname{Sound}\left(rule\right) \Rightarrow \operatorname{RuleLE}\left(rule, optimalTerminationRule\right))\\ \land (\forall rule,\ \operatorname{Greatest}\left(rule\right) \Rightarrow rule = optimalTerminationRule)\\ \land \operatorname{Sound}\left(alwaysAbstain\right)\\ \land \operatorname{StrictBelow}\left(alwaysAbstain, optimalTerminationRule\right)\\ \land \operatorname{StrictBelow}\left(optimalTerminationRule, majorityAdmit\right)\\ \land \neg\operatorname{Sound}\left(majorityAdmit\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.termination_router_sound_maximal_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Soundness means that every admitted observation is free of the Lean TerminationHazard. The second conjunct says every sound rule is pointwise below optimalTerminationRule. The third says any Greatest sound rule equals optimalTerminationRule; it does not assert uniqueness for a weaker or differently defined ordering.

The remaining four conjuncts make both comparisons substantive. alwaysAbstain is sound and lies strictly below optimalTerminationRule, with safeAdmittedObservation witnessing strictness. majorityAdmit is strictly more permissive than optimalTerminationRule but is not sound; hazardousMajorityObservation witnesses both the strict comparison and the soundness failure.

The proof identifies permit observations with an exact roster whose three named results are all satisfied, then uses Mathlib's IsGreatest.unique for the final equality. The proposition is internal to the Lean model and makes no claim about a current or future external plugin version.

**Theorem 1.4 (Maximal runs preserve budgets and have an explicit length bound).**

$$\forall config, run: \operatorname{MaximalRun}\left(inlineConsensusModel, config\right),\ \operatorname{WithinRetryBudgets}\left(config, run.events\right)\\ \land \operatorname{NoCarrierReopened}\left(run.events\right)\\ \land \operatorname{sharedPassCount}\left(run.events\right) \le config.sharedPassBudget\\ \land \operatorname{length}\left(run.events\right) \le \operatorname{explicitRunBound}\left(config\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusExecution.every_maximal_run_is_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every MaximalRun of inlineConsensusModel, each flight-failure event has a positive attempt number within its configured retry budget, the list of attempted stage-role-carrier keys has no duplicates, the number of bounded-pass events does not exceed the shared-pass budget, and the event-list length does not exceed explicitRunBound config.

The explicit bound is the cardinality of FlightKey plus seven stage/live credits plus the configured shared-pass budget. The proof derives all four conjuncts from the guarded execution. It makes no terminal-reachability claim: MaximalRun supplies maximality, but the stated conclusion is exactly the retry, uniqueness, shared-pass, and length conjunction above.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.every_maximal_run_is_bounded`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.no_stale_termination_permit_after_fix`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.termination_gate_requires_current_done_review`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusExecution.termination_router_sound_maximal_unique`
- Dependency: [D5/S0/History/Consensus/InlineConsensusOptimality](InlineConsensusOptimality.md)
