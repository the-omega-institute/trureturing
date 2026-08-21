# Inline Consensus Optimality

## Abstract

Carrier selection is the unique available priority minimum, and the design router rejects single-perspective consensus.

**Theorem 1.1 (Carrier selection is the unique available priority minimum).**

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

The design router maps exactly the singlePerspective situation to the rejectFakeConsensus exit. This equation states one router row; it does not supply an independent design hazard predicate or a design-router maximality theorem.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.design_router_rejects_single_perspective`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.selectCarrier_is_unique_minimum`
