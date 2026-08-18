# Paid Information and Full Revelation

## Abstract

Positive costly information production conflicts with a fully revealing price.

**Proposition 1.1 (Costly private information and full revelation cannot coexist).**

$$(\forall state,\ Equilibrium(state) \land PositiveProduction(state) \land FullyRevealing(state) \Rightarrow \exists agent, PaidTrade(state)(agent)) \land\\(\forall state, agent,\ Equilibrium(state) \land FullyRevealing(state) \Rightarrow MarginalGrossBenefit(state)(agent) = 0) \land\\(\forall state, agent,\ Equilibrium(state) \land PositiveProduction(state) \land PaidTrade(state)(agent) \Rightarrow cost \leq MarginalGrossBenefit(state)(agent)) \land 0 < cost \Rightarrow\\\neg\exists state,\ Equilibrium(state) \land PositiveProduction(state) \land FullyRevealing(state).$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PaidInformationIncentiveConflict.paid_information_full_revelation_conflict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that a state with positive private-information production and a fully revealing price identifies at least one paid information trader. Full revelation makes every agent's marginal gross trading benefit from the private information equal to zero.

The equilibrium incentive condition is stated explicitly: positive paid information production requires the identified trader's marginal gross benefit to be at least the information cost. This makes the economic content of equilibrium machine-visible.

When the information cost is strictly positive, the incentive condition would put that positive cost below zero. Therefore no equilibrium state can have both positive private-information production and a price that fully reveals the information.

Pinned Mathlib and Loogle returned the exact order theorem not_le_of_gt, which closes the contradiction directly. Repository search found adjacent pricing modules but no theorem for this incentive conflict; LeanSearch returned HTTP 404.

## References

- Truth anchor: `D5/S3/ResourceOrder/PaidInformationIncentiveConflict.paid_information_full_revelation_conflict`
