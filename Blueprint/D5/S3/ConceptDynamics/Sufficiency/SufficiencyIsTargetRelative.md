# Sufficiency Is Target-Relative

## Abstract

Sufficiency is relative to a target family: three concrete upgrades defeat interfaces sufficient for their coarser targets, while finite-state future windows are recorded to stabilize.

**Theorem 1.1 (Decision sufficiency does not recover the payoff profile).**

$$\begin{gathered}qDec: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(2\right) = \operatorname{fst},\\{}TPay: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right) = \operatorname{id},\\{}\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(qDec\right), qDec\right) \land\\{}\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(TPay\right), qDec\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.decision_target_sufficient_but_payoff_profile_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state space is the four-element product Fin(2) times Fin(2). Both the interface and the decision target read the first coordinate, so the target is constant on every interface fiber.

The complete payoff profile is the identity readout. The states (0, 0) and (0, 1) have the same interface value but different profiles, so the same interface is not sufficient for that strictly richer target.

**Theorem 1.2 (Interventional marginals do not recover counterfactual joints).**

$$\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(Int\right), Int\right) \land\\{}\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(CF\right), Int\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For deterministic Boolean structural causal models, the interface is the table of single-world interventional outcome counts. It is sufficient for that same marginal target by fiber constancy.

The existing strict-kernel witness supplies two concrete models with equal interventional tables but unequal unit-level counterfactual tables. Hence the interface is not sufficient for the cross-world joint target.

**Theorem 1.3 (Every finite prefix omits some future).**

$$\begin{gathered}\forall n: \mathbb{N},\\{}\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{finiteFutureWindow}\left(n\right)\right), \operatorname{finiteFutureWindow}\left(n\right)\right) \land\\{}\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(fullFuture\right), \operatorname{finiteFutureWindow}\left(n\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_window_sufficient_but_all_future_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state is an infinite Boolean stream. For each natural horizon n, the interface records times zero through n and is sufficient for that finite-prefix target, including when n is zero.

A constantly false stream and a stream with one pulse at time n + 1 have the same observed prefix but different complete futures. Thus every fixed finite interface in the family fails for the all-future target.

**Lemma 1.4 (Finite-state future windows stabilize).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\operatorname{Finite}\left(X\right), F: X \to X, q: X \to O,\\{}\operatorname{finiteFutureRelation}\left(F, q, \operatorname{observationStabilityDepth}\left(F, q\right)\right) = \operatorname{infiniteFutureRelation}\left(F, q\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_state_windows_stabilize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite state carrier, arbitrary update, and arbitrary readout, the finite-future relation at the canonical stability depth equals the relation of agreement at every future time.

This reused stabilization theorem explains why the preceding witness uses an infinite state space. Its statement also covers empty and singleton carriers, identity updates, and constant readouts.

**Lemma 1.5 (Finite state is necessary for window stabilization).**

$$\begin{gathered}\neg \operatorname{Finite}\left(InfiniteFuture\right) \land\\{}\forall n: \mathbb{N},\\{}\operatorname{finiteFutureRelation}\left(streamShift, streamHead, n\right) \neq \operatorname{infiniteFutureRelation}\left(streamShift, streamHead\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_state_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the state space of infinite Boolean streams, update by left shift and observe the head. At any finite depth n, the zero stream and a stream pulsing first at n + 1 remain equivalent.

Their all-future observations differ at that next time. Therefore no finite relation reaches the all-future relation in this system; combining strictness with finite-state stabilization proves that the stream carrier is not finite.

**Theorem 1.6 (Sufficiency is relative to the target family).**

$$(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(decisionTarget\right), decisionInterface\right) \land \neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(payoffProfile\right), decisionInterface\right)) \land\\{}(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(interventionMarginal\right), interventionMarginal\right) \land \neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(counterfactualJoint\right), interventionMarginal\right)) \land\\{}(\forall n: \mathbb{N}, \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{finiteFutureWindow}\left(n\right)\right), \operatorname{finiteFutureWindow}\left(n\right)\right) \land \neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(fullFuture\right), \operatorname{finiteFutureWindow}\left(n\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.sufficiency_is_target_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three witnesses are conjoined. They respectively upgrade a decision target to a complete payoff profile, interventional marginals to a counterfactual joint, and a fixed finite prefix to the complete future.

Each upgrade invalidates an interface that is sufficient for the coarser target. Sufficiency must therefore carry an explicit target family rather than functioning as an unsubscripted property.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.decision_target_sufficient_but_payoff_profile_not`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_state_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_state_windows_stabilize`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.finite_window_sufficient_but_all_future_not`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.sufficiency_is_target_relative`
- Dependency: [D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner](../Interventions/CounterfactualKernelStrictlyFiner.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](UniversalSufficiencyFactorization.md)
- Dependency: [D5/S3/Observer/Separation/FiniteHistoryStability](../../Observer/Separation/FiniteHistoryStability.md)
