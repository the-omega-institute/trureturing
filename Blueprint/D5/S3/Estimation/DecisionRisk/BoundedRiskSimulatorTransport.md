# Bounded-Risk Simulator Transport

## Abstract

Uniform simulation error bounds the statewise risk increase of every bounded-loss rule.

**Theorem 1.1 (A total-variation simulator transports every bounded-loss decision rule).**

$$\begin{gathered}\forall X, O, R, A,\\{}\operatorname{Fintype}(X), \operatorname{Nonempty}(X), \operatorname{Fintype}(O),\\{}\operatorname{Fintype}(R), \operatorname{Fintype}(A),\\{}K: X \to O \to \mathbb{R}, L: X \to R \to \mathbb{R},\\{}M: O \to R \to \mathbb{R}, d: R \to A \to \mathbb{R},\\{}ell: X \to A \to \mathbb{R}, epsilon: \mathbb{R},\\{}(\operatorname{IsRowStochastic}(K) \land \operatorname{IsRowStochastic}(L) \land \operatorname{IsRowStochastic}(M) \land \operatorname{IsRowStochastic}(d) \land\\{}(\forall x: X, a: A, 0 \leq ell(x, a) \land ell(x, a) \leq 1) \land \operatorname{sup}(x, \operatorname{TV}(L(x), \operatorname{channelOutput}(M, K(x)))) \leq epsilon) \Rightarrow\\{}\operatorname{let}(dK(o)(a) := \operatorname{channelOutput}(d, M(o))(a))\;\\{}\operatorname{IsRowStochastic}(dK) \land\\{}\forall x: X, \operatorname{sum}(a, \operatorname{channelOutput}(dK, K(x))(a) \cdot ell(x, a)) \leq \operatorname{sum}(a, \operatorname{channelOutput}(d, L(x))(a) \cdot ell(x, a)) + epsilon.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.bounded_loss_risk_stability_of_simulator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state, observation, simulated-observation, and action carriers are finite, with a nonempty state carrier. K and L are experiments, M is the simulator, and d is an arbitrary randomized decision rule based on L; all four are row-stochastic.

The transported rule is the canonical composition: after observing K, apply M and then d. Its row-stochasticity is part of the public conclusion, so the transported object is exposed rather than hidden behind an existence claim.

For every loss taking values between zero and one, the finite supremum of the rowwise total-variation simulation error bounds the increase of expected loss separately at every state.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.bounded_loss_risk_stability_of_simulator`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](DescentDefectBounds.md)
