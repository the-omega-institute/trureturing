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

**Lemma 1.2 (Composition preserves stochastic rows).**

$$\forall K, D, {}\operatorname{IsRowStochastic}(K) \land \operatorname{IsRowStochastic}(D) \Rightarrow \operatorname{IsRowStochastic}((i, o \mapsto \operatorname{channelOutput}(D, K(i))(o)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.row_stochastic_channel_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here I is an arbitrary type and M and O are finite types; K : I → M → ℝ and D : M → O → ℝ. The displayed composite is indexed by i : I and o : O.

For arbitrary input types and finite intermediate and output types, composing two nonnegative unit-row matrices gives another nonnegative unit-row matrix. The inner row sum reduces the composite row sum to the first matrix's row sum.

**Lemma 1.3 (Finite channel output is associative).**

$$\forall K, D, p, \operatorname{channelOutput}((i, o \mapsto \operatorname{channelOutput}(D, K(i))(o)), p) = \operatorname{channelOutput}(D, \operatorname{channelOutput}(K, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.channel_output_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here I and M are finite types and O is an arbitrary type; K : I → M → ℝ, D : M → O → ℝ and p : I → ℝ. The displayed composite is indexed by i : I and o : O.

For finite input and intermediate types and an arbitrary output type, applying a composite real matrix to a real mass agrees with two successive channel outputs. This is a finite distributive identity and requires no positivity or normalization.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.bounded_loss_risk_stability_of_simulator`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.channel_output_comp`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.row_stochastic_channel_comp`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](DescentDefectBounds.md)
