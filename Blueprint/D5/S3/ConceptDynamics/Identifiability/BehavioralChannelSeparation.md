# Behavioral Channel Separation

## Abstract

Opposite strict reports require a type-dependent behavioral channel.

**Theorem 1.1 (Strict behavioral separation exposes a differing channel).**

$$\begin{aligned}\forall Theta, R, O: \operatorname{Type},\\theta, theta_{prime}: Theta, r_{theta}, r_{theta_{prime}}: R,\\M: R \to O,\\u: Theta \to O \to \mathbb{R}, v, c, e: Theta \to R \to \mathbb{R},\\(u(theta, M(r_{theta})) + v(theta, r_{theta}) - c(theta, r_{theta}) + e(theta, r_{theta}) > u(theta, M(r_{theta_{prime}})) + v(theta, r_{theta_{prime}}) - c(theta, r_{theta_{prime}}) + e(theta, r_{theta_{prime}}) \land\\u(theta_{prime}, M(r_{theta_{prime}})) + v(theta_{prime}, r_{theta_{prime}}) - c(theta_{prime}, r_{theta_{prime}}) + e(theta_{prime}, r_{theta_{prime}}) > u(theta_{prime}, M(r_{theta})) + v(theta_{prime}, r_{theta}) - c(theta_{prime}, r_{theta}) + e(theta_{prime}, r_{theta})) \Rightarrow\\(\exists o: O, u(theta, o) \neq u(theta_{prime}, o)) \lor\\(\exists r: R, v(theta, r) \neq v(theta_{prime}, r)) \lor\\(\exists r: R, c(theta, r) \neq c(theta_{prime}, r)) \lor\\(\exists r: R, e(theta, r) \neq e(theta_{prime}, r)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identifiability/BehavioralChannelSeparation.behavioral_identification_requires_channel_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A report score is constructed from the mechanism outcome preference, verification effect, report cost, and external effect. Each channel is supplied independently on the source type and report carriers.

If the two types strictly prefer opposite reports, at least one channel must differ between them. Otherwise the common verification, cost, and external terms combine into a homogeneous report cost, and the frozen strict-separation impossibility theorem gives a contradiction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identifiability/BehavioralChannelSeparation.behavioral_identification_requires_channel_difference`
- Dependency: [D5/S3/ConceptDynamics/StrictSeparationImpossibility](../StrictSeparationImpossibility.md)
