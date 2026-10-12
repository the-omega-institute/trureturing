# Finite Event Coupling Sharp Bounds

## Abstract

A two-event coupling polytope has an explicit primal witness, replayable dual-slack certificate, and exact sharp projection bounds.

The feasible object is a normalized nonnegative law on two Boolean event indicators with two prescribed marginals. Its target coordinate is the true-true intersection cell.

Normalization and the two marginal rows produce exact slack identities for the Fréchet lower plane and the two upper planes. An additional linear cap on disagreement contributes a fourth lower plane.

The explicit four-cell coupling realizes every target in the resulting closed interval. The necessity proof replays the certificate, while the sufficiency proof constructs the primal witness.

**Theorem 1.1 (Marginal rows generate a replayable dual-slack certificate).**

$$\forall mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real, leftMarginal \in Real, rightMarginal \in Real, disagreementCap \in Real,\; \operatorname{IsEventCoupling}\left(mass, leftMarginal, rightMarginal\right) \Rightarrow \operatorname{EventCouplingDualCertificate}\left(mass, leftMarginal, rightMarginal, disagreementCap\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_dual_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every feasible coupling and every proposed disagreement cap, the four exact slack identities hold. Nonnegativity and the cap can then be checked separately when the certificate is replayed.

**Theorem 1.2 (The disagreement-constrained interval is exactly sharp).**

$$\forall leftMarginal \in Real, rightMarginal \in Real, disagreementCap \in Real, target \in Real,\; \left(\operatorname{max}\left(\operatorname{max}\left(0, leftMarginal + rightMarginal - 1\right), \frac{leftMarginal + rightMarginal - disagreementCap}{2}\right) \le target \land target \le \operatorname{min}\left(leftMarginal, rightMarginal\right)\right) \Leftrightarrow \left(\exists mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real,\; \operatorname{IsEventCoupling}\left(mass, leftMarginal, rightMarginal\right) \land \left(\operatorname{disagreementMass}\left(mass\right) \le disagreementCap \land mass\left(\operatorname{pair}\left(true, true\right)\right) = target\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_target_feasible_with_disagreement_cap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real target lies in the displayed interval exactly when some normalized nonnegative coupling has the required marginals, obeys the disagreement cap, and realizes that target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_dual_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_target_feasible_with_disagreement_cap_iff`
- Dependency: [D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds](BenefitProbabilityBounds.md)
