# Finite Realization Certificate

## Abstract

Every unrealizable real protocol signature has a finite strict linear certificate.

**Theorem 1.1 (Unrealizable signatures have finite linear witnesses).**

$$\begin{aligned}\forall State, Protocol: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(State)], [\operatorname{AddCommGroup}(State)], [\operatorname{Module}(\mathbb{R}, State)],\\\forall X: \operatorname{Set}(State),\\{}\operatorname{IsCompact}(X) \land \operatorname{Convex}(\mathbb{R}, X),\\\forall e: Protocol \to \operatorname{ContinuousAffineMap}(\mathbb{R}, State, \mathbb{R}), y: Protocol \to \mathbb{R},\\{}let Sigma: State \to Protocol \to \mathbb{R} = \operatorname{jointReadout}(e);\\\neg (y \in \operatorname{image}(Sigma, X)) \Rightarrow\\{}\exists S: \operatorname{Finset}(Protocol), \exists c: Protocol \to \mathbb{R},\\{}\operatorname{withBotCoe}(\sum_{p \in S} \operatorname{apply}(c, p) \cdot \operatorname{apply}(y, p)) > \operatorname{supWithBot}_{x \in X} \operatorname{withBotCoe}(\sum_{p \in S} \operatorname{apply}(c, p) \cdot \operatorname{apply}(e, p, x)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Residuals/FiniteRealizationCertificate.finite_realization_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact convex state set and its continuous affine real readouts construct the realization image through the canonical joint readout.

Strict separation produces a continuous linear functional on the product signature space. Continuity at zero forces that functional to depend on only finitely many protocol coordinates.

The displayed lower-completion coercions make the supremum equal negative infinity when the state set is empty. For every nonempty state set, they reduce to the ordinary attained real supremum.

## References

- Truth anchor: `D5/S3/Observer/Residuals/FiniteRealizationCertificate.finite_realization_certificate`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
