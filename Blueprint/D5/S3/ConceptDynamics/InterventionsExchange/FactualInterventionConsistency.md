# Factual Intervention Consistency

## Abstract

A factual outcome agrees with the potential outcome at the matching treatment.

**Theorem 1.1 (The factual outcome agrees with the matching intervention).**

$$\begin{gathered}\forall U, X, Y: \operatorname{Type},\\{}f: U \to X \to Y, XFact: U \to X,\\{}u: U, x: X,\\{}XFact(u) = x \Rightarrow\\{}\operatorname{let}(YFact := f(u, XFact(u)), YPot(xPrime) := f(u, xPrime))\;\\{}YFact = YPot(x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/FactualInterventionConsistency.factual_intervention_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factual and intervened outcomes are evaluations of one shared structural mechanism at the same exogenous state.

When the factual treatment equals the imposed value, equality transport through that mechanism identifies the outcomes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/FactualInterventionConsistency.factual_intervention_consistency`
