# Empirical Identifiability

## Abstract

Protocol outcomes determine exactly which model properties descend uniquely.

**Theorem 1.1 (Empirical quotient descent and residual obstruction).**

$$\forall P, Theta, Y,\ Out: P \to Theta \to \operatorname{Type}, T: Theta \to Y,\ ((\exists! d: Theta_{emp} \to Y, T(theta) = d(class(theta))) \iff (\forall theta, thetaPrime,\ (\forall P, Out(P)(theta) = Out(P)(thetaPrime)) \Rightarrow T(theta) = T(thetaPrime))) \land ((\exists theta, thetaPrime,\ (\forall P, Out(P)(theta) = Out(P)(thetaPrime)) \land T(theta) \neq T(thetaPrime)) \Rightarrow \neg\exists d: Theta_{emp} \to Y, T(theta) = d \circ class).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EmpiricalIdentifiability.empirical_identifiability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empirical setoid is constructed from equality of every allowed protocol outcome, and the quotient and class map are the canonical ones for that source relation.

A property descends to exactly one quotient map precisely when it is constant on every empirical-equivalence fiber. An empirically equivalent pair with different property values rules out every possible quotient factor.

Pinned quotient constructors were applied directly; no source object is defined as the target conclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EmpiricalIdentifiability.empirical_identifiability`
