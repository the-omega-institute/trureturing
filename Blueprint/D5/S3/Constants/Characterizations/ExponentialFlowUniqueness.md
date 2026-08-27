# Exponential Flow Uniqueness

## Abstract

A positive normalized multiplicative C1 flow is the real exponential.

**Theorem 1.1 (The normalized exponential flow is unique).**

$$\forall E: \mathbb{R} \to \mathbb{R},\\((\forall t\in \mathbb{R}, 0 < E(t)) \land E \in C^{1}(\mathbb{R}, \mathbb{R}) \land (\forall x, y\in \mathbb{R}, E(x + y) = E(x)E(y)) \land E'(0) = 1)\\ \Rightarrow \forall x\in \mathbb{R}, E(x) = e^{x}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Characterizations/ExponentialFlowUniqueness.exponential_flow_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict positivity condition is the real-valued encoding of the source codomain of positive reals. Together with C1 regularity, the multiplicative Cauchy equation, and the derivative value one at zero, it gives exactly the hypotheses of the formal theorem.

Differentiating the flow equation in its second argument at zero shows that the derivative of E equals E. The quotient of E by the real exponential then has zero derivative everywhere. Positivity fixes E at zero to one, so the quotient is identically one and E(1)=e.

## References

- Truth anchor: `D5/S3/Constants/Characterizations/ExponentialFlowUniqueness.exponential_flow_unique`
