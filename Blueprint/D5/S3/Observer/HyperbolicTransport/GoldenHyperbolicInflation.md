# Golden Visible-Hidden Hyperbolic Transport

## Abstract

Golden inflation expands the visible face and contracts the conjugate residual.

**Theorem 1.1 (Golden visible-hidden hyperbolic transport).**

$$\forall V, H \in \operatorname{Mod}_{\mathbb{R}},\ \forall n \in \mathbb{N},\ \forall x \in V \times H,\ goldenInflation^{n}(x) = (\varphi^{n} \cdot x_{parallel}, \varphi'^{n} \cdot x_{\perp}) \land \left(epsilon_{n} = \varphi^{-n} \land \left(epsilon_{n} = \left|\varphi'\right|^{n} \land \left(0 < epsilon_{1} \land epsilon_{1} < 1\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HyperbolicTransport/GoldenHyperbolicInflation.golden_visible_hidden_hyperbolic_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let epsilon_n denote endogenousResidualScale n. For every pair of real visible and hidden modules, the nth inflation step scales the visible coordinate by phi^n and the hidden coordinate by the nth power of the Galois conjugate phi-prime.

The remaining four conjuncts identify epsilon_n with phi^(-n), identify the same value with |phi-prime|^n, and state that the one-step residual scale is positive and strictly below one. Thus the small parameter is the conjugate multiplier itself, not an independently supplied perturbation.

At n=0 the scale is one, as required for zero iterations. The strict contraction assertion is attached to the one-step scale, so the zero-iteration case does not hollow out the theorem.

## References

- Truth anchor: `D5/S3/Observer/HyperbolicTransport/GoldenHyperbolicInflation.golden_visible_hidden_hyperbolic_transport`
- Dependency: [D5/S1/Scale/FibonacciEigen](../../../S1/Scale/FibonacciEigen.md)
