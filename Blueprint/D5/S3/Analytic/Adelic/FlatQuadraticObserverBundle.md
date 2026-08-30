# Flat Quadratic Observer Bundle

## Abstract

One compatible jet and constant second derivative determine a positive quadratic operator bundle.

**Theorem 1.1 (A common self-adjoint operator generates every quadratic fiber).**

$$\forall B \in \operatorname{Type}\left(\right), A \in \operatorname{Real}\left(\right) \to B, velocity \in \operatorname{Real}\left(\right) \to B, t0 \in \operatorname{Real}\left(\right),\; \left(\operatorname{CStarAlgebra}\left(B\right) \land \left(\operatorname{PartialOrder}\left(B\right) \land \left(\operatorname{StarOrderedRing}\left(B\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{HasDerivAt}\left(A, velocity\left(t\right), t\right)\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{HasDerivAt}\left(velocity, \operatorname{smul}\left(2, \operatorname{one}\left(B\right)\right), t\right)\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{IsSelfAdjoint}\left(A\left(t\right)\right)\right) \land A\left(t0\right) = \operatorname{smul}\left(\frac{1}{4}, \operatorname{sq}\left(velocity\left(t0\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow let H: B = \operatorname{algebraMap}\left(\operatorname{Real}\left(\right), B, t0\right) - \operatorname{smul}\left(\frac{1}{2}, velocity\left(t0\right)\right); \operatorname{IsSelfAdjoint}\left(H\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; A\left(t\right) = \operatorname{sq}\left(H - \operatorname{algebraMap}\left(\operatorname{Real}\left(\right), B, t\right)\right)\right) \land \left(\forall t \in \operatorname{Real}\left(\right),\; 0 \le \operatorname{sq}\left(H - \operatorname{algebraMap}\left(\operatorname{Real}\left(\right), B, t\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/FlatQuadraticObserverBundle.flat_quadratic_observer_bundle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family A and its named velocity live in one partially ordered C-star algebra. Their two derivative laws encode a constant second derivative equal to twice the identity operator.

Self-adjointness of the entire family makes the velocity at the base point self-adjoint. The displayed compatible jet then fixes the integration constants and constructs the single operator H.

The resulting affine square agrees with A at every real parameter. Because its affine factor is self-adjoint, every displayed square is positive. The closing determinant and Stieltjes paragraph in the source is an interpretation question outside the named theorem.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/FlatQuadraticObserverBundle.flat_quadratic_observer_bundle`
