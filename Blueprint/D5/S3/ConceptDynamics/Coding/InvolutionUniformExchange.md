# Involution uniform exchange

## Abstract

A finite-group involution supplies nonnegative exchange factors for a nonuniform perturbation of the uniform element.

**Theorem 1.1 (Reverse the factors to the uniform target).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), s \in H, t \in H, involution \in s \cdot s = 1,\; \operatorname{rightFactor}\left(s\right) \cdot \operatorname{leftFactor}\left(s, t\right) = \operatorname{target}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange.factors_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write u for the sum of all group elements and b(g) for a group-ring basis element. The explicit integral factors are U=u+(1-b(s))b(t) and V=1+b(s). Every coefficient of U is 1 plus one indicator minus one indicator, so both factors are nonnegative.

The forward product is 2u+(1-b(s))b(t)(1+b(s)). Reversing the factors gives 2u because s squared is the identity. Converting the nonnegative coefficients to natural numbers provides genuine natural-coefficient group-ring factors.

When s and t do not commute, the coefficient at t distinguishes the two endpoints. The counted companion module performs the coefficientwise conversion and constructs the exact one-step exchange.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange.factors_reverse`
