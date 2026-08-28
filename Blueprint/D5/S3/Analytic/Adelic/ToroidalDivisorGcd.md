# Toroidal Divisor GCD

## Abstract

Pointwise nonvanishing analytic twists identify the zero divisor of xi with the pointwise infimum of its normalized toroidal-period divisors.

**Theorem 1.1 (Xi is the divisor-gcd of normalized toroidal periods).**

$$\forall Index \in \operatorname{Type}\left(\right), rho \in \operatorname{Complex}\left(\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index,\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), T\left(i\right)\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right) \Rightarrow \left(\operatorname{analyticOrderAt}\left(xiReading, rho\right) = \operatorname{iInf}\left(i, \operatorname{analyticOrderAt}\left(xiReading \times T\left(i\right), rho\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{analyticOrderAt}\left(xiReading, s\right) = \operatorname{iInf}\left(i, \operatorname{analyticOrderAt}\left(xiReading \times T\left(i\right), s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalDivisorGcd.toroidal_divisor_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized period family is constructed directly as the canonical xi reading times an analytic twist; it is not an additional primitive or a factorization premise.

Analytic vanishing order is additive on each product. Pointwise nonvanishing supplies one twist of order zero, while every other product order is bounded below by the xi order.

The first conclusion is the prescribed order identity at rho. The second states the corresponding divisor identity at every complex point, with indexed infimum representing pointwise gcd.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalDivisorGcd.toroidal_divisor_gcd`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
