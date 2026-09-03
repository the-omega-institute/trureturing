# Unimodular Transfer Chebyshev Identity

## Abstract

Unimodular two-by-two transfer power traces realize first-kind Chebyshev values.

**Theorem 1.1 (Trace powers and Chebyshev slack).**

$$\begin{aligned}\forall M: SL_{2}(\mathbb{C}), N\in \mathbb{N},\\{}let x: \mathbb{C} = \frac{1}{2} \times \operatorname{tr}\left(M\right);\\{}\frac{1}{2} \times \operatorname{tr}\left(M^{N}\right) = \left(T_{N}\right)\left(x\right) \land\\{}1 - {\left(T_{N}\right)\left(x\right)}^{2} = -\frac{1}{4} \times (\operatorname{tr}\left(M^{N}\right)^{2} - 4).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/UnimodularTransferChebyshevIdentity.unimodular_transfer_chebyshev_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen two-by-two trace-power theorem reduces the matrix power trace to the power sum of the roots of its characteristic quadratic. Mathlib's Dickson identity then identifies that sum with the first-kind Chebyshev polynomial.

Substitution of the trace identity gives the displayed slack equality by polynomial arithmetic.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/UnimodularTransferChebyshevIdentity.unimodular_transfer_chebyshev_identities`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
