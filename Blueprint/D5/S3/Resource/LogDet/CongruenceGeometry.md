# Congruence Geometry of the Log-Determinant Divergence

## Abstract

The log-determinant divergence is invariant under invertible congruence, satisfies a three-point identity, and is not symmetric.

The total matrix definition remains invariant when both arguments are transformed by the same invertible congruence. No invertibility assumption on sigma is needed: nonsingular matrix inversion reverses products unconditionally, while the single hypothesis on T supplies exactly the cancellations used by the resulting similarity.

**Theorem 1.1 (Log-det divergence is invariant under invertible congruence).**

$$\operatorname{IsUnit}(\operatorname{det}(T)) \Rightarrow \operatorname{logDetDivergence}(T \rho T^{H}, T \sigma T^{H}) = \operatorname{logDetDivergence}(\rho, \sigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/CongruenceGeometry.logDetDivergence_conjugate_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After expanding the inverse of T sigma T conjugate-transpose, the quotient is similar to sigma inverse times rho through T conjugate-transpose. Trace cycling and determinant multiplicativity remove that similarity, including when sigma is singular under the total junk-value convention.

**Theorem 1.2 (Log-det divergence satisfies the three-point identity).**

$$\operatorname{PosDef}(\rho) \land \operatorname{PosDef}(\sigma) \land \operatorname{PosDef}(\tau) \Rightarrow \operatorname{logDetDivergence}(\rho, \sigma) + \operatorname{logDetDivergence}(\sigma, \tau) - \operatorname{logDetDivergence}(\rho, \tau) = \Re{\operatorname{tr}((\sigma^{-1} - \tau^{-1}) (\rho - \sigma))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/CongruenceGeometry.logDetDivergence_three_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three applications of the barrier Bregman identity cancel every barrier height. Distributing the remaining matrix products and using linearity of the trace leaves the stated inverse-difference pairing.

**Theorem 1.3 (Log-det divergence is not symmetric).**

$$\exists \rho, \sigma: \operatorname{Matrix}(\operatorname{Fin}(1), \operatorname{Fin}(1), \mathbb{C}), \operatorname{PosDef}(\rho) \land \operatorname{PosDef}(\sigma) \land \operatorname{logDetDivergence}(\rho, \sigma) \neq \operatorname{logDetDivergence}(\sigma, \rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/LogDet/CongruenceGeometry.exists_logDetDivergence_ne_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension one, take rho to be the diagonal matrix with entry two and sigma to be the identity. Both are positive definite, while equality of the two divergence orders would force three halves minus twice log two to vanish. The certified upper bound for log two makes that quantity strictly positive.

## References

- Truth anchor: `D5/S3/Resource/LogDet/CongruenceGeometry.exists_logDetDivergence_ne_swap`
- Truth anchor: `D5/S3/Resource/LogDet/CongruenceGeometry.logDetDivergence_conjugate_congr`
- Truth anchor: `D5/S3/Resource/LogDet/CongruenceGeometry.logDetDivergence_three_point`
- Dependency: [D5/S3/Resource/LogDetDivergence](../LogDetDivergence.md)
