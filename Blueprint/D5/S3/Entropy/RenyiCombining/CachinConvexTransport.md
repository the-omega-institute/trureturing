# Transport to Squared-Bias Elasticity

## Abstract

The real-power elasticity transform equals the Riccati denominator elasticity in squared-bias coordinates.

Use the auxiliary functions C and D of the Riccati branch, and define D1(n,z)=deriv(C_n)(z)+n. The Lean declaration for this function uses the subscript spelling D₁. For 0<r<1 the bias t=(1-r)/(1+r) also belongs to (0,1).

**Theorem 1.1 (The two elasticity formulas agree).**

$$\forall n, \forall r, 0 < n \land r \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{F}\left(n, r\right) = \operatorname{elasticity}\left(\operatorname{D}\left(n\right), \operatorname{D1}\left(n\right), \frac{1 - r}{1 + r}^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexTransport.F_eq_denominator_elasticity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hyperbolic quotient gives C_n(t^2)=nt(1+r^n)/(1-r^n). Substitute this identity into A_n(r) and B_n(r), and use the Riccati derivative of C_n. The result identifies F_n(r) with 1-2zD_n'(z)/D_n(z), where z=t^2. All denominators are nonzero because n>0 and 0<r<1. The certificate for positive parameters combines this identity with monotonicity of the squared-bias elasticity.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexTransport.F_eq_denominator_elasticity`
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexBranch](CachinConvexBranch.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone](CachinElasticityMonotone.md)
