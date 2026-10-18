# Positive-Parameter Convexity Certificate

## Abstract

The Riccati quotient gives the convex-branch elasticity comparison for every real parameter between zero and one quarter.

Write n = alpha - 1, with 0 < n <= 1/4. The auxiliary function is C_n(z)=n sqrt(z) coth(n artanh(sqrt(z))), extended by C_n(0)=1. Set D_n(z)=C_n(z)+nz. The analytic quotient and its exact initial jets provide a neighborhood where C_n''<0 and C_n'<-n. The first-zero argument propagates the negative curvature across (0,1).

**Theorem 1.1 (Decrease of the original elasticity transform).**

$$\forall n, 0 < n \land n \le \frac{1}{4} \Rightarrow \operatorname{AntitoneOn}\left(\operatorname{F}\left(n\right), \operatorname{Ioo}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.antitoneOn_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-power transform F(n,r) equals the denominator elasticity at z=((1-r)/(1+r))^2. That coordinate decreases with r, so the strictly increasing squared-bias elasticity gives antitonicity of F. This is the positive-parameter certificate consumed by the convex clause of Hirche's Conjecture IV.18.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.antitoneOn_F`
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone](CachinElasticityMonotone.md)
- Dependency: [D5/S3/QuantumChannels/ContractionSpectrumOrder](../../QuantumChannels/ContractionSpectrumOrder.md)
