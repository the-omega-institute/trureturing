# Positive-Parameter Convexity Certificate

## Abstract

The Riccati quotient gives the convex-branch elasticity comparison for every real parameter between zero and one quarter.

Write n = alpha - 1, with 0 < n <= 1/4. The auxiliary function is C_n(z)=n sqrt(z) coth(n artanh(sqrt(z))), extended by C_n(0)=1. Set D_n(z)=C_n(z)+nz. The analytic quotient and its exact initial jets provide a neighborhood where C_n''<0 and C_n'<-n. The first-zero argument propagates the negative curvature across (0,1).

**Theorem 1.1 (Strict negative curvature).**

$$\forall n, 0 < n \land n \le \frac{1}{4} \Rightarrow \forall z, z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{iteratedDeriv}\left(2, \operatorname{C}\left(n\right), z\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.C_secondDeriv_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a first zero of C_n'', the twice-differentiated Riccati identity forces C_n'''<0, contradicting the nonnegative left derivative at that first crossing.

**Theorem 1.2 (Derivative of the denominator).**

$$\forall n, 0 < n \Rightarrow \forall z, z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{D}\left(n\right), \operatorname{D1}\left(n, z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D1(n,z) is defined as deriv(C_n)(z)+n. Differentiating D_n=C_n+nz gives this derivative.

**Theorem 1.3 (Derivative of the denominator slope).**

$$\forall n, 0 < n \Rightarrow \forall z, z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{D1}\left(n\right), \operatorname{iteratedDeriv}\left(2, \operatorname{C}\left(n\right), z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D1_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of D1 is C_n'', which is strictly negative in the required parameter range.

**Theorem 1.4 (Strict decrease of the denominator).**

$$\forall n, 0 < n \land n \le \frac{1}{4} \Rightarrow \forall z, z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{D1}\left(n, z\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D1_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator slope is strictly decreasing. Its negative initial neighborhood therefore forces it to remain negative everywhere.

**Theorem 1.5 (Strict increase of squared-bias elasticity).**

$$\forall n, 0 < n \land n \le \frac{1}{4} \Rightarrow \operatorname{StrictMonoOn}\left(\operatorname{elasticity}\left(\operatorname{D}\left(n\right), \operatorname{D1}\left(n\right)\right), \operatorname{Ioo}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.elasticity_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For E(z)=1-2zD'(z)/D(z), differentiation gives E'=-2D'/D-2zD''/D+2z(D')^2/D^2. The first two terms are positive, and the last is nonnegative.

**Theorem 1.6 (Decrease of the original elasticity transform).**

$$\forall n, 0 < n \land n \le \frac{1}{4} \Rightarrow \operatorname{AntitoneOn}\left(\operatorname{F}\left(n\right), \operatorname{Ioo}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.antitoneOn_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-power transform F(n,r) equals the denominator elasticity at z=((1-r)/(1+r))^2. That coordinate decreases with r, so the strictly increasing squared-bias elasticity gives antitonicity of F. This is the positive-parameter certificate consumed by the convex clause of Hirche's Conjecture IV.18.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.C_secondDeriv_neg`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D1_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D1_neg`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.D_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.antitoneOn_F`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.elasticity_strictMonoOn`
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexLocal](CachinConvexLocal.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexTransport](CachinConvexTransport.md)
