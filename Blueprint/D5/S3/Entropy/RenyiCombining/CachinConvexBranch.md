# Riccati Curvature Mechanism

## Abstract

A Riccati differential identity and a first-zero principle certify curvature of the binary Renyi quotient.

Use artanh(t)=(log(1+t)-log(1-t))/2. For positive n and 0<z<1 define C_n(z)=n sqrt(z) cosh(n artanh(sqrt(z)))/sinh(n artanh(sqrt(z))). The total definition fills z=0 with one and also provides the n=0 quotient sqrt(z)/artanh(sqrt(z)). This module's derivative certificates use positive n and interior z only. Set D_n=C_n+nz.

**Theorem 1.1 (The Riccati equation).**

$$\forall n, \forall z, 0 < n \land z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{C}\left(n\right), \frac{\left(1 - z\right) \cdot \operatorname{C}\left(n, z\right) - \operatorname{C}\left(n, z\right)^{2} + n^{2} \cdot z}{2 \cdot z \cdot \left(1 - z\right)}, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct differentiation gives 2z(1-z)C_n'=(1-z)C_n-C_n^2+n^2z. All quotient denominators are nonzero in the stated domain.

**Theorem 1.2 (Agreement with the real-power quotient).**

$$\forall n, \forall t, 0 < n \land t \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow \operatorname{C}\left(n, t^{2}\right) = \frac{n \cdot t \cdot \left(\left(1 + t\right)^{n} + \left(1 - t\right)^{n}\right)}{\left(1 + t\right)^{n} - \left(1 - t\right)^{n}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_eq_power_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding sinh and cosh and using the logarithmic definition of real powers identifies the hyperbolic and power quotients.

**Theorem 1.3 (Twice-differentiated Riccati equation).**

$$\forall n, \forall z, 0 < n \land z \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow 2 \cdot z \cdot \left(1 - z\right) \cdot \operatorname{iteratedDeriv}\left(3, \operatorname{C}\left(n\right), z\right) = \left(-3 + 7 \cdot z - 2 \cdot \operatorname{C}\left(n, z\right)\right) \cdot \operatorname{iteratedDeriv}\left(2, \operatorname{C}\left(n\right), z\right) + 2 \cdot \operatorname{iteratedDeriv}\left(1, \operatorname{C}\left(n\right), z\right) \cdot \left(1 - \operatorname{iteratedDeriv}\left(1, \operatorname{C}\left(n\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_curvature_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the Riccati identity twice gives 2z(1-z)C_n'''=(-3+7z-2C_n)C_n''+2C_n'(1-C_n'). At a zero of C_n'', a negative C_n' forces the right side to be strictly negative.

The generic first-zero lemmas use continuity on compact intervals to select the earliest point with nonnegative curvature. The preceding negative curvature makes the companion first derivative decrease. At the earliest zero the left difference quotients are nonnegative, while the Riccati equation requires a negative derivative. This contradiction propagates any negative initial neighborhood across the whole open interval. The positive-parameter certificate obtains that initial neighborhood from the analytic quotient jets and applies this mechanism.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_curvature_equation`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_eq_power_quotient`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexBranch.C_hasDerivAt`
