# Complementary Contact Support

## Abstract

A zero complementary gap localizes residual support on entire contact zeros.

**Theorem 1.1 (Complementary contact support).**

$$\forall a \in \operatorname{Real}\left(\right), theta \in \operatorname{Real}\left(\right), phi \in \operatorname{WeilTestFunction}\left(\right), mu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right),\; \left(\left(\left(\left(\left(0 < a \land 0 \le theta\right) \land \left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{conj}\left(phi\left(x\right)\right) = phi\left(x\right)\right)\right) \land \left(\forall xi \in \operatorname{Real}\left(\right),\; 0 \le \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{xi^{2} + a^{2}}\right)\right) \land \operatorname{Integrable}\left((xi: \operatorname{Real}\left(\right) \mapsto \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{xi^{2} + a^{2}}), mu\right)\right) \land \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{xi^{2} + a^{2}}, mu\right) = 0\right) \Rightarrow \operatorname{let} S = (xi: \operatorname{Real}\left(\right) \mapsto \operatorname{realPart}\left(\operatorname{fourierLaplace}\left(phi, xi\right)\right) + \frac{theta}{xi^{2} + a^{2}}); \operatorname{let} G = (z: \operatorname{Complex}\left(\right) \mapsto \left(z^{2} + a^{2}\right) \cdot \operatorname{fourierLaplace}\left(phi, z\right) + theta); \left(\left(\operatorname{support}\left(mu\right) \subseteq \left\{S\left(xi\right) = 0 \mid xi \in \operatorname{Real}\left(\right)\right\} \land \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), G\right)\right) \land \left(\exists C \in \operatorname{Real}\left(\right), tau \in \operatorname{Real}\left(\right),\; \left(0 \le C \land 0 \le tau\right) \land \left(\forall z \in \operatorname{Complex}\left(\right),\; \operatorname{norm}\left(G\left(z\right)\right) \le C \cdot \operatorname{exp}\left(tau \cdot \operatorname{norm}\left(z\right)\right)\right)\right)\right) \land \operatorname{support}\left(mu\right) \subseteq \left\{G\left(xi\right) = 0 \mid xi \in \operatorname{Real}\left(\right)\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/ComplementaryContactSupport.complementary_contact_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contact gap is constructed from the canonical Fourier-Laplace transform and the positive resolvent denominator. Pointwise nonnegativity and a zero integral force it to vanish throughout the residual support.

Clearing the denominator constructs the complex contact function. Compact support makes the transform entire and supplies an explicit finite exponential bound after multiplication by the quadratic factor.

Reality of the even test makes the transform real on the real axis, so the first support localization transfers to the real zeros of the entire contact function.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/ComplementaryContactSupport.complementary_contact_support`
