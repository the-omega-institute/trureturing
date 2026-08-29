# Resolvent Parity Signatures

## Abstract

Local spectral correlations have a hyperbolic difference mode with opposite parity signs.

**Theorem 1.1 (Local completion difference).**

$$\forall L \in \operatorname{Real}\left(\right), a \in \operatorname{Real}\left(\right), nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), mu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), Dnu \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), Dmu \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), source \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \left(0 < L \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{InOpenInterval}\left(t, \operatorname{neg}\left(2 \cdot L\right), 2 \cdot L\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{lambda}\left(t, \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, nu\right)\right), Dnu\left(t\right), t\right)\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{InOpenInterval}\left(t, \operatorname{neg}\left(2 \cdot L\right), 2 \cdot L\right) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{lambda}\left(t, \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, mu\right)\right), Dmu\left(t\right), t\right)\right) \land \left(\left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{InOpenInterval}\left(t, \operatorname{neg}\left(2 \cdot L\right), 2 \cdot L\right) \Rightarrow \operatorname{HasDerivAt}\left(Dnu, a^{2} \cdot \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, nu\right) + source\left(t\right), t\right)\right) \land \left(\forall t \in \operatorname{Real}\left(\right),\; \operatorname{InOpenInterval}\left(t, \operatorname{neg}\left(2 \cdot L\right), 2 \cdot L\right) \Rightarrow \operatorname{HasDerivAt}\left(Dmu, a^{2} \cdot \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, mu\right) + source\left(t\right), t\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall t \in \operatorname{Real}\left(\right),\; \left|t\right| < 2 \cdot L \Rightarrow \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, nu\right) - \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(t \cdot xi\right)}{xi^{2} + a^{2}}, mu\right) = \left(\operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(0 \cdot xi\right)}{xi^{2} + a^{2}}, nu\right) - \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \frac{\operatorname{cos}\left(0 \cdot xi\right)}{xi^{2} + a^{2}}, mu\right)\right) \cdot \operatorname{cosh}\left(a \cdot t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/ResolventParitySignatures.local_completion_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correlations are constructed directly from the two real spectral measures. Shared local Green derivative data cancels in their difference, while the cosine kernel supplies evenness.

**Theorem 1.2 (Hyperbolic cosine correlation signature).**

$$\forall a \in \operatorname{Real}\left(\right), f \in \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right), h \in \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right),\; \left(\operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), f\right) \land \left(\operatorname{HasCompactSupport}\left(f\right) \land \left(\operatorname{ContDiff}\left(\operatorname{Real}\left(\right), \operatorname{infinity}\left(\right), h\right) \land \operatorname{HasCompactSupport}\left(h\right)\right)\right)\right) \Rightarrow \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{cosh}\left(a \cdot t\right)\right) \cdot \operatorname{convolution}\left(f, \operatorname{lambda}\left(x, \operatorname{conj}\left(h\left(-x\right)\right)\right)\right)\left(t\right), \operatorname{volume}\left(\right)\right) = \operatorname{integral}\left(x, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{cosh}\left(a \cdot x\right)\right) \cdot f\left(x\right), \operatorname{volume}\left(\right)\right) \cdot \operatorname{conj}\left(\operatorname{integral}\left(x, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{cosh}\left(a \cdot x\right)\right) \cdot h\left(x\right), \operatorname{volume}\left(\right)\right)\right) - \operatorname{integral}\left(x, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{sinh}\left(a \cdot x\right)\right) \cdot f\left(x\right), \operatorname{volume}\left(\right)\right) \cdot \operatorname{conj}\left(\operatorname{integral}\left(x, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{sinh}\left(a \cdot x\right)\right) \cdot h\left(x\right), \operatorname{volume}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/ResolventParitySignatures.cosh_correlation_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For smooth compactly supported complex functions, the convolution with involution is paired directly against the hyperbolic cosine kernel. The two bilateral exponential identities yield the positive even channel product minus the odd channel product.

## References

- Truth anchor: `D5/S3/Weil/ZetaCore/ResolventParitySignatures.cosh_correlation_signature`
- Truth anchor: `D5/S3/Weil/ZetaCore/ResolventParitySignatures.local_completion_difference`
