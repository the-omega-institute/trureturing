# Explicit-Formula Obstruction to a Finite Zero Carrier

## Abstract

The frozen unconditional explicit formula rules out every finite zero carrier, so the nontrivial zeta-zero set is infinite and ZeroData is inhabited.

This closes the zero-infinitude argument of 增订三十 by contradiction. For a finite carrier, the zero side of the frozen explicit formula tends to zero along the cosine-modulated packet. Its right side instead diverges because the Archimedean term grows, while the pole terms vanish and the fixed-support prime term stays bounded.

Applied to the repository's canonical zetaZeroConfig and its frozen unconditional EF_lit theorem, this proves that the full set of nontrivial zeta zeros is infinite. It is not Hardy's theorem asserting infinitely many zeros on the critical line.

The Nonempty ZeroData theorem is a bind-only companion obtained through the frozen M1-a bridge. Neither zero infinitude nor that companion proves the Riemann hypothesis.

**Theorem 1.1 (The modulated transform is the translated real packet).**

$$\forall T \in \mathbb{R}, r \in \mathbb{R},\; \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), r\right) = {\operatorname{packet}\left((t: \mathbb{R} \mapsto \Re (\operatorname{paperFT}\left(packetSquare, t\right))), T, r\right): \mathbb{C}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.paperFT_cosineModulation_packet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the real axis, reality of the convolution-square transform identifies the complex transform with the real translated-packet profile.

**Theorem 1.2 (The real packet transform has quadratic decay).**

$$\exists K \in \mathbb{R},\; 0 \le K \land \left(\forall x \in \mathbb{R},\; \left|\Re (\operatorname{paperFT}\left(packetSquare, x\right))\right| \le \frac{K}{1 + x^{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.packetTransform_re_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen closed-strip estimate dominates the absolute real part by the same quadratic majorant.

**Theorem 1.3 (The explicit formula forces an infinite carrier).**

$$\forall Z \in ZeroConfig,\; \operatorname{EFlit}\left(Z\right) \Rightarrow \operatorname{Infinite}\left(\operatorname{carrier}\left(Z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.carrier_infinite_of_EF_lit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite zero-side limit and the divergent literature right-hand side cannot both be the real part of the frozen explicit-formula identity.

**Theorem 1.4 (The canonical carrier is the nontrivial-zero set).**

$$\operatorname{carrier}\left(zetaZeroConfig\right) = \left\{\operatorname{IsNontrivialZero}\left(\rho\right) \mid \rho \in \mathbb{C}\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.zetaZeroConfig_carrier_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This public bridge binds the frozen carrier identification for zetaZeroConfig.

**Theorem 1.5 (The nontrivial zeta-zero set is infinite).**

$$\operatorname{Infinite}\left(\left\{\operatorname{IsNontrivialZero}\left(\rho\right) \mid \rho \in \mathbb{C}\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.isNontrivialZero_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen unconditional explicit formula instantiates the carrier theorem, and the canonical carrier identification transports infinitude.

**Theorem 1.6 (ZeroData is inhabited).**

$$\operatorname{Nonempty}\left(ZeroData\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.nonempty_zeroData` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the bind-only direction from zero infinitude through the frozen ZeroData nonemptiness equivalence.

## References

- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.carrier_infinite_of_EF_lit`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.isNontrivialZero_infinite`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.nonempty_zeroData`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.packetTransform_re_decay`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.paperFT_cosineModulation_packet`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.zetaZeroConfig_carrier_identification`
- Dependency: [D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence](ArchimedeanDivergence.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/CosinePacket](CosinePacket.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite](../ZetaBridge/ZeroDataNonemptyIffInfinite.md)
