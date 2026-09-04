# Cosine-Modulated Packet

## Abstract

A normalized convolution-square Weil packet has positive transform near zero, and cosine modulation gives uniform prime control and finite-side decay.

This is the packet half of the zero-infinitude argument of 增订三十. The explicit formula EF_lit holds for every ZeroConfig regardless of carrier cardinality; only the packet, its modulation, and the finite-side limits are proved here.

The prime bound needs neither Chebyshev nor the prime number theorem, because the support of the cosine-modulated packet is fixed. The test functions are this repository's WeilTestFunction.

No statement about zeta's zeros beyond the finite-carrier limit is made here. In particular, this document is not a proof of the Riemann hypothesis.

**Definition 1.1 (The normalized packet seed).**

$$\forall x \in \mathbb{R},\; \operatorname{packetSeed}\left(x\right) = \operatorname{standardBumpNormed}\left(volume, x\right)$$

*Formalization.* `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSeed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is the repository's canonical volume-normalized smooth bump.

**Theorem 1.2 (The seed is normalized at zero).**

$$\operatorname{fourierLaplace}\left(packetSeed, 0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSeed_fourierLaplace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its Fourier-Laplace transform at the origin is exactly one.

**Definition 1.3 (The convolution-square packet).**

$$packetSquare = \operatorname{convolutionSquare}\left(packetSeed\right)$$

*Formalization.* `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive packet is the repository convolution square of packetSeed.

**Theorem 1.4 (The packet transform is real and nonnegative).**

$$\forall t \in \mathbb{R},\; \operatorname{Im} (\operatorname{paperFT}\left(packetSquare, t\right)) = 0 \land 0 \le \Re (\operatorname{paperFT}\left(packetSquare, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_real_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the real axis, the imaginary part vanishes and the real part is nonnegative.

**Theorem 1.5 (The packet transform equals one at zero).**

$$\operatorname{paperFT}\left(packetSquare, 0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Convolution-square positivity combines with seed normalization at the origin.

**Theorem 1.6 (The packet transform is integrable).**

$$\operatorname{Integrable}\left((t: \mathbb{R} \mapsto \operatorname{paperFT}\left(packetSquare, t\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two derivatives and compact support give real-axis integrability.

**Theorem 1.7 (The packet transform stays above one half near zero).**

$$\exists delta \in \mathbb{R},\; 0 < delta \land \left(\forall t \in \mathbb{R},\; \left|t\right| \le delta \Rightarrow \frac{1}{2} \le \Re (\operatorname{paperFT}\left(packetSquare, t\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_ge_half_near_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity at the normalized value one supplies a positive neighborhood.

**Definition 1.8 (Cosine modulation of a Weil test function).**

$$\forall q \in WeilTestFunction, T \in \mathbb{R}, x \in \mathbb{R},\; \operatorname{cosineModulation}\left(q, T, x\right) = \operatorname{cos}\left(T \cdot x\right) \cdot \operatorname{apply}\left(q, x\right)$$

*Formalization.* `D5/S3/Weil/ZeroInfinitude/CosinePacket.cosineModulation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by cos(Tx) preserves smoothness, compact support, and evenness.

**Theorem 1.9 (Cosine modulation shifts the transform).**

$$\forall q \in WeilTestFunction, T \in \mathbb{R}, z \in \mathbb{C},\; \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(q, T\right), z\right) = \frac{\operatorname{paperFT}\left(q, z + T\right) + \operatorname{paperFT}\left(q, z - T\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two frequency shifts occur with equal coefficient one half.

**Theorem 1.10 (The modulated transform decays pointwise on the unit strip).**

$$\forall z \in \mathbb{C},\; \left|\operatorname{Im} (z)\right| \le 1 \Rightarrow \operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), z\right)), atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closed-strip quadratic decay sends both translated packet transforms to zero.

**Theorem 1.11 (The positive pole specialization tends to zero).**

$$\operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), \frac{i}{2}\right)), atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_pole_pos_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the pointwise strip limit specialized to positive i over two.

**Theorem 1.12 (The negative pole specialization tends to zero).**

$$\operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), -\frac{i}{2}\right)), atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_pole_neg_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the pointwise strip limit specialized to negative i over two.

**Theorem 1.13 (The modulated prime term has a uniform bound).**

$$\exists B \in \mathbb{R},\; \forall T \in \mathbb{R},\; \left\lVert \sum_{n \in \mathbb{N}} \frac{\operatorname{vonMangoldt}\left(n\right)}{\operatorname{sqrt}\left(n\right)} \cdot \left(\operatorname{cosineModulation}\left(packetSquare, T, \operatorname{log}\left(n\right)\right) + \operatorname{cosineModulation}\left(packetSquare, T, -\operatorname{log}\left(n\right)\right)\right) \right\rVert \le B$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.primeTerm_cosineModulation_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed compact support reduces the prime series to one finite carrier, while the cosine factor has absolute value at most one.

**Theorem 1.14 (Every finite-carrier zero side tends to zero).**

$$\forall Z \in ZeroConfig,\; \operatorname{Finite}\left(\operatorname{carrier}\left(Z\right)\right) \Rightarrow \operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \sum_{rho \in \operatorname{carrier}\left(Z\right)} \operatorname{mult}\left(Z, rho\right) \cdot \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), \operatorname{gammaOf}\left(rho\right)\right)), atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/CosinePacket.finiteCarrier_zeroSide_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise strip decay passes through the finite multiplicity-weighted sum.

## References

- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.cosineModulation`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.finiteCarrier_zeroSide_tendsto_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSeed`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSeed_fourierLaplace_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetSquare`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_ge_half_near_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_integrable`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_real_nonneg`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.packetTransform_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_pole_neg_tendsto_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_pole_pos_tendsto_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.paperFT_cosineModulation_tendsto_zero`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/CosinePacket.primeTerm_cosineModulation_bounded`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation](../TestFunctions/EvenTestFunctionFiniteInterpolation.md)
- Dependency: [D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay](../TestFunctions/FourierLaplaceClosedStripDecay.md)
