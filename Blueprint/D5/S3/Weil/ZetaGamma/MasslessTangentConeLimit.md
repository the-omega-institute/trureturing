# Massless Tangent-Cone Limit

## Abstract

The logarithmic Archimedean tower has the universal massless tangent symbol.

**Definition 1.1 (The logarithmic tower dispersion).**

$$\forall sigma, lambda\in \mathbb{R}, \phi_{sigma}(lambda) = \sum_{m=0}^{\infty} \operatorname{log}\left(1 + \frac{lambda}{(sigma + 2m)^{2}}\right).$$

*Formalization.* `D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit.archimedean_dispersion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function is constructed directly as the infinite sum over the source scales sigma plus twice the natural index.

**Theorem 1.2 (The scaled tower converges to the massless symbol).**

$$\begin{aligned}\forall sigma\in \mathbb{R}, 0 < sigma \Rightarrow\\{}[\forall lambda\in \mathbb{R}, 0 \leq lambda \Rightarrow \lim_{\varepsilon\to0^{+}} \varepsilon \phi_{sigma}(\frac{lambda}{\varepsilon^{2}}) = \frac{\pi}{2} \sqrt{lambda}] \land\\{}[\forall n\in \mathbb{N}, k: \operatorname{Fin}\left(n\right) \to \mathbb{R}, c\in \operatorname{FiniteFourierBand}\left(n\right), \lim_{\varepsilon\to0^{+}} \operatorname{M}\left(j \mapsto \varepsilon \phi_{sigma}(\frac{k(j)^{2}}{\varepsilon^{2}})\right)(c) = \operatorname{M}\left(j \mapsto \frac{\pi}{2} \left|k(j)\right|\right)(c)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit.massless_tangent_cone_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive sigma, monotone sum-integral comparison traps the tower between an explicit integral and that integral plus its first summand. Both scaled bounds converge to pi over two.

The second public conjunct is the operator clause on a concrete finite Fourier coefficient space. For every finite frequency band and every coefficient vector, the diagonal continuous linear multipliers converge in the coefficient-space norm, which is strong operator convergence on each fixed band. The claim does not assert bounded operator-norm convergence on the whole L2 circle, where the limiting absolute-frequency multiplier is unbounded.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit.archimedean_dispersion`
- Truth anchor: `D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit.massless_tangent_cone_limit`
