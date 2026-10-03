# Uniform Power Slope

## Abstract

Power difference quotients converge uniformly on bounded nonnegative spectra, including zero.

**Theorem 1.1 (A common error bound through the zero eigenvalue).**

$$\forall K \in \mathbb{R}, \forall \varepsilon, 0 < \varepsilon \Rightarrow \exists \delta, 0 < \delta \land \forall h, (0 < \lvert h\rvert \land \lvert h\rvert < \delta) \Rightarrow \forall x \in [0, K], \lvert\frac{x^{1+h}-x}{h}-x \log x\rvert < \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope.rpow_slope_tendsto_uniformly` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For every real upper bound K and every epsilon greater than zero, there exists delta greater than zero such that every real h with 0 < abs(h) < delta and every x in [0,K] satisfy the displayed bound. The logarithm is natural. The interval may be empty; the zero endpoint is included, with x log x equal to zero there.

The proof uses a common exponential majorant near zero and a uniform exponential remainder estimate on the remaining compact positive interval. The same delta controls both signs of h. No lower positive spectral bound or state dimension assumption is imposed.

This attributed Physlib port supplies a supporting analytic estimate for singular matrix relative-entropy limits. The variable-base trace limit, noncommutative data processing, quantum Pinsker and thermal recovery remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope.rpow_slope_tendsto_uniformly`
