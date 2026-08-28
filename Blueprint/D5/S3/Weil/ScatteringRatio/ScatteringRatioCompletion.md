# Scattering-Ratio Completion

## Abstract

Scattering-ratio readings together with right-shift normalization determine the function.

**Theorem 1.1 (Scattering ratios determine a normalized function).**

$$\forall F: \mathbb{C}\to \mathbb{C}, \forall G: \mathbb{C}\to \mathbb{C}, \left(\forall z \in \mathbb{C},\; F(z) \ne 0\right) \land \left(\left(\forall z \in \mathbb{C},\; G(z) \ne 0\right) \land \left(\left(\forall s \in \mathbb{C},\; \frac{F(2 \cdot s - 1)}{F(2 \cdot s)} = \frac{G(2 \cdot s - 1)}{G(2 \cdot s)}\right) \land \left(\forall z \in \mathbb{C},\; \lim_{n\to\infty} \frac{F(z + n)}{G(z + n)} = 1\right)\right)\right) \Rightarrow F = G$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ScatteringRatio/ScatteringRatioCompletion.scattering_ratio_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed hypotheses keep the source ratio observation explicit: the values of F and G are nonzero, their shifted ratios agree, and the quotient F(z+n)/G(z+n) tends to one along every right shift.

Evaluating the ratio identity at (z+1)/2 gives one-step periodicity of F/G. Iteration and the right-shift limit force that quotient to equal one at every z, hence F=G.

## References

- Truth anchor: `D5/S3/Weil/ScatteringRatio/ScatteringRatioCompletion.scattering_ratio_completion`
