# Strict shear monotonicity

## Abstract

The planar theta function strictly decreases in the shear coordinate on the reduced half-strip at every positive temperature.

**Theorem 1.1 (Negative shear derivative).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall x \in \mathbb{R},\; 0 < t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \left(0 < x \Rightarrow \left(x < \frac{1}{2} \Rightarrow \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, z, y\right)), x\right) < 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaShearMonotonicity.shear_derivative_neg` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Poisson summation in the first integer coordinate rewrites the planar theta series as the square root of y over t times a sum of one-dimensional Fourier theta functions. Pairing positive and negative second coordinates isolates a constant zero row. A Gaussian first moment bounds the row derivatives uniformly, so termwise differentiation is valid. Write s equal to y over t and v equal to t y. The first row contributes a negative term of size A times exp of negative pi v times sin of two pi x; the remaining rows contribute at most B times the same factors times the normalized Gaussian tail at v. For s at least one half, take A = 4 pi exp(-pi s) (1 - G(s)) and B = 4 pi exp(-pi s) (1 + G(s)), where G is the normalized Gaussian tail. The bound G(s) < 1/15 and the tail bound at v give B times gaussianTail(v) < A. For s at most one half, the strengthened small-parameter derivative bounds again give a positive first-row margin against the tail. The relation v s equal to y squared makes the exponentially scaled tail less than one over thirty-nine thousand nine hundred ninety-nine. Thus the first row dominates in both cases when t is at least one. Reciprocal-temperature duality transfers the strict sign to every positive temperature. This is the shear step of the proof of Montgomery's planar theta theorem.

**Theorem 1.2 (Unique horizontal minimum).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \forall x \in \mathbb{R},\; 0 < t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \left(0 \le x \Rightarrow \left(x \le \frac{1}{2} \Rightarrow \left(\operatorname{F}\left(t, \frac{1}{2}, y\right) \le \operatorname{F}\left(t, x, y\right) \land \left(\operatorname{F}\left(t, x, y\right) = \operatorname{F}\left(t, \frac{1}{2}, y\right) \Leftrightarrow x = \frac{1}{2}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaShearMonotonicity.shear_minimum` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The Gaussian series is differentiable and hence continuous in the shear parameter. Its derivative is negative at every point in the interior of the closed interval from zero to one half. The mean value theorem therefore gives strict decrease on the whole closed interval, including its endpoints. The right endpoint is the unique horizontal minimizer.

## References

- Truth anchor: `D5/S3/Fourier/ThetaShearMonotonicity.shear_derivative_neg`
- Truth anchor: `D5/S3/Fourier/ThetaShearMonotonicity.shear_minimum`
- Dependency: [D5/S3/Fourier/ThetaDerivativeBounds](ThetaDerivativeBounds.md)
