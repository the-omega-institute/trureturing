# Fourier and Gaussian theta derivative bounds

## Abstract

The real theta Fourier series and its translated Gaussian representation give tail-sensitive derivative bounds for every positive parameter and stronger lower bounds for parameters at most pi over six.

**Definition 1.1 (Real theta Fourier series).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{thetaFourier}\left(s, b\right) = 1 + 2 \cdot \operatorname{tsum}\left((k:\mathbb{N} \mapsto \operatorname{exp}\left(-\left(\pi \cdot s \cdot \left(k + 1\right)^{2}\right)\right) \cdot \operatorname{cos}\left(2 \cdot \pi \cdot \left(k + 1\right) \cdot b\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The constant term is one. Pairing positive and negative integer frequencies produces twice the positive cosine series.

**Definition 1.2 (Sine series).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{thetaSine}\left(s, b\right) = \operatorname{tsum}\left((k:\mathbb{N} \mapsto \left(k + 1\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot s \cdot \left(k + 1\right)^{2}\right)\right) \cdot \operatorname{sin}\left(2 \cdot \pi \cdot \left(k + 1\right) \cdot b\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaDerivativeBounds.thetaSine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The positive-frequency sine series carries the factor n from differentiation in the translation parameter.

**Theorem 1.3 (Polynomial Gaussian moments).**

$$\forall s \in \mathbb{R},\; 0 < s \Rightarrow \left(\forall j \in \mathbb{N},\; \operatorname{Summable}\left((k:\mathbb{N} \mapsto \left(k + 1\right)^{j} \cdot \operatorname{exp}\left(-\left(\pi \cdot s \cdot \left(k + 1\right)^{2}\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.gaussian_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Restrict the summable integer Gaussian moments to nonnegative indices and remove the zero index. This positive-frequency moment is shared by the Fourier differentiation, the Gaussian Poisson representation, and the planar shear comparison.

**Theorem 1.4 (Cosine Gaussian convergence).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{Summable}\left((k:\mathbb{N} \mapsto \operatorname{exp}\left(-\left(\pi \cdot s \cdot \left(k + 1\right)^{2}\right)\right) \cdot \operatorname{cos}\left(2 \cdot \pi \cdot \left(k + 1\right) \cdot b\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.cos_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Every cosine factor has absolute value at most one. The zeroth Gaussian moment therefore dominates the full positive-frequency cosine series. This shared summability estimate also bounds translated theta values by their zero-translation values.

**Theorem 1.5 (Derivative of the Fourier series).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{HasDerivAt}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), -4 \cdot \pi \cdot \operatorname{thetaSine}\left(s, b\right), b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.hasDerivAt_thetaFourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Every cosine summand has derivative negative two pi n times the corresponding sine. Its absolute value is bounded independently of b by the first Gaussian moment. Comparing n squared with n gives a summable exponential majorant for every positive s, so the differentiated series sums to negative four pi times the sine series.

**Theorem 1.6 (First-mode error).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \left|\operatorname{thetaSine}\left(s, b\right) - \operatorname{exp}\left(-\left(\pi \cdot s\right)\right) \cdot \operatorname{sin}\left(2 \cdot \pi \cdot b\right)\right| \le \operatorname{exp}\left(-\left(\pi \cdot s\right)\right) \cdot \left|\operatorname{sin}\left(2 \cdot \pi \cdot b\right)\right| \cdot \operatorname{gaussianTail}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaSine_first_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The sine addition inequality bounds the absolute value of sin of n u by n times the absolute value of sin u. After separating n equal to one, each remaining term is therefore dominated by n squared times its Gaussian weight times the absolute value of sin of two pi b. Factoring out the first Gaussian gives exactly the normalized tail. Absolute convergence justifies summing the inequalities.

**Theorem 1.7 (Tail-sensitive derivative bounds).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \left(\left|\operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right)\right| \le 4 \cdot \pi \cdot \operatorname{exp}\left(-\left(\pi \cdot s\right)\right) \cdot \left|\operatorname{sin}\left(2 \cdot \pi \cdot b\right)\right| \cdot \left(1 + \operatorname{gaussianTail}\left(s\right)\right) \land \left(0 \le b \Rightarrow \left(b \le \frac{1}{2} \Rightarrow 4 \cdot \pi \cdot \operatorname{exp}\left(-\left(\pi \cdot s\right)\right) \cdot \operatorname{sin}\left(2 \cdot \pi \cdot b\right) \cdot \left(1 - \operatorname{gaussianTail}\left(s\right)\right) \le -\operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Separating the first mode gives the exact factors one plus the normalized Gaussian tail in the upper bound and one minus that tail in the lower bound. The first-mode estimate holds for every positive s. On the closed half-period the sine is nonnegative, so the lower bound includes both endpoints.

**Theorem 1.8 (Uniform sine control).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \left|\operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right)\right| \le \frac{4 \cdot \operatorname{exp}\left(-1\right)}{s} \cdot \left(\operatorname{thetaFourier}\left(\frac{s}{2}, 0\right) - 1\right) \cdot \left|\operatorname{sin}\left(2 \cdot \pi \cdot b\right)\right|$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The sine addition bound reduces the derivative to a second Gaussian moment. The inequality u exp of negative u at most two exp of negative one times exp of negative u over two bounds this moment by the zeroth moment at half the parameter. This yields the coefficient four exp of negative one divided by s.

**Theorem 1.9 (Integer Fourier frequencies).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{tsum}\left((n:\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(\pi \cdot s \cdot n^{2}\right)\right) \cdot \operatorname{cos}\left(2 \cdot \pi \cdot n \cdot b\right))\right) = \operatorname{thetaFourier}\left(s, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.real_fourier_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Split the absolutely convergent integer series into its zero term and its two nonzero half-lines. The positive and negative cosine terms agree, so the sum is exactly the positive-frequency theta expansion. At zero translation this identity is the shared bridge between the real integer Gaussian sum and theta.

**Theorem 1.10 (Translated Gaussian representation).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{thetaFourier}\left(s, b\right) = \frac{1}{\operatorname{sqrt}\left(s\right)} \cdot \operatorname{tsum}\left((n:\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(\frac{\pi}{s} \cdot \left(b - n\right)^{2}\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_poisson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Apply the Gaussian Poisson identity with coefficient pi s and angle two pi b. Taking real parts gives the cosine Fourier sum. Its zero frequency is one, and pairing the positive and negative frequencies gives twice the positive cosine sum. The coefficient reduces to the reciprocal positive square root of s. The transformed Gaussian is centered at b.

**Theorem 1.11 (Reciprocal parameter at zero).**

$$\forall s \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{thetaFourier}\left(s, 0\right) = \frac{1}{\operatorname{sqrt}\left(s\right)} \cdot \operatorname{thetaFourier}\left(\frac{1}{s}, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_zero_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

At zero translation the cosine factors are one. Replacing s by its reciprocal in the integer Fourier sum identifies the Gaussian series from the Poisson formula. Positivity of s fixes the square root.

**Theorem 1.12 (Translated Gaussian derivative).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < a \Rightarrow \operatorname{HasDerivAt}\left((z:\mathbb{R} \mapsto \operatorname{tsum}\left((n:\mathbb{Z} \mapsto \operatorname{exp}\left(-\left(a \cdot \left(z - n\right)^{2}\right)\right))\right)), \operatorname{tsum}\left((n:\mathbb{Z} \mapsto -\left(2 \cdot a\right) \cdot \left(b - n\right) \cdot \operatorname{exp}\left(-\left(a \cdot \left(b - n\right)^{2}\right)\right))\right), b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.hasDerivAt_gaussianTranslate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Near a fixed translation b, choose M equal to the absolute value of b plus one. The quadratic inequality for the translated square bounds each Gaussian by exp of negative a times n squared plus two a M times the absolute value of n. The derivative contributes at most two a times the sum of the absolute value of n and M. The zeroth and first Gaussian moments are summable, so this uniform bound justifies differentiation of the integer series.

**Theorem 1.13 (Signed Gaussian force).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right) = -\frac{2 \cdot \pi}{s \cdot \operatorname{sqrt}\left(s\right)} \cdot \operatorname{tsum}\left((n:\mathbb{Z} \mapsto \left(b - n\right) \cdot \operatorname{exp}\left(-\left(\frac{\pi}{s} \cdot \left(b - n\right)^{2}\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Differentiate the translated Gaussian representation with a equal to pi divided by s. Factoring the constant from the differentiated series gives the negative factor two pi divided by s times the square root of s. Thus positive force gives a strictly negative derivative of the Fourier theta function.

**Theorem 1.14 (Uniform derivative bounds).**

$$\forall s \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < s \Rightarrow \left(s \le \frac{\pi}{6} \Rightarrow \left(\left|\operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right)\right| \le \frac{6}{s \cdot \operatorname{sqrt}\left(s\right)} \cdot \left|\operatorname{sin}\left(2 \cdot \pi \cdot b\right)\right| \land \left(0 \le b \Rightarrow \left(b \le \frac{1}{2} \Rightarrow \frac{3}{10 \cdot s \cdot \operatorname{sqrt}\left(s\right)} \cdot \operatorname{exp}\left(-\frac{\pi}{4 \cdot s}\right) \cdot \operatorname{sin}\left(2 \cdot \pi \cdot b\right) \le -\operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{thetaFourier}\left(s, z\right)), b\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_small_derivative_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The sine addition inequality and a Gaussian second-moment estimate bound the derivative in absolute value using the uniform sine control and the zero-translation theta value at s over two, times the absolute value of sin of two pi b. Reciprocal-parameter duality bounds that zero-translation value by three over the square root of s, giving the upper constant six. For the lower bound, Poisson summation expresses the derivative as negative two pi divided by the product of s and its square root, multiplied by the Gaussian force with a equal to pi over s. The condition s at most pi over six implies a at least six. Gaussian pairing then gives the coefficient three tenths in the lower bound on the closed half-period. The upper bound holds for every real translation.

## References

- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.cos_summable`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.gaussian_moment`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.hasDerivAt_gaussianTranslate`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.hasDerivAt_thetaFourier`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.real_fourier_int`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_bounds`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_control`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_derivative_gaussian`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_poisson`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_small_derivative_bounds`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_zero_duality`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaSine`
- Truth anchor: `D5/S3/Fourier/ThetaDerivativeBounds.thetaSine_first_mode`
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeWindow](../Analytic/Polynomial/DiagonalPadeWindow.md)
- Dependency: [D5/S3/Fourier/ThetaGaussianPairing](ThetaGaussianPairing.md)
