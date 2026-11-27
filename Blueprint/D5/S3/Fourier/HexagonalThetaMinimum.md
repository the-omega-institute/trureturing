# Strict vertical monotonicity and the hexagonal minimum

## Abstract

The positive and negative vertical contributions give an explicit differential margin. Stationarity and strict shear and height comparisons identify the unique reduced theta minimum.

**Theorem 1.1 (Uniform first-row-scale bound).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 \le t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \operatorname{verticalNegative}\left(t, y\right) < \frac{91}{15} \cdot 2 \cdot \pi \cdot t \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \left(y + \frac{1}{4 \cdot y}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaMinimum.vertical_negative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Pairing the positive and negative second coordinates expresses the weighted sum through positive rows. In the first row, pairing the first coordinate m with negative m minus one bounds the centered half-translate by one plus the unshifted theta series. Every other shifted Gaussian row is bounded by the unshifted one because all Fourier coefficients are nonnegative. The remaining normalized row tail is bounded by the Gaussian tail at eight ninths of the height, hence by one fifteenth. The reciprocal-parameter identity bounds theta at t over y by the square root of y times theta at y. Since y exceeds five sixths, exp of negative pi y is less than one eighth, and a geometric sum gives theta at y less than four thirds. Using y and its square root both greater than four fifths gives the factor ninety-one fifteenths. The weighted series converges by comparison with the planar theta series at half the temperature. Its term with integer coordinates zero and one proves strict positivity.

**Theorem 1.2 (Positive differential margin).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 \le t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \operatorname{verticalScale}\left(t, y\right) \cdot \left(\frac{20 \cdot \pi \cdot t}{9} - \frac{91}{15}\right) < \operatorname{deriv}\left((b:\mathbb{R} \mapsto \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, z\right)), b\right)), y\right) + \frac{2}{y} \cdot \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, z\right)), y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaMinimum.hexagonal_vertical_differential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The positive square sum is at least the Gaussian scale times twenty pi t over nine. The negative sum is less than the scale times ninety-one over fifteen. For t at least one, pi t exceeds three. Their difference is greater than the scale times twenty pi t over nine minus ninety-one fifteenths; this margin is positive.

**Theorem 1.3 (Strict vertical derivative).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} < y \Rightarrow 0 < \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, z\right)), y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaMinimum.height_derivative_pos` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For t at least one, multiply the first height derivative by y squared. Its derivative is y squared times the positive differential expression, so the weighted first derivative strictly increases. At the hexagonal height it is zero by threefold symmetry. It is consequently positive at every larger height. For temperatures below one, reciprocal-temperature duality multiplies the derivative at reciprocal temperature by the positive factor one over t.

**Theorem 1.4 (Unique height minimum).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \left(\operatorname{F}\left(t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \le \operatorname{F}\left(t, \frac{1}{2}, y\right) \land \left(\operatorname{F}\left(t, \frac{1}{2}, y\right) = \operatorname{F}\left(t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \Leftrightarrow y = \frac{\operatorname{sqrt}\left(3\right)}{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaMinimum.hexagonal_height_minimum` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The theta function at shear one half is continuous on the closed height half-line and has positive derivative in its interior. It is strictly increasing, giving both the lower bound and the equality classification.

**Theorem 1.5 (Unique minimum on the reduced half-strip).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 \le x \Rightarrow \left(x \le \frac{1}{2} \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \left(\operatorname{F}\left(t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \le \operatorname{F}\left(t, x, y\right) \land \left(\operatorname{F}\left(t, x, y\right) = \operatorname{F}\left(t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \Leftrightarrow \left(x = \frac{1}{2} \land y = \frac{\operatorname{sqrt}\left(3\right)}{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaMinimum.reduced_theta_minimum` (`✓ std3`). ∎

*Citation.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

First decrease theta by increasing the shear to one half. Then decrease it by lowering the height to the square root of three divided by two. Equality in the combined comparison forces equality in both strictly monotone steps. The proof needs only the rectangular half-strip hypotheses; the circle condition from lattice reduction is unnecessary for this comparison. This is the reduced-coordinate conclusion of Montgomery's Theorem 1, a literature result with the proof reorganized here.

## References

- Truth anchor: `D5/S3/Fourier/HexagonalThetaMinimum.height_derivative_pos`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaMinimum.hexagonal_height_minimum`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaMinimum.hexagonal_vertical_differential_bound`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaMinimum.reduced_theta_minimum`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaMinimum.vertical_negative_bound`
- Dependency: [D5/S3/Fourier/ThetaShearMonotonicity](ThetaShearMonotonicity.md)
- Dependency: [D5/S3/Fourier/ThetaVerticalPositive](ThetaVerticalPositive.md)
