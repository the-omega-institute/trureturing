# Gaussian tails and translated pairing

## Abstract

Explicit Gaussian tails control the higher modes and pairing errors. Cancellation between paired translated terms yields a positive sine-shaped force lower bound.

**Definition 1.1 (Normalized tail).**

$$\forall v \in \mathbb{R},\; \operatorname{gaussianTail}\left(v\right) = \operatorname{tsum}\left((k:\mathbb{N} \mapsto \left(k + 2\right)^{2} \cdot \operatorname{exp}\left(-\left(\pi \cdot v \cdot \left(\left(k + 2\right)^{2} - 1\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaGaussianPairing.gaussianTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The index k enumerates the positive modes n equal to k plus two. Subtracting one in the exponent normalizes by the first Gaussian mode.

**Theorem 1.2 (Uniform geometric bound).**

$$\forall v \in \mathbb{R},\; \frac{1}{2} \le v \Rightarrow \left(\operatorname{Summable}\left((k:\mathbb{N} \mapsto \left(k + 2\right)^{2} \cdot \operatorname{exp}\left(-\left(\pi \cdot v \cdot \left(\left(k + 2\right)^{2} - 1\right)\right)\right))\right) \land \left(\operatorname{gaussianTail}\left(v\right) \le \frac{4 \cdot \operatorname{exp}\left(-\left(3 \cdot \pi \cdot v\right)\right)}{1 - 4 \cdot \operatorname{exp}\left(-\left(3 \cdot \pi \cdot v\right)\right)} \land \operatorname{gaussianTail}\left(v\right) < \frac{1}{15}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaGaussianPairing.gaussian_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For n at least two, n squared is at most four to the power n minus one, and n squared minus one is at least three times n minus one. Thus the summands are bounded by successive positive powers of r equal to four exp of negative three pi v. A finite Taylor bound gives exp of three halves greater than four. For v at least one half this implies r less than one sixteenth, and the geometric sum is less than one fifteenth.

**Theorem 1.3 (Exponential margin).**

$$\forall s \in \mathbb{R},\; \forall v \in \mathbb{R},\; 0 < s \Rightarrow \left(s \le \frac{\pi}{6} \Rightarrow \left(\frac{3}{4 \cdot s} \le v \Rightarrow \operatorname{exp}\left(\frac{\pi}{4 \cdot s}\right) \cdot \operatorname{gaussianTail}\left(v\right) < \frac{1}{39999}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaGaussianPairing.gaussian_tail_scaled_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

If s lies in the interval zero to pi over six and v is at least three divided by four s, the scaled exponent is at most negative twelve times n minus one. The identity three n squared minus four at least eight times n minus one gives this comparison. The geometric ratio four exp of negative twelve is less than one forty-thousandth, since the Taylor lower bound exp of three greater than twenty implies exp of twelve greater than one hundred sixty thousand. Summing gives the strict bound one over thirty-nine thousand nine hundred ninety-nine. The estimates are a derivation for the one-dimensional theta comparison underlying Montgomery's planar minimum.

**Definition 1.4 (Gaussian pairing error).**

$$\forall a \in \mathbb{R},\; \operatorname{gaussianPairTail}\left(a\right) = \operatorname{tsum}\left((k:\mathbb{N} \mapsto 4 \cdot a \cdot \left(k + \frac{3}{4}\right)^{2} \cdot \operatorname{exp}\left(-\left(a \cdot \left(\left(k + 1\right)^{2} - \frac{k + 1}{2}\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaGaussianPairing.gaussianPairTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For positive integers n, the normalized pairing error is four a times the sum of (n minus one quarter) squared times exp of negative a times n squared minus n over two.

**Theorem 1.5 (Pairing tail bound).**

$$\forall a \in \mathbb{R},\; 6 \le a \Rightarrow \left(\operatorname{Summable}\left((k:\mathbb{N} \mapsto 4 \cdot a \cdot \left(k + \frac{3}{4}\right)^{2} \cdot \operatorname{exp}\left(-\left(a \cdot \left(\left(k + 1\right)^{2} - \frac{k + 1}{2}\right)\right)\right))\right) \land \operatorname{gaussianPairTail}\left(a\right) \le \frac{27}{2} \cdot \operatorname{exp}\left(-3\right) + \frac{96 \cdot \operatorname{exp}\left(-18\right)}{1 - 4 \cdot \operatorname{exp}\left(-9\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaGaussianPairing.gaussian_pair_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The inequality one plus u at most exp u bounds a exp of negative a d by six exp of negative six d whenever a is at least six and d is at least one half. The n equal to one term is bounded by twenty-seven halves times exp of negative three. For n at least two the exponent is at most negative nine n; a geometric series bounds the remaining sum by ninety-six times exp of negative eighteen divided by one minus four times exp of negative nine. This explicit total is strictly less than seven tenths, and therefore less than three quarters.

**Definition 1.6 (Periodized Gaussian force).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{gaussianForce}\left(a, b\right) = \operatorname{tsum}\left((m:\mathbb{Z} \mapsto \left(b - m\right) \cdot \operatorname{exp}\left(-\left(a \cdot \left(b - m\right)^{2}\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaGaussianPairing.gaussianForce` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The signed sum records the derivative of the periodized Gaussian apart from its positive normalization. All integer translates are retained.

**Theorem 1.7 (Absolute convergence).**

$$\forall a \in \mathbb{R},\; 0 < a \Rightarrow \left(\forall b \in \mathbb{R},\; \operatorname{Summable}\left((m:\mathbb{Z} \mapsto \left(b - m\right) \cdot \operatorname{exp}\left(-\left(a \cdot \left(b - m\right)^{2}\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaGaussianPairing.summable_gaussian_force` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The translated first Gaussian moment is the integer Hurwitz kernel moment of order one, with shift negative b and temperature a divided by pi. Its summability directly gives absolute convergence.

**Theorem 1.8 (Closed half-period bound).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 6 \le a \Rightarrow \left(0 \le b \Rightarrow \left(b \le \frac{1}{2} \Rightarrow \frac{3}{20 \cdot \pi} \cdot \operatorname{exp}\left(-\frac{a}{4}\right) \cdot \operatorname{sin}\left(2 \cdot \pi \cdot b\right) \le \operatorname{gaussianForce}\left(a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaGaussianPairing.gaussian_force_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For b at most one quarter, pair positive and negative integers. The negative derivative of u exp of negative a u squared decreases for u at least three quarters when a is at least six. The mean value theorem bounds each pair by the corresponding normalized Gaussian pairing-tail summand. The seven-tenths tail bound leaves at least three tenths of the central term. For b between one quarter and one half, pair around one half. All pairs beyond the first are nonnegative. With delta equal to one half minus b, the first pair is at least delta divided by two times exp of negative a over four. This follows from one minus exp of negative four delta at least two delta. Finally sin of two pi b is bounded by two pi times the distance to the nearest endpoint. The result holds for every a at least six and every b in the closed half-period.

## References

- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussianForce`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussianPairTail`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussianTail`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussian_force_lower`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussian_pair_tail_bound`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussian_tail_bound`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.gaussian_tail_scaled_bound`
- Truth anchor: `D5/S3/Fourier/ThetaGaussianPairing.summable_gaussian_force`
- Dependency: [D5/S3/Fourier/PlanarThetaFoundation](PlanarThetaFoundation.md)
