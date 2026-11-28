# Hexagonal stationarity and vertical contributions

## Abstract

Threefold integer symmetry forces stationarity at the hexagonal height. Four retained directions control the positive square contribution, while the second-coordinate Gaussian moment is strictly positive.

**Definition 1.1 (Integer hexagonal rotation).**

$$\forall v \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; \operatorname{hexTurn}\left(v\right) = \operatorname{pair}\left(\operatorname{snd}\left(v\right), -\operatorname{fst}\left(v\right) - \operatorname{snd}\left(v\right)\right)$$

*Formalization.* `D5/S3/Fourier/ThetaVerticalPositive.hexTurn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The bijection sends (m,n) to (n,−m−n), and its inverse sends (m,n) to (−m−n,m). It has order three.

**Theorem 1.2 (Preservation of the hexagonal form).**

$$\forall v \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, \operatorname{hexTurn}\left(v\right)\right) = \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaVerticalPositive.hex_q_turn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Multiplying Q at the hexagonal point by square root three over two gives m squared plus mn plus n squared. Substituting the integer rotation preserves this polynomial, and hence the original form.

**Theorem 1.3 (Vanishing height derivative).**

$$\forall t \in \mathbb{R},\; 0 < t \Rightarrow \operatorname{deriv}\left((y:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, y\right)), \frac{\operatorname{sqrt}\left(3\right)}{2}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaVerticalPositive.hexagonal_height_stationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Put c equal to the square root of three divided by two. The integer map sending (m,n) to (n,−m−n) is a bijection of order three and preserves the form (m squared plus mn plus n squared) divided by c. The three height derivatives of the quadratic form along each orbit sum to zero. Their Gaussian factors are equal, so the three differentiated Gaussian terms also sum to zero. The height derivative terms are absolutely summable: the absolute value of the height derivative of Q is at most Q divided by y, and the exponential absorbs this linear weight at temperature t divided by two. Reindexing the three sums therefore gives three times the height derivative equal to zero. This proves stationarity for every positive temperature.

**Definition 1.4 (Negative height contribution).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{verticalNegative}\left(t, y\right) = \frac{2 \cdot \pi \cdot t}{y} \cdot \operatorname{tsum}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{snd}\left(v\right)^{2} \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, y, v\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaVerticalPositive.verticalNegative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The weighted Gaussian sum records the square of the second integer coordinate. Its coefficient is twice pi times the temperature divided by the height.

**Theorem 1.5 (Weighted convergence).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{Summable}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{snd}\left(v\right)^{2} \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, y, v\right)\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaVerticalPositive.weighted_gaussian_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The square of the second coordinate is at most the quadratic form divided by y. For c equal to pi t over two, the inequality u exp of negative u at most one bounds the weighted Gaussian by one over c y times the unweighted series at half the temperature. Gaussian convergence proves the comparison series summable for every positive temperature and height.

**Definition 1.6 (Positive square contribution).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{verticalPositive}\left(t, y\right) = \left(\pi \cdot t\right)^{2} \cdot \operatorname{tsum}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \left(\operatorname{snd}\left(v\right)^{2} - \frac{\left(\operatorname{fst}\left(v\right) + \operatorname{snd}\left(v\right) \cdot \frac{1}{2}\right)^{2}}{y^{2}}\right)^{2} \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, y, v\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Fourier/ThetaVerticalPositive.verticalPositive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Each term is a squared height derivative of the quadratic form times its positive Gaussian weight. Multiplication by pi t squared is the positive part of the second derivative expression.

**Definition 1.7 (Shortest-direction Gaussian scale).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{verticalScale}\left(t, y\right) = 2 \cdot \pi \cdot t \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \left(y + \frac{1}{4 \cdot y}\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/ThetaVerticalPositive.verticalScale` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The scale uses the Gaussian length y plus one over four y and the positive factor two pi t.

**Theorem 1.8 (Four-direction lower bound).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; \frac{4}{\operatorname{sqrt}\left(3\right)} \le \pi \cdot t \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \operatorname{verticalScale}\left(t, y\right) \cdot \frac{20 \cdot \pi \cdot t}{9} \le \operatorname{verticalPositive}\left(t, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaVerticalPositive.verticalPositive_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Retain precisely (1,0), (−1,0), (0,1), and (0,−1). All other square summands are nonnegative. The retained contribution divided by the Gaussian scale is P one plus P two, where P one is pi t divided by y to the fourth times exp of pi t times y minus three over four y. Its derivative has the sign of pi t times the sum of y squared and three quarters, minus four y. When pi t is at least four divided by square root three, completing the square makes this derivative nonnegative above the hexagonal height. Thus P one increases and is at least sixteen pi t over nine. The condition y squared at least three quarters gives P two at least four pi t over nine. Their sum gives the stated twenty pi t over nine lower bound. Summability follows from the quadratic Taylor bound for exp: the square weight is absorbed by the Gaussian at temperature t over two.

**Theorem 1.9 (Vertical differential identity).**

$$\forall t \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \operatorname{deriv}\left((b:\mathbb{R} \mapsto \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, z\right)), b\right)), y\right) + \frac{2}{y} \cdot \operatorname{deriv}\left((z:\mathbb{R} \mapsto \operatorname{F}\left(t, \frac{1}{2}, z\right)), y\right) = \operatorname{verticalPositive}\left(t, y\right) - \operatorname{verticalNegative}\left(t, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ThetaVerticalPositive.vertical_differential_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The second Gaussian height derivative contains the square of the first quadratic derivative and a term involving the second quadratic derivative. Adding twice the first theta derivative divided by y cancels the contribution of the shifted first coordinate. The remaining negative contribution is twice pi t divided by y times the second-coordinate Gaussian moment. Absolute convergence of the square terms, first derivative terms and second-coordinate moments permits the sums to be combined.

## References

- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.hexTurn`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.hex_q_turn`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.hexagonal_height_stationary`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.verticalNegative`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.verticalPositive`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.verticalPositive_lower`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.verticalScale`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.vertical_differential_identity`
- Truth anchor: `D5/S3/Fourier/ThetaVerticalPositive.weighted_gaussian_summable`
- Dependency: [D5/S3/Fourier/PlanarThetaFoundation](PlanarThetaFoundation.md)
