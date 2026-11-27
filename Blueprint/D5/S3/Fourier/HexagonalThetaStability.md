# Parametric hexagonal theta stability

## Abstract

The least three-point exponential gap over all admissible orbit angles gives an all-temperature lower bound for the hexagonal theta difference. A freely chosen positive anchor supplies a cubic certificate, and a negative orbit displacement supplies an exponential certificate.

**Definition 1.1 (Hyperbolic displacement).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{hexGap}\left(x, y\right) = \frac{\left(x - \frac{1}{2}\right)^{2} + \left(y - \frac{\operatorname{sqrt}\left(3\right)}{2}\right)^{2}}{\operatorname{sqrt}\left(3\right) \cdot y}$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.hexGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

For positive height, h is cosh of the hyperbolic distance from x plus iy to one half plus i times square root three over two, minus one.

**Definition 1.2 (Orbit amplitude).**

$$\forall h \in \mathbb{R},\; \operatorname{gapAmplitude}\left(h\right) = \operatorname{sqrt}\left(h \cdot \left(h + 2\right)\right)$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.gapAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The nonnegative amplitude is denoted by s. Its square equals h(h+2) when h(h+2) is nonnegative.

**Definition 1.3 (Three-point gap).**

$$\forall h \in \mathbb{R},\; \forall a \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall e \in \mathbb{R},\; \operatorname{threePointGap}\left(h, a, c, d, e\right) = \operatorname{exp}\left(-\left(a \cdot \left(h + \operatorname{gapAmplitude}\left(h\right) \cdot c\right)\right)\right) + \operatorname{exp}\left(-\left(a \cdot \left(h + \operatorname{gapAmplitude}\left(h\right) \cdot d\right)\right)\right) + \operatorname{exp}\left(-\left(a \cdot \left(h + \operatorname{gapAmplitude}\left(h\right) \cdot e\right)\right)\right) - 3$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.threePointGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The three exponents are the deformations of one hexagonal orbit.

**Definition 1.4 (Admissible coefficients).**

$$OrbitCoeff = \operatorname{setOf}\left((cde:\operatorname{Prod}\left(\mathbb{R}, \operatorname{Prod}\left(\mathbb{R}, \mathbb{R}\right)\right) \mapsto c + d + e = 0 \land c^{2} + d^{2} + e^{2} = \frac{3}{2})\right)$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.OrbitCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The first moment is zero and the second moment is three halves. In particular, each coefficient lies between minus one and one.

**Definition 1.5 (Uniform orbit bound).**

$$\forall h \in \mathbb{R},\; \forall a \in \mathbb{R},\; \operatorname{orbitGap}\left(h, a\right) = \operatorname{iInf}\left((cde:OrbitCoeff \mapsto \operatorname{threePointGap}\left(h, a, c, d, e\right))\right)$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.orbitGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The infimum over the admissible coefficients is the greatest lower bound uniform in the unknown orbit angle. The coefficient set contains (1,−1/2,−1/2), and every three-point gap is at least minus three.

**Definition 1.6 (Cubic anchor certificate).**

$$\forall h \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{cubicGap}\left(h, b\right) = -\left(3 \cdot b \cdot h\right) + \frac{b^{2}}{2} \cdot \left(3 \cdot h + \frac{9 \cdot h^{2}}{2}\right) - \frac{b^{3}}{6} \cdot \left(9 \cdot h^{2} + \frac{15 \cdot h^{3}}{2} + \frac{3}{4} \cdot \operatorname{gapAmplitude}\left(h\right)^{3}\right)$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.cubicGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The cubic Taylor polynomial of the exponential is a lower bound on the entire real line.

**Definition 1.7 (Exponential escape certificate).**

$$\forall h \in \mathbb{R},\; \forall a \in \mathbb{R},\; \operatorname{escapeGap}\left(h, a\right) = \operatorname{exp}\left(a \cdot \operatorname{max}\left(\frac{\operatorname{gapAmplitude}\left(h\right)}{2} - h, 0\right)\right) - 1 - a \cdot \operatorname{max}\left(\frac{\operatorname{gapAmplitude}\left(h\right)}{2} - h, 0\right) - 3 \cdot a \cdot h$$

*Formalization.* `D5/S3/Fourier/HexagonalThetaStability.escapeGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

At least one coefficient is at most minus one half. Its exponential remainder controls escape once s/2 exceeds h.

**Theorem 1.8 (Parametric lower certificates).**

$$\forall h \in \mathbb{R},\; \left(\forall b \in \mathbb{R},\; \forall a \in \mathbb{R},\; 0 < b \Rightarrow \left(b \le a \Rightarrow \frac{a}{b} \cdot \operatorname{cubicGap}\left(h, b\right) \le \operatorname{orbitGap}\left(h, a\right)\right)\right) \land \left(\forall a \in \mathbb{R},\; \operatorname{escapeGap}\left(h, a\right) \le \operatorname{orbitGap}\left(h, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaStability.orbitGap_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

The finite budget envelope, applied to probabilities (2+c)/6, (2+d)/6, (2+e)/6 and again after negating c,d,e, bounds the absolute third moment by three quarters. When h(h+2)≥0, the displacement moments are 3h, 3h+9h²/2, and at most 9h²+15h³/2+3s³/4. Taylor's inequality gives the cubic certificate at any positive b. Convexity of the three-exponential sum and its value three at zero extend it to every a at least b, with factor a/b. For the escape bound, exp(u)−1−u is nonnegative everywhere and increasing for u nonnegative. On the negative half-line the remainder is decreasing; the same least displacement therefore supplies the escape bound for every real a. For −2<h<0 the amplitude is zero, and both certificates still hold. In that interval the cubic certificate follows directly from the cubic Taylor bound and a nonpositive correction term.

**Theorem 1.9 (All-temperature orbit stability).**

$$\forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < t \Rightarrow \left(0 < y \Rightarrow \left(\operatorname{Summable}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{orbitGap}\left(\operatorname{hexGap}\left(x, y\right), \pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right)\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right)\right)\right))\right) \land \frac{1}{3} \cdot \operatorname{tsum}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{orbitGap}\left(\operatorname{hexGap}\left(x, y\right), \pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right)\right) \cdot \operatorname{exp}\left(-\left(\pi \cdot t \cdot \operatorname{Q}\left(\frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}, v\right)\right)\right))\right) \le \operatorname{F}\left(t, x, y\right) - \operatorname{F}\left(t, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/HexagonalThetaStability.hexagonal_theta_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Commentary.*

Put a_v=πtQ_hex(v) and h=hexGap(x,y). The order-three rotation preserves Q_hex. Each nonzero orbit has lengths Q_hex(v)(1+h+s c_j), where the coefficients have zero first moment and second moment three halves; zero amplitude permits any admissible coefficients. Reindexing the three absolutely convergent theta sums gives the identity 3(F_z−F_hex)=Σ_v exp(−a_v) threePointGap(h,a_v,c_v). The zero vector contributes zero. Replacing each orbit gap by its infimum proves the inequality. Its series converges absolutely: the absolute summand is bounded by 3exp(−a_v)+3exp(−a_v(1+h−s)), with 1+h−s positive. At t=0 each theta summand is one, so the theta series diverges; t=0 is outside its convergence range. Lean's totalized sum there is only a conventional value. The following consequences have not been separately checked in Lean. Far from the hexagonal point the bound is not a positive modulus. For h≥2/3 one has s≤2h, and the admissible coefficients (1,−1/2,−1/2) give orbitGap(h,a)≤exp(−a(h+s))+2exp(−a(h−s/2))−3<0 for every a>0. Hence for every t>0 and every point with hexGap≥2/3, for example x=3/2, y=√3/2, the whole orbit series is strictly negative, and on that region the inequality alone does not recover the hexagonal minimum. For 0≤h≤1/25, choosing b=3 gives cubicGap(h,3)≥3h/2. At t≥1 each nonzero a_v is at least three, so F_z−F_hex≥(h/6)Σ_v a_v exp(−a_v)≥h αt exp(−αt), where α=2π/√3. Temperature duality gives the corresponding bound for t<1, with reciprocal temperature and factor 1/t. On the same h interval, m=max(s/2−h,0) satisfies m²≥h/4; exp(u)−1−u≥u²/2 for u≥0 gives the quadratic certificate h(a²/8−3a). The number 1/25 is an h cutoff for the cubic certificate; no optimality of this cutoff is asserted. A global lower bound linear in h cannot hold: for fixed positive temperature and y tending to infinity, F grows on the scale √y whereas h grows on the scale y. Montgomery's minimal-theta theorem gives qualitative hexagonal minimality. Local Hessian and local optimality precedents include L. Bétermin, arXiv:1611.07820, and T. Leblé, arXiv:2511.03353. M. Faulhuber and S. Steinerberger, arXiv:1903.06856, give local coercivity in the deep-hole direction. These precedents are not asserted to contain the parametric orbit bound stated here.

## References

- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.OrbitCoeff`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.cubicGap`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.escapeGap`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.gapAmplitude`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.hexGap`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.hexagonal_theta_stability`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.orbitGap`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.orbitGap_lower`
- Truth anchor: `D5/S3/Fourier/HexagonalThetaStability.threePointGap`
- Dependency: [D5/S3/Entropy/FiniteSpectralEnvelope](../Entropy/FiniteSpectralEnvelope.md)
- Dependency: [D5/S3/Fourier/ThetaVerticalPositive](ThetaVerticalPositive.md)
