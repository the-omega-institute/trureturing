# Epstein zeta through the theta Mellin integral

## Abstract

For real s greater than one the Epstein series is the Gamma-normalized Mellin integral of theta minus one. Hexagonal lattices uniquely minimize it at every positive covolume, with the normalized orthogonal-image equality classification.

**Definition 1.1 (Planar Epstein zeta series).**

$$\forall s \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{epstein}\left(s, x, y\right) = \operatorname{tsum}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{Q}\left(x, y, v\right)^{-s})\right)$$

*Formalization.* `D5/S3/Fourier/EpsteinMellinMinimum.epstein` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

The series uses the positive unit-area binary quadratic form. For s greater than one its zero-vector summand is zero. Outside the summability range the totalized sum is not an analytic continuation.

**Theorem 1.2 (Temperature continuity).**

$$\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 < y \Rightarrow \operatorname{ContinuousOn}\left((t:\mathbb{R} \mapsto \operatorname{F}\left(t, x, y\right)), \operatorname{Ioi}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.continuousOn_temperature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

Near any positive temperature t, all summands are bounded by the Gaussian at temperature t divided by two. This summable bound makes the sum continuous.

**Theorem 1.3 (Absolute convergence).**

$$\forall s \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 < s \Rightarrow \left(0 < y \Rightarrow \operatorname{Summable}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{Q}\left(x, y, v\right)^{-s})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.epstein_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

The maximum norm of the integer coordinate vector squared is bounded by the sum of the coordinate squares. Gaussian quadratic control bounds this sum by a fixed positive constant times the form. Taking negative real powers bounds each nonzero Epstein term by that constant to the power s times the maximum norm to the power negative two s. The latter series is summable for two s greater than two.

**Theorem 1.4 (Integrability of the Mellin weight).**

$$\forall s \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 < s \Rightarrow \left(0 < y \Rightarrow \operatorname{IntegrableOn}\left((t:\mathbb{R} \mapsto \left(\operatorname{F}\left(t, x, y\right) - 1\right) \cdot t^{s - 1}), \operatorname{Ioi}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.epstein_mellin_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

For each nonzero integer pair, the Gamma integral evaluates the integral of its Gaussian times t to the power s minus one. The resulting positive values are pi to negative s times Gamma of s times the Epstein terms. Their sum is finite. The integral of the sum of absolute values is finite by Tonelli, and bounds the absolute value of the summed function. Continuity at every positive t supplies measurability.

**Theorem 1.5 (Mellin representation).**

$$\forall s \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 < s \Rightarrow \left(0 < y \Rightarrow \operatorname{epstein}\left(s, x, y\right) = \frac{\pi^{s}}{\operatorname{Gamma}\left(s\right)} \cdot \operatorname{integral}\left(\operatorname{Ioi}\left(0\right), (t:\mathbb{R} \mapsto \left(\operatorname{F}\left(t, x, y\right) - 1\right) \cdot t^{s - 1})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.epstein_mellin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

The zero vector contributes exactly one to theta. Removing it and interchanging the remaining Gaussian sum with the integral is justified by the summable integral norms. The Gamma integral and its positivity give the displayed normalization.

**Theorem 1.6 (Unique reduced Epstein minimum).**

$$\forall s \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 1 < s \Rightarrow \left(0 \le x \Rightarrow \left(x \le \frac{1}{2} \Rightarrow \left(\frac{\operatorname{sqrt}\left(3\right)}{2} \le y \Rightarrow \left(\operatorname{epstein}\left(s, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \le \operatorname{epstein}\left(s, x, y\right) \land \left(\operatorname{epstein}\left(s, x, y\right) = \operatorname{epstein}\left(s, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \Leftrightarrow \left(x = \frac{1}{2} \land y = \frac{\operatorname{sqrt}\left(3\right)}{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.reduced_epstein_minimum` (`✓ std3`). ∎

*Citation.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Commentary.*

Multiply the theta comparison by the positive Mellin weight and integrate. If the reduced point differs from the hexagonal point, the theta gap is strictly positive at every positive temperature. The weighted gap therefore has support containing the whole positive half-line, so its integral is strictly positive. This proves the classical Epstein minimum and its equality classification.

**Definition 1.7 (Epstein zeta in actual basis coordinates).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall s \in \mathbb{R},\; \operatorname{basisEpstein}\left(s, a, b\right) = \operatorname{tsum}\left((v:\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right) \mapsto \operatorname{normSq}\left(\operatorname{fst}\left(v\right) \cdot a + \operatorname{snd}\left(v\right) \cdot b\right)^{-s})\right)$$

*Formalization.* `D5/S3/Fourier/EpsteinMellinMinimum.basisEpstein` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. L. Montgomery (1988). *Minimal theta functions*. DOI: [10.1017/S0017089500007047](https://doi.org/10.1017/S0017089500007047). URL: <https://doi.org/10.1017/S0017089500007047>.

*Acknowledgement.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Acknowledgement.* R. A. Rankin (1953). *A minimum problem for the Epstein zeta-function*. DOI: [10.1017/S2040618500035668](https://doi.org/10.1017/S2040618500035668). URL: <https://doi.org/10.1017/S2040618500035668>.

*Acknowledgement.* V. Ennola (1964). *A lemma about the Epstein zeta-function*. DOI: [10.1017/S2040618500035024](https://doi.org/10.1017/S2040618500035024). URL: <https://doi.org/10.1017/S2040618500035024>.

*Acknowledgement.* V. Ennola (1964). *On a problem about the Epstein zeta-function*. DOI: [10.1017/S0305004100038330](https://doi.org/10.1017/S0305004100038330). URL: <https://doi.org/10.1017/S0305004100038330>.

*Acknowledgement.* P. H. Diananda (1964). *Notes on two lemmas concerning the Epstein zeta-function*. DOI: [10.1017/S2040618500035036](https://doi.org/10.1017/S2040618500035036). URL: <https://doi.org/10.1017/S2040618500035036>.

*Commentary.*

The summands are the negative s-th powers of the squared lengths of all integer combinations of the two basis vectors.

**Theorem 1.8 (Epstein minimum and orthogonal rigidity).**

$$\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall s \in \mathbb{R},\; \forall A \in \mathbb{R},\; 0 < A \Rightarrow \left(\left|\operatorname{re}\left(a\right) \cdot \operatorname{im}\left(b\right) - \operatorname{im}\left(a\right) \cdot \operatorname{re}\left(b\right)\right| = A \Rightarrow \left(1 < s \Rightarrow \left(A^{-s} \cdot \operatorname{epstein}\left(s, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \le \operatorname{basisEpstein}\left(s, a, b\right) \land \left(\operatorname{basisEpstein}\left(s, a, b\right) = A^{-s} \cdot \operatorname{epstein}\left(s, \frac{1}{2}, \frac{\operatorname{sqrt}\left(3\right)}{2}\right) \Leftrightarrow \operatorname{IsHexagonalBasis}\left(\operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, a\right), \operatorname{smul}\left(\frac{1}{\operatorname{sqrt}\left(A\right)}, b\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/EpsteinMellinMinimum.basis_epstein_minimum_isometry` (`✓ std3`). ∎

*Citation.* J. W. S. Cassels (1959). *On a problem of Rankin about the Epstein zeta-function*. DOI: [10.1017/S2040618500033906](https://doi.org/10.1017/S2040618500033906). URL: <https://doi.org/10.1017/S2040618500033906>.

*Commentary.*

Normalize a basis of positive covolume A to unit area. Its Epstein series scales by A to the power negative s. The unit-area minimum yields the scaled comparison value and equality precisely when the normalized basis generates an orthogonal hexagonal image. Positive Mellin weights preserve the strict theta gap for every real s greater than one.

## References

- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.basisEpstein`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.basis_epstein_minimum_isometry`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.continuousOn_temperature`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.epstein`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.epstein_mellin`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.epstein_mellin_integrable`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.epstein_summable`
- Truth anchor: `D5/S3/Fourier/EpsteinMellinMinimum.reduced_epstein_minimum`
- Dependency: [D5/S3/Fourier/ThetaLatticeMinimum](ThetaLatticeMinimum.md)
