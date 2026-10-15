# Relative phases can change the Geiger–Kedem spin entropy

## Abstract

The spin-one entropy in equations (15)–(18) depends on a relative phase.

The spin-one state has three real amplitude magnitudes determined by thetaAlpha and thetaBeta, and two relative phases phaseX and phaseZ. The common global phase cancels from its squared complex modulus. All logarithms are natural.

**Definition 1.1 (The polarization-angle density).**

$$\forall (thetaAlpha: \mathbb{R}), (\forall (thetaBeta: \mathbb{R}), (\forall (phaseX: \mathbb{R}), (\forall (phaseZ: \mathbb{R}), (\forall (phi: \mathbb{R}), ((\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.density}\left(thetaAlpha, thetaBeta, phaseX, phaseZ, phi\right): \mathbb{R}) = \frac{\operatorname{Complex.normSq}\left((((\operatorname{Complex.ofReal}\left((\operatorname{Real.sin}\left(thetaAlpha\right)) \cdot (\operatorname{Real.cos}\left(thetaBeta\right))\right)) \cdot (\operatorname{Complex.exp}\left((\operatorname{Complex.ofReal}\left((phaseX) + ((2) \cdot (phi))\right)) \cdot (\operatorname{Complex.I})\right))) + ((\operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(thetaAlpha\right)\right)) \cdot (\operatorname{Complex.exp}\left((\operatorname{Complex.ofReal}\left(phi\right)) \cdot (\operatorname{Complex.I})\right)))) + ((\operatorname{Complex.ofReal}\left((\operatorname{Real.sin}\left(thetaAlpha\right)) \cdot (\operatorname{Real.sin}\left(thetaBeta\right))\right)) \cdot (\operatorname{Complex.exp}\left((\operatorname{Complex.ofReal}\left((phaseZ) - ((2) \cdot (phi))\right)) \cdot (\operatorname{Complex.I})\right)))\right)}{(2) \cdot (\operatorname{Real.pi})})))))$$

*Formalization.* `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.density` (`✓ std3`).

*Citation.* Davi Geiger; Zvi M. Kedem (2022). *Spin Entropy*. DOI: [10.3390/e24091292](https://doi.org/10.3390/e24091292). URL: <https://arxiv.org/abs/2111.11605v3>.

*Commentary.*

Proposition 2 takes Complex.normSq of the sum of the three amplitudes, with frequencies +2, +1 and -2, and divides by twice Real.pi. Complex.ofReal displays each real-to-complex cast explicitly. The two outer amplitudes are the products of Real.sin thetaAlpha with Real.cos thetaBeta and Real.sin thetaBeta, respectively.

**Definition 1.2 (The spin-one entropy).**

$$\forall (thetaAlpha: \mathbb{R}), (\forall (thetaBeta: \mathbb{R}), (\forall (phaseX: \mathbb{R}), (\forall (phaseZ: \mathbb{R}), ((\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.spinEntropy}\left(thetaAlpha, thetaBeta, phaseX, phaseZ\right): \mathbb{R}) = ((-(\operatorname{intervalIntegral}\left(\lambda (phi: \mathbb{R}) \mapsto ((\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.density}\left(thetaAlpha, thetaBeta, phaseX, phaseZ, phi\right)) \cdot (\operatorname{Real.log}\left(\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.density}\left(thetaAlpha, thetaBeta, phaseX, phaseZ, phi\right)\right))), (0: \mathbb{R}), (2) \cdot (\operatorname{Real.pi}), \operatorname{MeasureTheory.volume}\right))) + (\operatorname{Real.binEntropy}\left((\operatorname{Real.cos}\left(thetaAlpha\right))^{2}\right))) + (((\operatorname{Real.sin}\left(thetaAlpha\right))^{2}) \cdot (\operatorname{Real.binEntropy}\left((\operatorname{Real.cos}\left(thetaBeta\right))^{2}\right)))))))$$

*Formalization.* `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.spinEntropy` (`✓ std3`).

*Citation.* Davi Geiger; Zvi M. Kedem (2022). *Spin Entropy*. DOI: [10.3390/e24091292](https://doi.org/10.3390/e24091292). URL: <https://arxiv.org/abs/2111.11605v3>.

*Commentary.*

Equation (17) adds the differential entropy of the density to the Shannon entropy of the three spin-component probabilities. The intervalIntegral is taken from zero to twice Real.pi with respect to MeasureTheory.volume. The density times its real logarithm is continuous, including at density zero. The qualified Mathlib function Real.binEntropy is defined by p log p⁻¹ + (1 − p) log (1 − p)⁻¹ for every real p.

**Definition 1.3 (The phase-independence assertion).**

$$(\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.claim}) \Leftrightarrow (\forall (thetaAlpha: \mathbb{R}), (\forall (thetaBeta: \mathbb{R}), (\forall (phaseX: \mathbb{R}), (\forall (phaseZ: \mathbb{R}), ((thetaAlpha \in \operatorname{Set.Icc}\left((0: \mathbb{R}), \frac{\operatorname{Real.pi}}{2}\right)) \Rightarrow ((thetaBeta \in \operatorname{Set.Icc}\left((0: \mathbb{R}), \frac{\operatorname{Real.pi}}{2}\right)) \Rightarrow ((phaseX \in \operatorname{Set.Ico}\left((0: \mathbb{R}), (2) \cdot (\operatorname{Real.pi})\right)) \Rightarrow ((phaseZ \in \operatorname{Set.Ico}\left((0: \mathbb{R}), (2) \cdot (\operatorname{Real.pi})\right)) \Rightarrow (\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.spinEntropy}\left(thetaAlpha, thetaBeta, phaseX, phaseZ\right) = \operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.spinEntropy}\left(thetaAlpha, thetaBeta, 0, 0\right))))))))))$$

*Formalization.* `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim` (`✓ std3`).

*Citation.* Davi Geiger; Zvi M. Kedem (2022). *Spin Entropy*. DOI: [10.3390/e24091292](https://doi.org/10.3390/e24091292). URL: <https://arxiv.org/abs/2111.11605v3>.

*Commentary.*

Conjecture 1 asserts that equation (17) equals the zero-phase expression (18). Both angles range over Set.Icc zero (Real.pi divided by two), and both relative phases range over Set.Ico zero (twice Real.pi). Equality with the zero-phase value is asserted for every such choice. The Shannon terms in spinEntropy use the qualified Mathlib function Real.binEntropy.

**Theorem 1.4 (A relative phase produces an entropy gap).**

$$\neg (\operatorname{D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/geiger-kedem-2022-spin-one-entropy-phase-independence-refutation` (refuted) by `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"geiger-kedem-2022-spin-one-entropy-phase-independence-refutation","declaration_gid":"D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Davi Geiger; Zvi M. Kedem (2022). *Spin Entropy*. DOI: [10.3390/e24091292](https://doi.org/10.3390/e24091292). URL: <https://arxiv.org/abs/2111.11605v3>.

*Commentary.*

Choose thetaAlpha = Real.arctan (Real.sqrt 10) and thetaBeta = Real.arctan (1/3). These angles lie in the required interval and give the three amplitudes (3, 1, 1)/Real.sqrt 11. Set phaseX = 0 and compare phaseZ = 0 with phaseZ = Real.pi.

For s equal to 1 or -1, the polynomial 3 + z + s z^4 has real part at least one on the closed unit disc. Its product with its principal complex logarithm has value 3 Real.log 3, first derivative Real.log 3 + 1, and fourth derivative 24 s (Real.log 3 + 1) + 2/27 at zero. Cauchy's coefficient formula at orders zero, one and four gives the circle mean of the polynomial's squared modulus as 11, and the circle mean of that squared modulus times the real logarithm of that squared modulus as 22 Real.log 3 + 4 + s/162.

After division of the polynomial's squared modulus by 22 Real.pi, the integral of the density times its logarithm is 2 Real.log 3 + 4/11 + s/1782 - Real.log (22 Real.pi). The Shannon terms agree for the two phases, so the entropy at phaseZ = Real.pi minus the entropy at phaseZ = 0 is 1/891. This nonzero difference contradicts the universal phase-independence assertion.

## References

- Truth anchor: `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim`
- Truth anchor: `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.density`
- Truth anchor: `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result`
- Truth anchor: `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.spinEntropy`
