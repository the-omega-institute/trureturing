# Cat pairs need not be optimal for metrology with noisy measurements

## Abstract

Len, Gefen, Retzker and Kołodyński (arXiv:2109.01160, Nature Communications 13, 6971) conjecture that for every classical noise channel M_x = sum_i p(x|i) Pi_i applied independently to N probes, the pair of orthonormal states maximizing the noisy Fisher coefficient gamma can be taken of cat form cos(theta)|j>^N + sin(theta)|k>^N, -sin(theta)|j>^N + cos(theta)|k>^N. For a three-outcome qutrit detector with entries in (1/20)Z and two probes, the pair |10>, |21> attains a larger gamma than every cat pair.

**Definition 1.1 (The single-probe noisy measurement).**

$$\forall d : \mathbb{N}, \forall X : Type, [\operatorname{Fintype}\left(X\right)], \forall p : X \to \operatorname{Fin}\left(d\right) \to \mathbb{R}, \forall x : X, \operatorname{probeOp}\left(p, x\right) = \sum_{i \in \operatorname{Fin}\left(d\right)} p\left(x, i\right) \cdot \operatorname{single}\left(i, i, 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.probeOp` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

M_x = sum_i p(x|i) Pi_i, with Pi_i = |i><i| the matrix with a single 1 in position (i, i).

**Definition 1.2 (Independent measurement of N probes).**

$$\forall d : \mathbb{N}, \forall X : Type, [\operatorname{Fintype}\left(X\right)], \forall p : X \to \operatorname{Fin}\left(d\right) \to \mathbb{R}, \forall N : \mathbb{N}, \forall xs : \operatorname{Fin}\left(N\right) \to X, \forall s, t : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)), \operatorname{multiProbeOp}\left(p, xs\right)\left(s, t\right) = \prod_{l \in \operatorname{Fin}\left(N\right)} \operatorname{probeOp}\left(p, xs\left(l\right)\right)\left(s\left(l\right), t\left(l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.multiProbeOp` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

Eq. (AMxvec): M_x = M_{x_1} (x) ... (x) M_{x_N}, written entrywise on the product basis indexed by the words s : Fin N -> Fin d.

**Definition 1.3 (The noisy Fisher coefficient).**

$$\forall d : \mathbb{N}, \forall X : Type, [\operatorname{Fintype}\left(X\right)], \forall p : X \to \operatorname{Fin}\left(d\right) \to \mathbb{R}, \forall N : \mathbb{N}, \forall zeta, zetaperp, psi, psiperp : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \to \mathbb{C}, ((psi = \frac{zeta + zetaperp}{\sqrt{2}}) \land (psiperp = \frac{zeta - zetaperp}{\sqrt{2}})) \Rightarrow (\operatorname{gamma}\left(p, zeta, zetaperp\right) = \sum_{xs : \operatorname{Fin}\left(N\right) \to X} \operatorname{Re}\left(\frac{\frac{1}{4} \cdot (\langle psiperp, \operatorname{multiProbeOp}\left(p, xs\right) \cdot psi \rangle + \overline{\langle psiperp, \operatorname{multiProbeOp}\left(p, xs\right) \cdot psi \rangle})^{2}}{\langle psi, \operatorname{multiProbeOp}\left(p, xs\right) \cdot psi \rangle}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.gamma` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

Eq. (AgammaN): gamma = (1/4) sum over outcome words of [<psi_perp|V^dagger M_x V|psi> + c.c.]^2 / <psi|V^dagger M_x V|psi>, where V psi = (zeta + zeta_perp)/sqrt(2) and V psi_perp = (zeta - zeta_perp)/sqrt(2) invert the relations V (psi +- psi_perp)/sqrt(2) = zeta, zeta_perp of Eq. (AVPhichoice). Here <a, b> = sum_s conj(a(s)) b(s) and M psi is the matrix-vector product. The real part reads the source quotient, whose numerator and denominator are real.

**Definition 1.4 (Repeated basis words).**

$$\forall d, N : \mathbb{N}, \forall j : \operatorname{Fin}\left(d\right), \forall s : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)), \operatorname{basisPower}\left(j\right)\left(s\right) = \prod_{l \in \operatorname{Fin}\left(N\right)} \operatorname{PiSingle}\left(j, 1\right)\left(s\left(l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.basisPower` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

|j>^N is the product of N copies of the basis vector |j> of the common eigenbasis.

**Definition 1.5 (The cat state).**

$$\forall d, N : \mathbb{N}, \forall j, k : \operatorname{Fin}\left(d\right), \forall \theta : \mathbb{R}, \operatorname{catState}\left(j, k, \theta\right) = \operatorname{cos}\left(\theta\right) \cdot \operatorname{basisPower}\left(j\right) + \operatorname{sin}\left(\theta\right) \cdot \operatorname{basisPower}\left(k\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.catState` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

The first member of the conjectured optimal pair.

**Definition 1.6 (Its orthogonal partner).**

$$\forall d, N : \mathbb{N}, \forall j, k : \operatorname{Fin}\left(d\right), \forall \theta : \mathbb{R}, \operatorname{catPerp}\left(j, k, \theta\right) = -\operatorname{sin}\left(\theta\right) \cdot \operatorname{basisPower}\left(j\right) + \operatorname{cos}\left(\theta\right) \cdot \operatorname{basisPower}\left(k\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.catPerp` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

The second member of the conjectured optimal pair.

**Definition 1.7 (The conjectured optimality of cat pairs).**

$$(claim) \Leftrightarrow (\forall d : \mathbb{N}, (2 \le d) \Rightarrow (\forall X : Type, [\operatorname{Fintype}\left(X\right)], \forall p : X \to \operatorname{Fin}\left(d\right) \to \mathbb{R}, ((\forall x : X, \forall i : \operatorname{Fin}\left(d\right), 0 < p\left(x, i\right)) \land (\forall i : \operatorname{Fin}\left(d\right), \sum_{x \in X} p\left(x, i\right) = 1)) \Rightarrow (\forall N : \mathbb{N}, (1 \le N) \Rightarrow (\exists j, k : \operatorname{Fin}\left(d\right), (j \ne k) \land (\exists \theta : \mathbb{R}, \forall zeta, zetaperp : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \to \mathbb{C}, (((\langle zeta, zeta \rangle = 1) \land (\langle zetaperp, zetaperp \rangle = 1)) \land (\langle zetaperp, zeta \rangle = 0)) \Rightarrow (\operatorname{gamma}\left(p, zeta, zetaperp\right) \le \operatorname{gamma}\left(p, \operatorname{catState}\left(j, k, \theta\right), \operatorname{catPerp}\left(j, k, \theta\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.claim` (`✓ std3`).

*Citation.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

For every d >= 2, every finite outcome set X, every classical noise channel p with all entries positive, so that a maximizing pair exists, and every N >= 1 there are labels j != k and an angle theta whose cat pair attains the largest gamma among all orthonormal pairs. Orthonormality uses <a, b> = sum_s conj(a(s)) b(s). This is the weakest reading of the conjecture; it does not require j and k to be found from a single probe.

**Definition 1.8 (The detector).**

$$((detector\left(0\right) = (\frac{1}{20}, \frac{14}{20}, \frac{2}{20})) \land (detector\left(1\right) = (\frac{15}{20}, \frac{2}{20}, \frac{17}{20}))) \land (detector\left(2\right) = (\frac{4}{20}, \frac{4}{20}, \frac{1}{20}))$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.detector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

Row x lists p(x|0), p(x|1), p(x|2); every column sums to 1 and every entry is at least 1/20.

**Definition 1.9 (The first witness state).**

$$witness = |10\rangle$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

The basis word 10 of two qutrits.

**Definition 1.10 (The second witness state).**

$$witnessPerp = |21\rangle$$

*Formalization.* `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.witnessPerp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

The basis word 21 of two qutrits.

**Theorem 1.11 (A crossed pair beats every cat pair).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/len-2022-noisy-metrology-cat-optimality` (refuted) by `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"len-2022-noisy-metrology-cat-optimality","declaration_gid":"D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński (2022). *Quantum metrology with imperfect measurements*. DOI: [10.1038/s41467-022-33563-8](https://doi.org/10.1038/s41467-022-33563-8). URL: <https://arxiv.org/abs/2109.01160v2>.

*Commentary.*

Take d = 3, X = Fin 3, the detector above and N = 2. Write m_x(s) = p(x_1|s_1) p(x_2|s_2). For real orthonormal vectors supported on two words u != v the coefficient is gamma = sum_x t (1 - t) (m_x(u) - m_x(v))^2 / (t m_x(u) + (1 - t) m_x(v)), where t is the squared weight of u in (zeta + zeta_perp)/sqrt(2). The witness pair has u = 10, v = 21 and t = 1/2, and gamma = 6643859399/9075312000 > 73/100. Every cat pair with j != k has u = jj, v = kk and t = (cos(theta) - sin(theta))^2 / 2. Each summand is D - ab/D - (2t - 1)(a - b) with D = ta + (1 - t)b, and ab/D >= ab (2/D_0 - D/D_0^2) for D_0 = t_0 a + (1 - t_0) b, so gamma is bounded by an affine function of t. Evaluating it at t = 0 and t = 1 with t_0 = 2061/4000, 191/500, 1939/4000, 363/800, 309/500 or 437/800 for the six ordered pairs (j, k) gives gamma < 73/100. So no cat pair maximizes gamma.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.basisPower`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.catPerp`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.catState`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.detector`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.gamma`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.multiProbeOp`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.probeOp`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.witness`
- Truth anchor: `D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.witnessPerp`
