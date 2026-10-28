# The explicit weighted Bessel kernel

## Abstract

A two-mode counterexample to weighted Bessel-kernel positivity.

**Definition 1.1 (Successive positive zeros).**

$$\begin{aligned}\operatorname{j}\left(0\right) = 0\\\operatorname{j}\left(1\right) = \operatorname{firstZero}\left(0\right)\\\forall (n: \mathbb{N}), \operatorname{j}\left(n + 2\right) = \operatorname{sInf}\left(\{x: \mathbb{R} | (0 < x) \land ((\operatorname{j}\left(n + 1\right) < x) \land (\operatorname{nbessel}\left(0, x\right) = 0))\}\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.j` (`✓ std3`).

*Citation.* Ryan L. Acosta Babb (2024). *A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero*. DOI: [10.48550/arXiv.2410.17681](https://doi.org/10.48550/arXiv.2410.17681). URL: <https://arxiv.org/abs/2410.17681v1>.

*Commentary.*

Lemma 2.2, p. 6: “Let jₘ denote the mth positive zero of J₀. Then”. The real function nbessel 0 is J₀. The sequence is indexed from one, with an unused value zero at index zero; the first zero is firstZero 0, and later entries are infima of the positive zeros strictly above the preceding entry. Only the first two entries are needed below; their infima are attained and lie in the rational intervals described below.

**Definition 1.2 (The printed partial sum).**

$$\forall (\alpha: \mathbb{R}), \forall (m: \mathbb{N}), \forall (x: \mathbb{R}), \operatorname{S}\left(\alpha, m, x\right) = \sum_{k \in \operatorname{Finset.Icc}\left(1, m\right)} (\operatorname{j}\left(m\right)^{\alpha} \cdot \operatorname{nbessel}\left(0, \operatorname{j}\left(k\right) \cdot x\right))$$

*Formalization.* `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.S` (`✓ std3`).

*Citation.* Ryan L. Acosta Babb (2024). *A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero*. DOI: [10.48550/arXiv.2410.17681](https://doi.org/10.48550/arXiv.2410.17681). URL: <https://arxiv.org/abs/2410.17681v1>.

*Commentary.*

Section 3, p. 7: “Let us write $S^{\alpha}_{m}(x) = \sum_{k=1}^{m} j_{m}^{\alpha} J_{0}(j_{k} x)$.” The factor is jₘ raised to alpha even inside the sum over k. Consequently this printed S does not give the printed Cesaro equality for the explicit weighted kernel; S is retained separately.

**Definition 1.3 (The explicit weighted kernel).**

$$\forall (\alpha: \mathbb{R}), \forall (M: \mathbb{N}), \forall (x: \mathbb{R}), \operatorname{K}\left(\alpha, M, x\right) = if (M = 0) then 1 else \sum_{m \in \operatorname{Finset.Icc}\left(1, M\right)} ((1 - \frac{(m: \mathbb{R})}{(M: \mathbb{R}) + 1}) \cdot \operatorname{j}\left(m\right)^{\alpha} \cdot \operatorname{nbessel}\left(0, \operatorname{j}\left(m\right) \cdot x\right))$$

*Formalization.* `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.K` (`✓ std3`).

*Citation.* Ryan L. Acosta Babb (2024). *A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero*. DOI: [10.48550/arXiv.2410.17681](https://doi.org/10.48550/arXiv.2410.17681). URL: <https://arxiv.org/abs/2410.17681v1>.

*Commentary.*

Section 3, p. 7, the explicit right-hand display is “$= \sum_{m=1}^{M} (1 - \frac{m}{M + 1}) j_{m}^{\alpha} J_{0}(j_{m} x)$.” The separate sentence is “We will also set $K^{\alpha}_{0}(x) \equiv 1$ when $M = 0$.” Here the sum ranges over positive natural indices, and both m and M are cast to real numbers in the weight. K uses this explicit formula, independently of the preceding printed S equality.

**Definition 1.4 (Conjecture 1).**

$$claim = (\forall (\alpha: \mathbb{R}), (0 \le \alpha) \Rightarrow ((\alpha \le \frac{1}{2}) \Rightarrow (\forall (M: \mathbb{N}), \forall (x: \mathbb{R}), (0 \le x) \Rightarrow ((x \le 1) \Rightarrow (0 \le \operatorname{K}\left(\alpha, M, x\right))))))$$

*Formalization.* `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.claim` (`✓ std3`).

*Citation.* Ryan L. Acosta Babb (2024). *A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero*. DOI: [10.48550/arXiv.2410.17681](https://doi.org/10.48550/arXiv.2410.17681). URL: <https://arxiv.org/abs/2410.17681v1>.

*Commentary.*

Conjecture 1, p. 10: “For all, $0 \leq \alpha \leq \frac{1}{2}$, $M \in \mathbb{N}$ and $x \in [0,1]$, $K^{\alpha}_{M}(x) \geq 0$.” The natural M includes zero; alpha and x are real numbers, and both intervals are closed. K is the explicit weighted formula on p. 7.

**Theorem 1.5 (Refutation at two modes).**

$$\neg (\forall (\alpha: \mathbb{R}), (0 \le \alpha) \Rightarrow ((\alpha \le \frac{1}{2}) \Rightarrow (\forall (M: \mathbb{N}), \forall (x: \mathbb{R}), (0 \le x) \Rightarrow ((x \le 1) \Rightarrow (0 \le \operatorname{K}\left(\alpha, M, x\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ab2410` (refuted) by `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ab2410","declaration_gid":"D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ryan L. Acosta Babb (2024). *A partial converse to the Riemann–Lebesgue lemma for Bessel–Fourier series of order zero*. DOI: [10.48550/arXiv.2410.17681](https://doi.org/10.48550/arXiv.2410.17681). URL: <https://arxiv.org/abs/2410.17681v1>.

*Commentary.*

At alpha=1/2, M=2 and x=999/1000 the weighted kernel is strictly negative. If a=j 1 and b=j 2, then 24048255/10000000 <= a <= 24048256/10000000 and 55200781/10000000 <= b <= 55200782/10000000. Alternating-series estimates give nbessel 0 (a*x) <= 1/800 and nbessel 0 (b*x) <= -187/100000; also sqrt(a) <= 1551/1000 and sqrt(b) >= 2349/1000. Thus the negative second mode outweighs twice the first mode. The first two zeros are isolated by derivative signs, the intermediate value theorem and a negative polynomial bound between the two intervals. This proves the single counterexample. A uniform rectangle of negative values, a sharp exponent threshold, positivity at other mode counts, and the source's downstream existence assertions are separate questions.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.K`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.S`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.claim`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.j`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.result`
- Dependency: [D5/S3/Analytic/BesselRatioLogConcavity/Result](../BesselRatioLogConcavity/Result.md)
- Dependency: [D5/S3/Analytic/BesselRedheffer/Series](Series.md)
