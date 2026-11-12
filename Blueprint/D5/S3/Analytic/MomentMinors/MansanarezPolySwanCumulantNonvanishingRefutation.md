# The universal cumulant-coefficient condition fails

## Abstract

A finite-support symmetric moment-determinate law refutes universal cumulant-coefficient nonvanishing.

**Definition 1.1 (All moments are integrable).**

$$\forall mu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; (\operatorname{AllMoments}\left(mu\right)) \Leftrightarrow (\forall n \in \mathbb{N},\; \operatorname{Integrable}\left((fun x: \mathbb{R} \mapsto x^{n}), mu\right))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.AllMoments` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

AllMoments μ states that every natural power of the identity function is integrable against μ.

**Definition 1.2 (Symmetric moment-determinate laws).**

$$\forall mu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; (\operatorname{SMD}\left(mu\right)) \Leftrightarrow ((\operatorname{Measure.map}\left((fun x: \mathbb{R} \mapsto -x), mu\right) = mu) \land ((\operatorname{AllMoments}\left(mu\right)) \land (\forall nu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; (\operatorname{IsProbabilityMeasure}\left(nu\right)) \Rightarrow ((\operatorname{AllMoments}\left(nu\right)) \Rightarrow ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{moment}\left(\operatorname{id}, n, mu\right) = \operatorname{moment}\left(\operatorname{id}, n, nu\right))) \Rightarrow (mu = nu))))))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.SMD` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

SMD μ states reflection invariance, integrability of every power, and uniqueness among probability measures with all moments and the same positive-order moments.

**Definition 1.3 (Characteristic-function cumulants).**

$$\forall mu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; \forall n \in \mathbb{N},\; \operatorname{cumulant}\left(mu, n\right) = \operatorname{Complex.re}\left(\left(-\operatorname{Complex.I}\right)^{n} \cdot \operatorname{iteratedDeriv}\left(n, (fun t: \mathbb{R} \mapsto \operatorname{Complex.log}\left(\operatorname{charFun}\left(mu, t\right)\right)), 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.cumulant` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

For a real measure μ and natural n, cumulant uses the nth iterated derivative at zero of the principal complex logarithm of the real characteristic function, multiplied by (-I)^n and projected to the real part.

**Definition 1.4 (The shifted polynomial derivative).**

$$\forall j \in \mathbb{N},\; \forall P \in \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right),\; \operatorname{shiftDerivative}\left(j, P\right) = \sum_{i\in \operatorname{MvPolynomial.vars}\left(P\right)} (\operatorname{MvPolynomial.X}\left(i + j\right) \cdot \operatorname{MvPolynomial.pderiv}\left(i, P\right))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.shiftDerivative` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

The operator sums X(i+j) times the partial derivative in i over the finite variable support of a multivariate polynomial.

**Definition 1.5 (The source L operator).**

$$\forall P \in \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right),\; \operatorname{sourceL}\left(P\right) = \operatorname{MvPolynomial.C}\left((\frac{1}{2}: \mathbb{R})\right) \cdot \left(\operatorname{shiftDerivative}\left(1, \operatorname{shiftDerivative}\left(1, P\right)\right) - \operatorname{shiftDerivative}\left(2, P\right)\right)$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceL` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

sourceL is one half of the difference between two successive unit shifts and the shift by two.

**Definition 1.6 (The source H operator).**

$$\forall P \in \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right),\; \operatorname{sourceH}\left(P\right) = \sum_{i\in \operatorname{MvPolynomial.vars}\left(P\right)} ((\operatorname{MvPolynomial.C}\left((-\frac{1}{2}: \mathbb{R})\right) \cdot \sum_{l\in \operatorname{Finset.Ico}\left(1, i\right)} (\operatorname{MvPolynomial.C}\left((\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(i, l\right)\right): \mathbb{R})\right) \cdot \operatorname{MvPolynomial.X}\left(1 + l\right) \cdot \operatorname{MvPolynomial.X}\left(1 + i - l\right))) \cdot \operatorname{MvPolynomial.pderiv}\left(i, P\right))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceH` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

sourceH is the finite sum of the binomial inner derivative expression from Definition 3.8.

**Definition 1.7 (The source A polynomial).**

$$\forall n \in \mathbb{N},\; \operatorname{sourceA}\left(n\right) = -\sum_{k\in \operatorname{Finset.Ico}\left(1, n\right)} (\operatorname{MvPolynomial.C}\left((\operatorname{Nat.cast}\left(\operatorname{Nat.choose}\left(n, k\right)\right): \mathbb{R})\right) \cdot \operatorname{MvPolynomial.X}\left(1 + k\right) \cdot \operatorname{MvPolynomial.X}\left(1 + n - k\right) \cdot \operatorname{MvPolynomial.X}\left(n\right))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceA` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

sourceA is the negative finite binomial sum in Lemma 3.4.

**Definition 1.8 (The recurrence-defined polynomial sequence).**

$$\forall R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; (\operatorname{IsSourceSequence}\left(R\right)) \Leftrightarrow ((R\left(2\right) = 0) \land ((R\left(3\right) = -\operatorname{MvPolynomial.C}\left((2: \mathbb{R})\right) \cdot \operatorname{MvPolynomial.X}\left(2\right)^{3}) \land (\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow (R\left(n + 1\right) = \operatorname{sourceA}\left(n\right) + \operatorname{sourceL}\left(R\left(n\right)\right) + \operatorname{sourceH}\left(R\left(n\right)\right)))))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.IsSourceSequence` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

The sequence starts with R₂ = 0 and R₃ = -2 X₂³ and satisfies the source recurrence for every n ≥ 3.

**Definition 1.9 (The linear monomial coefficient extractor).**

$$\forall n \in \mathbb{N},\; \forall P \in \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right),\; \operatorname{linearCoefficient}\left(n, P\right) = \sum_{d\in \operatorname{MvPolynomial.support}\left(P\right)} (\operatorname{let} c = \operatorname{AddMonoidAlgebra.coeff}\left(P\right)\left(d\right), \operatorname{if}\left(d\left(n\right) = 1, \operatorname{MvPolynomial.monomial}\left(\operatorname{Finsupp.erase}\left(n, d\right), c\right), 0\right))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.linearCoefficient` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

linearCoefficient keeps terms whose exponent at n is one and erases that exponent, summing over the polynomial support.

**Definition 1.10 (The source coefficient aₙ).**

$$\forall R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; \forall n \in \mathbb{N},\; \operatorname{coefficientForm}\left(R, n\right) = \operatorname{linearCoefficient}\left(n, R\left(n + 1\right)\right)$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.coefficientForm` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

coefficientForm applies linearCoefficient n to R at n+1.

**Definition 1.11 (The universal nonvanishing assertion).**

$$(\exists R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; \operatorname{IsSourceSequence}\left(R\right)) \land (\forall R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; (\operatorname{IsSourceSequence}\left(R\right)) \Rightarrow (\forall mu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; (\operatorname{IsProbabilityMeasure}\left(mu\right)) \Rightarrow ((\operatorname{SMD}\left(mu\right)) \Rightarrow (\forall m \in \mathbb{N},\; (3 \le m) \Rightarrow (\operatorname{MvPolynomial.eval}\left(\operatorname{cumulant}\left(mu\right), \operatorname{coefficientForm}\left(R, 2 \cdot m\right)\right) \ne 0)))))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.claim` (`✓ std3`).

*Citation.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

Remark 3.31 states: “Let X be a symmetric random variable determined by its moments. Then X verifies \eqref{Hypostar}.” The displayed Lean proposition additionally records the source recurrence sequence and quantifies the coefficient evaluation for every m ≥ 3. The source uses the local logarithmic characteristic-function cumulants and imposes no MGF, density or non-Gaussianity hypothesis.

**Theorem 1.12 (A finite-support counterexample).**

$$\neg ((\exists R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; \operatorname{IsSourceSequence}\left(R\right)) \land (\forall R \in (\mathbb{N} \to \operatorname{MvPolynomial}\left(\mathbb{N}, \mathbb{R}\right)),\; (\operatorname{IsSourceSequence}\left(R\right)) \Rightarrow (\forall mu \in \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right),\; (\operatorname{IsProbabilityMeasure}\left(mu\right)) \Rightarrow ((\operatorname{SMD}\left(mu\right)) \Rightarrow (\forall m \in \mathbb{N},\; (3 \le m) \Rightarrow (\operatorname{MvPolynomial.eval}\left(\operatorname{cumulant}\left(mu\right), \operatorname{coefficientForm}\left(R, 2 \cdot m\right)\right) \ne 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mps-cumulant-coefficient-nonvanishing` (refuted) by `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mps-cumulant-coefficient-nonvanishing","declaration_gid":"D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Mansanarez; Guillaume Poly; Yvik Swan (2024). *Derivatives of entropy and the MMSE conjecture*. DOI: [10.1109/TIT.2024.3466566](https://doi.org/10.1109/TIT.2024.3466566). URL: <https://arxiv.org/abs/2311.04831v2>.

*Commentary.*

For 0 < p < 1, the law with masses p/2, 1-p and p/2 at -1, 0 and 1 is a symmetric probability law with all moments and a direct three-point moment-determinacy argument. Its cumulants satisfy K₂ = p, K₄ = p - 3p², K₆ = p - 15p² + 30p³ and K₈ = p - 63p² + 420p³ - 630p⁴.

The quartic 56700p⁴ - 56700p³ + 18165p² - 1950p + 41 changes sign between 1/100 and 1/20. At its exact root, K₂, K₄ and K₆ are positive, K₈ is negative, and 21K₆² + 20K₄K₈ = 0. The source recurrence gives the evaluated coefficients a₆ = -140K₄², a₈ = -1008K₄K₆ and a₁₀ = -132(21K₆² + 20K₄K₈), so the m = 5 nonvanishing assertion fails while the earlier signs remain strict.

The source's Remark 1.5 prints -210 T₃T₆ for a₆; the defining recurrence gives -210 T₃T₅. Both mixed terms vanish for the symmetric witness, so the refutation uses the recurrence defined in Lemma 3.4.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.AllMoments`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.IsSourceSequence`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.SMD`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.claim`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.coefficientForm`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.cumulant`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.linearCoefficient`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.shiftDerivative`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceA`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceH`
- Truth anchor: `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.sourceL`
