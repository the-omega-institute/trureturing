# Sample Covariance Spectral And Smooth

## Abstract

SampleCovarianceSpectralAndSmooth mathematical statements.

**Theorem 1.1 (gramHermitian).**

$$\forall (n : \mathbb{N}) (A : Matrix (Fin n) (Fin n) \mathbb{C}), (A * A^{H}). IsHermitian$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gramHermitian satisfies the displayed statement.

**Definition 1.2 (gramEigenvalue).**

$$\forall (n : \mathbb{N}) (A : Matrix (Fin n) (Fin n) \mathbb{C}) (i : Fin n), gramEigenvalue n A i = ((gramHermitian n A). eigenvalues i)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramEigenvalue` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.3 (empiricalSpectralMeasure).**

$$\forall (n : \mathbb{N}) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) \mathbb{C}), empiricalSpectralMeasure n hn A = ((n : \operatorname{ENNReal})^{-1} \cdot \sum i : Fin n, Measure. dirac (gramEigenvalue n A i / n))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.empiricalSpectralMeasure` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.4 (EntryLaw).**

$$\forall (\mu : Measure \mathbb{C}), EntryLaw \mu \iff (\mu Set. univ = 1 \land Integrable (fun z : \mathbb{C} \mapsto z) \mu \land Integrable (fun z : \mathbb{C} \mapsto \Vert z\Vert^{2}) \mu \land (\int z : \mathbb{C}, z \operatorname{d} \mu) = 0 \land (\int z : \mathbb{C}, \Vert z\Vert^{2} \operatorname{d} \mu) = 1)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.EntryLaw` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.5 (matrixLaw).**

$$\forall (n : \mathbb{N}) (\mu : Measure \mathbb{C}), matrixLaw n \mu = (Measure. map (fun f : Fin n \times Fin n \to \mathbb{C} \mapsto fun i j \mapsto f (i, j)) (Measure. pi (Function. const (Fin n \times Fin n) \mu)))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.matrixLaw` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.6 (meanSpectralMeasure).**

$$\forall (n : \mathbb{N}) (hn : 0 < n) (\mu : Measure \mathbb{C}), meanSpectralMeasure n hn \mu = ((matrixLaw n \mu). bind (fun A \mapsto empiricalSpectralMeasure n hn A))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.meanSpectralMeasure` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.7 (logPositiveKernel).**

$$\forall (x y : \mathbb{R}), logPositiveKernel x y = (if x = y then \infty else ENNReal. ofReal (max (Real. log (1 / | x - y| )) 0))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logPositiveKernel` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.8 (logNegativeKernel).**

$$\forall (x y : \mathbb{R}), logNegativeKernel x y = (if x = y then 0 else ENNReal. ofReal (max (- Real. log (1 / | x - y| )) 0))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logNegativeKernel` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.9 (logarithmicEnergy).**

$$\forall (\mu : Measure \mathbb{R}), logarithmicEnergy \mu = ((\int^{-}  x, \int^{-}  y, logPositiveKernel x y \operatorname{d} \mu \operatorname{d} \mu : EReal) - (\int^{-}  x, \int^{-}  y, logNegativeKernel x y \operatorname{d} \mu \operatorname{d} \mu : EReal))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logarithmicEnergy` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.10 (firstMoment).**

$$\forall (\mu : Measure \mathbb{R}), firstMoment \mu = (ENNReal. toEReal (\int^{-}  x, ENNReal. ofReal (max x 0) \operatorname{d} \mu))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.firstMoment` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.11 (penalizedEnergy).**

$$\forall (\mu : Measure \mathbb{R}), penalizedEnergy \mu = (logarithmicEnergy \mu + firstMoment \mu)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.penalizedEnergy` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.12 (marchenkoPasturDensity).**

$$\forall (x : \mathbb{R}), marchenkoPasturDensity x = (if 0 < x then ENNReal. ofReal (Real. sqrt (max (4 - x) 0) / (2 * Real. pi * Real. sqrt x)) else 0)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.marchenkoPasturDensity` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Definition 1.13 (marchenkoPastur).**

$$marchenkoPastur = (Measure. withDensity (Measure. restrict MeasureTheory. volume (Set. Ici 0)) marchenkoPasturDensity)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.marchenkoPastur` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

For an n×n matrix A with entries in ℂ, we denote by λ₁(A),…,λₙ(A) its eigenvalues, which are the roots in ℂ of its characteristic polynomial z ↦ det(A−z Idₙ), viewed as a multiset of n elements. We denote the empirical spectral distribution by μA ≔ (1/n)∑ₖ₌₁ⁿδλₖ₍A₎. The logarithmic energy ℰ(μ) ≔ ∬ log(1/|x−y|) μ(dx)μ(dy). Finally, we consider the square Marchenko–Pastur law given by μMP ≔ √(4−x)₊/(2π√x) dx. Here ℰ⁽¹⁾(μ) ≔ ℰ(μ)+m₁(μ). The displayed expression uses real nonnegative Gram eigenvalues and dimension normalization.

**Lemma 1.14 (measurable_gramEigenvalue).**

$$\forall (n : \mathbb{N}) (i : Fin n), Measurable (fun A : Matrix (Fin n) (Fin n) \mathbb{C} \mapsto gramEigenvalue n A i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.measurable_gramEigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

measurable_gramEigenvalue satisfies the displayed statement.

**Lemma 1.15 (lintegral_meanSpectralMeasure).**

$$\forall (n : \mathbb{N}) (hn : 0 < n) (\mu : Measure \mathbb{C}) (f : \mathbb{R} \to \operatorname{ENNReal}), (Measurable f) \to (\int^{-}  x, f x \operatorname{d} meanSpectralMeasure n hn \mu) = (n : \operatorname{ENNReal})^{-1} * \int^{-}  A, \sum i : Fin n, f (gramEigenvalue n A i / n) \operatorname{d} matrixLaw n \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.lintegral_meanSpectralMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

lintegral_meanSpectralMeasure satisfies the displayed statement.

**Lemma 1.16 (two_copy_gram_det_nonzero_iff).**

$$\forall (n : \mathbb{N}) (A C : Matrix (Fin n) (Fin n) \mathbb{C}), Matrix. det (Matrix. kronecker ((A * A^{H})) ((1 : Matrix (Fin n) (Fin n) \mathbb{C}))- Matrix. kronecker ((1 : Matrix (Fin n) (Fin n) \mathbb{C})) ((C * C^{H}))) \neq 0 \iff \forall i j : Fin n, gramEigenvalue n A i \neq gramEigenvalue n C j$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.two_copy_gram_det_nonzero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

two_copy_gram_det_nonzero_iff satisfies the displayed statement.

**Lemma 1.17 (gramEigenvalue_nonneg).**

$$\forall (n : \mathbb{N}) (A : Matrix (Fin n) (Fin n) \mathbb{C}) (i : Fin n), 0 \leq gramEigenvalue n A i$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramEigenvalue_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gramEigenvalue_nonneg satisfies the displayed statement.

**Lemma 1.18 (logarithmicEnergy_mean_eq_log_det_of_moments).**

$$\forall (n : \mathbb{N}) (hn : 0 < n) (\mu : Measure \mathbb{C}) [ IsProbabilityMeasure \mu ], (\forall i : Fin n, Integrable (fun A \mapsto gramEigenvalue n A i) (matrixLaw n \mu)) \to (\forall^{ae}  AC : Matrix (Fin n) (Fin n) \mathbb{C} \times Matrix (Fin n) (Fin n) \mathbb{C} \operatorname{d} (matrixLaw n \mu). prod (matrixLaw n \mu), \forall i j, gramEigenvalue n AC. 1 i \neq gramEigenvalue n AC. 2 j) \to (Integrable (fun AC : Matrix (Fin n) (Fin n) \mathbb{C} \times Matrix (Fin n) (Fin n) \mathbb{C} \mapsto Real. log \Vert Matrix. det (Matrix. kronecker ((AC. 1 * AC. 1^{H})) ((1 : Matrix (Fin n) (Fin n) \mathbb{C}))- Matrix. kronecker ((1 : Matrix (Fin n) (Fin n) \mathbb{C})) ((AC. 2 * AC. 2^{H})))\Vert ) ((matrixLaw n \mu). prod (matrixLaw n \mu))) \to logarithmicEnergy (meanSpectralMeasure n hn \mu) = (Real. log n - \left((n : \mathbb{R})^{-1}\right)^{2} * \int AC : Matrix (Fin n) (Fin n) \mathbb{C} \times Matrix (Fin n) (Fin n) \mathbb{C}, Real. log \Vert Matrix. det (Matrix. kronecker ((AC. 1 * AC. 1^{H})) ((1 : Matrix (Fin n) (Fin n) \mathbb{C}))- Matrix. kronecker ((1 : Matrix (Fin n) (Fin n) \mathbb{C})) ((AC. 2 * AC. 2^{H})))\Vert \operatorname{d} (matrixLaw n \mu). prod (matrixLaw n \mu) : \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logarithmicEnergy_mean_eq_log_det_of_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

logarithmicEnergy_mean_eq_log_det_of_moments satisfies the displayed statement.

**Definition 1.19 (Smooth.complexGaussian).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}), Smooth. complexGaussian m v = (Measure. map (fun xy : \mathbb{R} \times \mathbb{R} \mapsto (xy. 1 : \mathbb{C}) + (xy. 2 : \mathbb{C}) * Complex. I) ((gaussianReal m v). prod (gaussianReal 0 v)))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.complexGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.complexGaussian is given by the displayed expression.

**Definition 1.20 (Smooth.complexGaussian_probability).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}), IsProbabilityMeasure (complexGaussian m v)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.complexGaussian_probability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.complexGaussian_probability satisfies the displayed statement.

**Definition 1.21 (Smooth.mixture).**

$$\forall (a b : \mathbb{R}) (v : \operatorname{NNReal}), Smooth. mixture a b v = ((255/ 256 : \operatorname{ENNReal}) \cdot complexGaussian a v + (1/ 256 : \operatorname{ENNReal}) \cdot complexGaussian b v)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.mixture` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.mixture is given by the displayed expression.

**Definition 1.22 (Smooth.noiseVariance).**

$$\forall (\varepsilon : \mathbb{R}), Smooth. noiseVariance \varepsilon = \langle \varepsilon^{2} / (2* (1+ \varepsilon^{2})), by positivity \rangle$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.noiseVariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.noiseVariance is given by the displayed expression.

**Definition 1.23 (Smooth.smoothLaw).**

$$\forall (\varepsilon : \mathbb{R}), Smooth. smoothLaw \varepsilon = (mixture (- 1 / (Real. sqrt 255 * Real. sqrt (1+ \varepsilon^{2}))) (Real. sqrt 255 / Real. sqrt (1+ \varepsilon^{2})) (noiseVariance \varepsilon))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.smoothLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.smoothLaw is given by the displayed expression.

**Lemma 1.24 (Smooth.smoothLaw_EntryLaw).**

$$\forall (\varepsilon : \mathbb{R}), D5. S3. Analytic. Probability. SampleCovarianceSpectralAndSmooth. EntryLaw (smoothLaw \varepsilon)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.smoothLaw_EntryLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Smooth.smoothLaw_EntryLaw satisfies the displayed statement.

**Lemma 1.25 (Gaussian.gaussian_mv_eval_integrable).**

$$\forall \{ n : \mathbb{N} \} (m : \mathbb{R}) (v : \operatorname{NNReal}) (p : MvPolynomial (Fin n) \mathbb{C}), Integrable (fun x \mapsto MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p) (Measure. pi (Function. const (Fin n) (gaussianReal m v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gaussian_mv_eval_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Gaussian.gaussian_mv_eval_integrable satisfies the displayed statement.

**Lemma 1.26 (Gaussian.gaussian_mv_log_coeff_lower).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) (n : \mathbb{N}) (p : MvPolynomial (Fin n) \mathbb{C}) (d : Fin n \to_{0} \mathbb{N}) (D : \mathbb{N}), v \neq 0 \to p. coeff d \neq 0 \to (\forall i, p. degreeOf i \leq D) \to (\forall^{ae}  x \operatorname{d} Measure. pi (Function. const (Fin n) (gaussianReal m v)), MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p \neq 0) \land Integrable (fun x \mapsto Real. log \Vert MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p\Vert ) (Measure. pi (Function. const (Fin n) (gaussianReal m v))) \land Real. log \Vert p. coeff d\Vert - (n : \mathbb{R})* D* (Real. log 2 + D5. S3. Analytic. Probability. GaussianPolynomialLog. rootLogCost m v) \leq \int x, Real. log \Vert MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p\Vert \operatorname{d} Measure. pi (Function. const (Fin n) (gaussianReal m v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gaussian_mv_log_coeff_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Gaussian.gaussian_mv_log_coeff_lower satisfies the displayed statement.

## References

- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.EntryLaw`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.complexGaussian`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.complexGaussian_probability`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.empiricalSpectralMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.firstMoment`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gaussian_mv_eval_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gaussian_mv_log_coeff_lower`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramEigenvalue`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramEigenvalue_nonneg`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.gramHermitian`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.lintegral_meanSpectralMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logNegativeKernel`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logPositiveKernel`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logarithmicEnergy`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.logarithmicEnergy_mean_eq_log_det_of_moments`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.marchenkoPastur`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.marchenkoPasturDensity`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.matrixLaw`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.meanSpectralMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.measurable_gramEigenvalue`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.mixture`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.noiseVariance`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.penalizedEnergy`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.smoothLaw`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.smoothLaw_EntryLaw`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth.two_copy_gram_det_nonzero_iff`
- Dependency: [D5/S3/Analytic/Probability/GaussianPolynomialLog](GaussianPolynomialLog.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
