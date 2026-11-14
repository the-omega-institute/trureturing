# Sample Covariance Bernoulli Orders

## Abstract

SampleCovarianceBernoulliOrders mathematical statements.

**Definition 1.1 (Noise.noise).**

$$\forall \{ n : \mathbb{N} \} (b : Bool), Noise. noise (n := n) b = (fun (i j : Fin n) \mapsto MvPolynomial. X (b, false, i, j) + MvPolynomial. C Complex. I * MvPolynomial. X (b, true, i, j))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.noise` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.noise is given by the displayed expression.

**Definition 1.2 (Noise.poly).**

$$\forall \{ n : \mathbb{N} \} (A C : Matrix (Fin n) (Fin n) \mathbb{C}), Noise. poly A C = (D5. S3. Analytic. Probability. GaussianPolynomialLog. Covariance. pairDet ((A. map MvPolynomial. C)) ((C. map MvPolynomial. C)) (noise false) (noise true))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.poly` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.poly is given by the displayed expression.

**Definition 1.3 (Noise.evalNoise).**

$$\forall \{ n : \mathbb{N} \} (G K : Matrix (Fin n) (Fin n) \mathbb{C}), Noise. evalNoise G K = (MvPolynomial. eval_{2}Hom (RingHom. id \mathbb{C}) (fun \langle b, im, i, j \rangle \mapsto if im then ((if b then K i j else G i j). im : \mathbb{C}) else ((if b then K i j else G i j). re : \mathbb{C})))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.evalNoise` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.evalNoise is given by the displayed expression.

**Lemma 1.4 (Noise.poly_ne_zero).**

$$\forall \{ n : \mathbb{N} \} (A C : Matrix (Fin n) (Fin n) \mathbb{C}), poly A C \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.poly_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.poly_ne_zero satisfies the displayed statement.

**Definition 1.5 (Events.bmat).**

$$\forall \{ n : \mathbb{N} \} (b : ((Bool \times Fin n \times Fin n) \to Bool)) (side : Bool), Events. bmat b side = (Matrix. of (fun i j \mapsto if b (side, i, j) then (Real. sqrt 255 : \mathbb{C}) else (- 1/ Real. sqrt 255 : \mathbb{R})))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.bmat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Events.bmat is given by the displayed expression.

**Definition 1.6 (Events.k).**

$$\forall \{ n : \mathbb{N} \} (b : ((Bool \times Fin n \times Fin n) \to Bool)), Events. k b = ((poly (bmat b false) (bmat b true)). natTrailingDegree)$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.k` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Events.k is given by the displayed expression.

**Definition 1.7 (Events.L).**

$$\forall (n : \mathbb{N}), Events. L n = ((\sum b : ((Bool \times Fin n \times Fin n) \to Bool), D5. S3. StatisticalMechanics. ParticleProcesses. ExclusionMovingParticleOptimality. bernoulli (1/ 256) (fun i \mapsto finTwoEquiv. symm (b i)) * k b) / (n: \mathbb{R})^{2})$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Events.L is given by the displayed expression.

**Lemma 1.8 (Events.w_sum).**

$$\forall (n : \mathbb{N}), \sum b : ((Bool \times Fin n \times Fin n) \to Bool), D5. S3. StatisticalMechanics. ParticleProcesses. ExclusionMovingParticleOptimality. bernoulli (1/ 256) (fun i \mapsto finTwoEquiv. symm (b i)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.w_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Events.w_sum satisfies the displayed statement.

**Lemma 1.9 (Events.L_gap).**

$$L 2 < L 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.L_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Events.L_gap satisfies the displayed statement.

**Lemma 1.10 (Noise.eval_pairDet).**

$$\forall \{ n : \mathbb{N} \} (\varepsilon : \mathbb{R}) (A C G K : Matrix (Fin n) (Fin n) \mathbb{C}), (D5. S3. Analytic. Probability. GaussianPolynomialLog. Covariance. pairDet A C G K). eval (\varepsilon: \mathbb{C}) = Matrix. det (Matrix. kronecker (((A+ (\varepsilon: \mathbb{C}) \cdot G)* (A+ (\varepsilon: \mathbb{C}) \cdot G)^{H})) ((1 : Matrix (Fin n) (Fin n) \mathbb{C}))- Matrix. kronecker ((1 : Matrix (Fin n) (Fin n) \mathbb{C})) (((C+ (\varepsilon: \mathbb{C}) \cdot K)* (C+ (\varepsilon: \mathbb{C}) \cdot K)^{H})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.eval_pairDet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.eval_pairDet satisfies the displayed statement.

**Definition 1.11 (Noise.polyAt).**

$$\forall \{ n : \mathbb{N} \} (A C : Matrix (Fin n) (Fin n) \mathbb{C}) (\varepsilon : \mathbb{R}), Noise. polyAt A C \varepsilon = ((poly A C). eval (MvPolynomial. C (\varepsilon: \mathbb{C})))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.polyAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.polyAt is given by the displayed expression.

**Lemma 1.12 (Noise.evalNoise_polyAt).**

$$\forall \{ n : \mathbb{N} \} (\varepsilon : \mathbb{R}) (A C G K : Matrix (Fin n) (Fin n) \mathbb{C}), evalNoise G K (polyAt A C \varepsilon) = (D5. S3. Analytic. Probability. GaussianPolynomialLog. Covariance. pairDet A C G K). eval (\varepsilon: \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.evalNoise_polyAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.evalNoise_polyAt satisfies the displayed statement.

**Lemma 1.13 (Noise.polyAt_ne_zero).**

$$\forall \{ n : \mathbb{N} \} (A C : Matrix (Fin n) (Fin n) \mathbb{C}) (\varepsilon : \mathbb{R}), (\varepsilon \neq 0) \to polyAt A C \varepsilon \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.polyAt_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Noise.polyAt_ne_zero satisfies the displayed statement.

**Lemma 1.14 (Gaussian.gaussian_mv_log_integrable).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) \{ n : \mathbb{N} \} (p : MvPolynomial (Fin n) \mathbb{C}), v \neq 0 \to p \neq 0 \to (\forall^{ae}  x \operatorname{d} Measure. pi (Function. const (Fin n) (gaussianReal m v)), MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p \neq 0) \land Integrable (fun x \mapsto Real. log \Vert MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) p\Vert ) (Measure. pi (Function. const (Fin n) (gaussianReal m v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.gaussian_mv_log_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Gaussian.gaussian_mv_log_integrable satisfies the displayed statement.

**Lemma 1.15 (Gaussian.gaussian_noiseFamily_log_order).**

$$\forall \{ n N : \mathbb{N} \} (m : \mathbb{R}) (v : \operatorname{NNReal}) (q : Fin (N+ 1) \to MvPolynomial (Fin n) \mathbb{C}) (d : Fin n \to_{0} \mathbb{N}) (k : \mathbb{N}), v \neq 0 \to (q 0). coeff d \neq 0 \to Tendsto (fun \varepsilon : \mathbb{R} \mapsto - (\int x, Real. log \Vert (\varepsilon : \mathbb{C})^{k} * MvPolynomial. eval (fun i \mapsto (x i : \mathbb{C})) (\sum j : Fin (N+ 1), MvPolynomial. C ((\varepsilon : \mathbb{C})^{j : \mathbb{N}}) * q j)\Vert \operatorname{d} Measure. pi (Function. const (Fin n) (gaussianReal m v))) / Real. log (1/ \varepsilon)) (\mathcal{N} [ >  ] 0) (\mathcal{N} (k : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.gaussian_noiseFamily_log_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Gaussian.gaussian_noiseFamily_log_order satisfies the displayed statement.

## References

- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.L`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.L_gap`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.bmat`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.evalNoise`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.evalNoise_polyAt`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.eval_pairDet`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.gaussian_mv_log_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.gaussian_noiseFamily_log_order`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.k`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.noise`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.poly`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.polyAt`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.polyAt_ne_zero`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.poly_ne_zero`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders.w_sum`
- Dependency: [D5/S3/Analytic/Probability/GaussianPolynomialLog](GaussianPolynomialLog.md)
- Dependency: [D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth](SampleCovarianceSpectralAndSmooth.md)
- Dependency: [D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality](../../StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.md)
