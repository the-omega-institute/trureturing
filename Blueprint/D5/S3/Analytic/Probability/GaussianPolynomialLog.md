# Gaussian Polynomial Log

## Abstract

GaussianPolynomialLog mathematical statements.

**Lemma 1.1 (gaussian_roots_nonzero).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) (s : Multiset \mathbb{C}), (v \neq 0) \to \forall^{ae}  x : \mathbb{R} \operatorname{d} gaussianReal m v, (s. map (fun z \mapsto (x : \mathbb{C})- z)). prod \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_roots_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gaussian_roots_nonzero satisfies the displayed statement.

**Lemma 1.2 (gaussian_polynomial_log_integrable).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) (p : Polynomial \mathbb{C}), (v \neq 0) \to (p \neq 0) \to Integrable (fun x : \mathbb{R} \mapsto Real. log \Vert p. eval (x : \mathbb{C})\Vert ) (gaussianReal m v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_polynomial_log_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gaussian_polynomial_log_integrable satisfies the displayed statement.

**Definition 1.3 (rootLogCost).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}), rootLogCost m v = ((\int x : \mathbb{R}, | x| \operatorname{d} gaussianReal m v) + (Real. sqrt (2 * Real. pi * v))^{-1} * (\int x : \mathbb{R}, Real. posLog x^{-1}))$$

*Formalization.* `D5/S3/Analytic/Probability/GaussianPolynomialLog.rootLogCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

rootLogCost is given by the displayed expression.

**Lemma 1.4 (rootLogCost_nonneg).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}), 0 \leq rootLogCost m v$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.rootLogCost_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

rootLogCost_nonneg satisfies the displayed statement.

**Lemma 1.5 (gaussian_polynomial_log_coeff_lower).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) (p : Polynomial \mathbb{C}) (j : \mathbb{N}), (v \neq 0) \to (p. coeff j \neq 0) \to Real. log \Vert p. coeff j\Vert - p. natDegree * (Real. log 2 + rootLogCost m v) \leq \int x : \mathbb{R}, Real. log \Vert p. eval (x : \mathbb{C})\Vert \operatorname{d} gaussianReal m v$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_polynomial_log_coeff_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gaussian_polynomial_log_coeff_lower satisfies the displayed statement.

**Lemma 1.6 (gaussian_complex_pow_integrable).**

$$\forall (m : \mathbb{R}) (v : \operatorname{NNReal}) (k : \mathbb{N}), Integrable (fun x : \mathbb{R} \mapsto (x : \mathbb{C})^{k}) (gaussianReal m v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_complex_pow_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

gaussian_complex_pow_integrable satisfies the displayed statement.

**Lemma 1.7 (norm_eq_two_pos_sub).**

$$\forall (t : \mathbb{R}), \Vert t\Vert = 2 * max t 0 - t$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.norm_eq_two_pos_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

norm_eq_two_pos_sub satisfies the displayed statement.

**Lemma 1.8 (integrable_prod_of_pos_and_fiber_lower).**

$$\forall \{ \alpha \beta : Type*  \} [ MeasurableSpace \alpha ] [ MeasurableSpace \beta ] (\mu : Measure \alpha) (\nu : Measure \beta) [ SFinite \mu ] [ SFinite \nu ] (f : \alpha \times \beta \to \mathbb{R}) (g : \beta \to \mathbb{R}), (AEStronglyMeasurable f (\mu. prod \nu)) \to (Integrable (fun z \mapsto max (f z) 0) (\mu. prod \nu)) \to (\forall^{ae}  y \operatorname{d} \nu, Integrable (fun x \mapsto f (x, y)) \mu) \to (Integrable g \nu) \to (\forall^{ae}  y \operatorname{d} \nu, g y \leq \int x, f (x, y) \operatorname{d} \mu) \to Integrable f (\mu. prod \nu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.integrable_prod_of_pos_and_fiber_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

integrable_prod_of_pos_and_fiber_lower satisfies the displayed statement.

**Definition 1.9 (Covariance.affineGramPoly).**

$$\forall \{ R : Type*  \} [ CommRing R ] [ StarRing R ] \{ n : \mathbb{N} \} (A G : Matrix (Fin n) (Fin n) R), Covariance. affineGramPoly A G = ((A * A^{H}). map Polynomial. C + (Polynomial. X : Polynomial R) \cdot (A * G^{H} + G * A^{H}). map Polynomial. C + (Polynomial. X : Polynomial R)^{2} \cdot (G * G^{H}). map Polynomial. C)$$

*Formalization.* `D5/S3/Analytic/Probability/GaussianPolynomialLog.affineGramPoly` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.affineGramPoly is given by the displayed expression.

**Definition 1.10 (Covariance.pairDet).**

$$\forall \{ R : Type*  \} [ CommRing R ] [ StarRing R ] \{ n : \mathbb{N} \} (A C G K : Matrix (Fin n) (Fin n) R), Covariance. pairDet A C G K = (Matrix. det (Matrix. kronecker (affineGramPoly A G) ((1 : Matrix (Fin n) (Fin n) (Polynomial R)))- Matrix. kronecker ((1 : Matrix (Fin n) (Fin n) (Polynomial R))) (affineGramPoly C K)))$$

*Formalization.* `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.pairDet is given by the displayed expression.

**Lemma 1.11 (Covariance.rankOne_order_lower).**

$$\forall \{ R : Type*  \} [ CommRing R ] [ StarRing R ] [ Nontrivial R ] \{ s : \mathbb{N} \} (a : R) (G K : Matrix (Fin (s+ 1)) (Fin (s+ 1)) R), (Polynomial. X : Polynomial R)^{2* s* s+ 1} \mid pairDet (Matrix. single 0 0 a) (Matrix. single 0 0 a) G K$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.rankOne_order_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.rankOne_order_lower satisfies the displayed statement.

**Lemma 1.12 (Covariance.pairDet_degree_le).**

$$\forall \{ R : Type*  \} [ CommRing R ] [ StarRing R ] [ Nontrivial R ] \{ n : \mathbb{N} \} (A C G K : Matrix (Fin n) (Fin n) R), (pairDet A C G K). natDegree \leq 2* n* n$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_degree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.pairDet_degree_le satisfies the displayed statement.

**Lemma 1.13 (Covariance.pairDet_identity_noise_ne_zero).**

$$\forall \{ R : Type*  \} [ CommRing R ] [ StarRing R ] [ Nontrivial R ] \{ n : \mathbb{N} \} (A C : Matrix (Fin n) (Fin n) R), pairDet A C 1 0 \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_identity_noise_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.pairDet_identity_noise_ne_zero satisfies the displayed statement.

**Lemma 1.14 (Covariance.pairDet_rankOne_witness_order).**

$$\forall \{ s : \mathbb{N} \} (a : \mathbb{R}), (a \neq 0) \to (pairDet (Matrix. single 0 0 (a : \mathbb{C})) (Matrix. single 0 0 (a : \mathbb{C})) (1 : Matrix (Fin (s+ 1)) (Fin (s+ 1)) \mathbb{C}) 0). natTrailingDegree = 2* s* s+ 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_rankOne_witness_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Covariance.pairDet_rankOne_witness_order satisfies the displayed statement.

## References

- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.affineGramPoly`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_complex_pow_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_polynomial_log_coeff_lower`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_polynomial_log_integrable`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.gaussian_roots_nonzero`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.integrable_prod_of_pos_and_fiber_lower`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.norm_eq_two_pos_sub`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_degree_le`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_identity_noise_ne_zero`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.pairDet_rankOne_witness_order`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.rankOne_order_lower`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.rootLogCost`
- Truth anchor: `D5/S3/Analytic/Probability/GaussianPolynomialLog.rootLogCost_nonneg`
