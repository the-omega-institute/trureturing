# WeightedGapMajorant

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Definition 1.1 (coefficient).**

$$\forall (A B: \mathbb{R}), coefficient A B = (fun (n : \mathbb{N}) \mapsto match n with | 0 \mapsto 0 | 1 \mapsto 1 | 2 \mapsto 0 | n + 3 \mapsto (A \cdot coefficient A B (n + 1) + B \cdot coefficient A B n) / ((n + 2 : \mathbb{R}) \cdot (n + 3 : \mathbb{R})))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The initial coefficients are zero, one, and zero; subsequent coefficients satisfy the displayed three-step recurrence.

**Theorem 1.2 (coefficient_weighted_bound).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (\forall (n: \mathbb{N}), | coefficient A B n | \cdot 2 ^{n} \leq (3 : \mathbb{R}) ^{16}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.coefficient_weighted_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Multiplication by two to the coefficient index gives the uniform bound three to the sixteenth power.

**Theorem 1.3 (geometric_coefficient_tail).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (M: \mathbb{R}), (\forall n : \mathbb{N} , | c n | \cdot 2 ^{n} \leq M) \Rightarrow (\forall (N: \mathbb{N}), | (tsum (fun n : \mathbb{N} \mapsto c n)) - \sum_{n \in Finset . range N} (c n) | \leq 2 \cdot M / 2 ^{N})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.geometric_coefficient_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

A geometric coefficient bound controls the difference between the infinite series and each finite partial sum.

**Definition 1.4 (aValue1).**

$$aValue1 = (value ! [ Real . pi ] (Expr . mul (- 2428617296905570659967249 / 250000000000000000000000) (- 1942893837524456527961331 / 200000000000000000000000) (Expr . mul (- 9869498914037038654536273 / 1000000000000000000000000) (- 61684368212731491590459 / 6250000000000000000000) (Expr . neg (- 999989311927 / 1000000000000) (- 999989311927 / 1000000000000) (Expr . const (999989311927 / 1000000000000) (999989311927 / 1000000000000) (999989311927 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.aValue1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.5 (bValue1).**

$$bValue1 = (value ! [ Real . pi ] (Expr . mul (- 310059452829512029335543 / 1000000000000000000000000) (- 310059452829512029332581 / 1000000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 999989311927 / 100000000000000) (- 999989311927 / 100000000000000) (- 999989311927 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.bValue1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.6 (polynomial_sign1).**

$$(state aValue1 bValue1 79) . total < - (1 : \mathbb{R}) / 10 ^{15}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.polynomial_sign1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.7 (aValue_eq1).**

$$aValue1 = - (Real . pi ^{2}) \cdot ((999989311927 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.aValue_eq1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.8 (bValue_eq1).**

$$bValue1 = Real . pi ^{3} \cdot ((0 : \mathbb{R}) - ((999989311927 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.bValue_eq1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.9 (a_bound1).**

$$| aValue1 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.a_bound1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.10 (b_bound1).**

$$| bValue1 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.b_bound1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.aValue1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.aValue_eq1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.a_bound1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.bValue1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.bValue_eq1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.b_bound1`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.coefficient`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.coefficient_weighted_bound`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.geometric_coefficient_tail`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapMajorant.polynomial_sign1`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate](WeightedGapPolynomialCertificate.md)
