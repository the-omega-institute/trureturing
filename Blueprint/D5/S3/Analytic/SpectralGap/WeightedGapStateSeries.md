# WeightedGapStateSeries

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Theorem 1.1 (coefficient_next).**

$$\forall (A B: \mathbb{R}), \forall (n: \mathbb{N}), coefficient A B (n + 2) = (A \cdot coefficient A B n + B \cdot coefficient A B (n - 1)) / ((n + 1 : \mathbb{R}) \cdot (n + 2 : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.coefficient_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The recurrence also has the displayed form with the index shifted by two.

**Theorem 1.2 (state_total).**

$$\forall (A B: \mathbb{R}), \forall (n: \mathbb{N}), (state A B n) . total = \sum_{k \in Finset . range (n + 2)} (coefficient A B k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.state_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated state coordinate equals the finite sum of coefficients through the next index.

**Definition 1.3 (aValue2).**

$$aValue2 = (value ! [ Real . pi ] (Expr . mul (- 38858787444486999357325107 / 1000000000000000000000000) (- 9714696861121749839268937 / 250000000000000000000000) (Expr . mul (- 39478920883584609751820237 / 1000000000000000000000000) (- 7895784176716921950313781 / 200000000000000000000000) (Expr . neg (- 4000050992847 / 1000000000000) (- 4000050992847 / 1000000000000) (Expr . const (4000050992847 / 1000000000000) (4000050992847 / 1000000000000) (4000050992847 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.4 (bValue2).**

$$bValue2 = (value ! [ Real . pi ] (Expr . mul (- 1240266878195220788994209 / 1000000000000000000000000) (- 248053375639044157796473 / 200000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 4000050992847 / 100000000000000) (- 4000050992847 / 100000000000000) (- 4000050992847 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.5 (polynomial_sign2).**

$$(state aValue2 bValue2 79) . total < - (1 : \mathbb{R}) / 10 ^{15}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.polynomial_sign2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.6 (aValue_eq2).**

$$aValue2 = - (Real . pi ^{2}) \cdot ((4000050992847 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue_eq2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.7 (bValue_eq2).**

$$bValue2 = Real . pi ^{3} \cdot ((0 : \mathbb{R}) - ((4000050992847 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue_eq2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.8 (a_bound2).**

$$| aValue2 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.a_bound2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.9 (b_bound2).**

$$| bValue2 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.b_bound2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Definition 1.10 (aValue3).**

$$aValue3 = (value ! [ Real . pi ] (Expr . mul (- 38858787444525857649395859 / 1000000000000000000000000) (- 38858787444525857649146499 / 1000000000000000000000000) (Expr . mul (- 7895784176724817633884919 / 200000000000000000000000) (- 19739460441812044084586631 / 500000000000000000000000) (Expr . neg (- 4000050992851 / 1000000000000) (- 4000050992851 / 1000000000000) (Expr . const (4000050992851 / 1000000000000) (4000050992851 / 1000000000000) (4000050992851 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.11 (bValue3).**

$$bValue3 = (value ! [ Real . pi ] (Expr . mul (- 1240266878196461040061421 / 1000000000000000000000000) (- 1240266878196461040049577 / 1000000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 4000050992851 / 100000000000000) (- 4000050992851 / 100000000000000) (- 4000050992851 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.12 (polynomial_sign3).**

$$(1 : \mathbb{R}) / 10 ^{15} < (state aValue3 bValue3 79) . total$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.polynomial_sign3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.13 (aValue_eq3).**

$$aValue3 = - (Real . pi ^{2}) \cdot ((4000050992851 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue_eq3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.14 (bValue_eq3).**

$$bValue3 = Real . pi ^{3} \cdot ((0 : \mathbb{R}) - ((4000050992851 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue_eq3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.15 (a_bound3).**

$$| aValue3 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.a_bound3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.16 (b_bound3).**

$$| bValue3 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.b_bound3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue_eq2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.aValue_eq3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.a_bound2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.a_bound3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue_eq2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.bValue_eq3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.b_bound2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.b_bound3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.coefficient_next`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.polynomial_sign2`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.polynomial_sign3`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapStateSeries.state_total`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapMajorant](WeightedGapMajorant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate](WeightedGapPolynomialCertificate.md)
