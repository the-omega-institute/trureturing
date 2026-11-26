# WeightedGapVolterra

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Theorem 1.1 (solution_volterra).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (\forall (x: \mathbb{R}), (x \in Icc (0 : \mathbb{R}) 1) \Rightarrow (solution A B x = x + \int_{(0 : \mathbb{R})}^{x} ((x - t) \cdot (A + B \cdot t) \cdot solution A B t) d t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.solution_volterra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The power-series solution satisfies the integrated second-order equation with value zero and slope one at the origin.

**Definition 1.2 (aParameter).**

$$\forall (z: \mathbb{R}), aParameter z = (- (Real . pi ^{2}) \cdot z \cdot (1 - Real . pi / 200))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aParameter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

This is the constant coefficient in the equation after rescaling the spatial interval to the unit interval.

**Definition 1.3 (bParameter).**

$$\forall (\delta z: \mathbb{R}), bParameter \delta z = (Real . pi ^{3} \cdot (\delta - z) / 100)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bParameter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

This is the linear coefficient in the rescaled equation for the indicated potential slope and spectral parameter.

**Theorem 1.4 (parameter_bounds).**

$$\forall (\delta z: \mathbb{R}), (\delta \in Icc (0 : \mathbb{R}) 1) \Rightarrow ((z \in Icc (0 : \mathbb{R}) 5) \Rightarrow (| aParameter z | \leq 64 \land | bParameter \delta z | \leq 32))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.parameter_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The displayed rectangle of slopes and spectral parameters lies inside the coefficient estimates parameter range.

**Theorem 1.5 (determinant_continuous).**

$$\forall (\delta: \mathbb{R}), (\delta \in Icc (0 : \mathbb{R}) 1) \Rightarrow (ContinuousOn (fun z : \mathbb{R} \mapsto solution (aParameter z) (bParameter \delta z) 1) (Icc 0 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.determinant_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The shooting determinant is continuous in the spectral parameter on the indicated closed interval.

**Theorem 1.6 (short_full_series_tail).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (| (tsum (fun n : \mathbb{N} \mapsto coefficient A B n)) - \sum_{n \in Finset . range 81} (coefficient A B n) | \leq 2 \cdot (3 : \mathbb{R}) ^{16} / 2 ^{81}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.short_full_series_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The displayed geometric bound controls the remainder after the polynomial of degree eighty.

**Theorem 1.7 (short_remainder_lt).**

$$2 \cdot (3 : \mathbb{R}) ^{16} / 2 ^{81} < 1 / 10 ^{16}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.short_remainder_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The degree-eighty geometric remainder bound is strictly less than one over ten to the sixteenth power.

**Definition 1.8 (aValue6).**

$$aValue6 = (value ! [ Real . pi ] (Expr . mul (- 39011169810722420273864229 / 1000000000000000000000000) (- 39011169810722420273613891 / 1000000000000000000000000) (Expr . mul (- 19816867532649884990866187 / 500000000000000000000000) (- 4954216883162471247685007 / 125000000000000000000000) (Expr . neg (- 4015736948983 / 1000000000000) (- 4015736948983 / 1000000000000) (Expr . const (4015736948983 / 1000000000000) (4015736948983 / 1000000000000) (4015736948983 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue6` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.9 (bValue6).**

$$bValue6 = (value ! [ Real . pi ] (Expr . mul (- 467533871175850606991657 / 500000000000000000000000) (- 58441733896981325873399 / 62500000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 3015736948983 / 100000000000000) (- 3015736948983 / 100000000000000) (- 3015736948983 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue6` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.10 (polynomial_sign6).**

$$(state aValue6 bValue6 79) . total < - (1 : \mathbb{R}) / 10 ^{15}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.polynomial_sign6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.11 (aValue_eq6).**

$$aValue6 = - (Real . pi ^{2}) \cdot ((4015736948983 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue_eq6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.12 (bValue_eq6).**

$$bValue6 = Real . pi ^{3} \cdot ((1 : \mathbb{R}) - ((4015736948983 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue_eq6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.13 (a_bound6).**

$$| aValue6 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.a_bound6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.14 (b_bound6).**

$$| bValue6 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.b_bound6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Definition 1.15 (aValue7).**

$$aValue7 = (value ! [ Real . pi ] (Expr . mul (- 1950558490538063928296749 / 50000000000000000000000) (- 19505584905380639282842321 / 500000000000000000000000) (Expr . mul (- 39633735065339248399336731 / 1000000000000000000000000) (- 39633735065339248399084413 / 1000000000000000000000000) (Expr . neg (- 4015736948987 / 1000000000000) (- 4015736948987 / 1000000000000) (Expr . const (4015736948987 / 1000000000000) (4015736948987 / 1000000000000) (4015736948987 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue7` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.16 (bValue7).**

$$bValue7 = (value ! [ Real . pi ] (Expr . mul (- 467533871176470732525263 / 500000000000000000000000) (- 233766935588235366260399 / 250000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 3015736948987 / 100000000000000) (- 3015736948987 / 100000000000000) (- 3015736948987 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue7` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.17 (polynomial_sign7).**

$$(1 : \mathbb{R}) / 10 ^{15} < (state aValue7 bValue7 79) . total$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.polynomial_sign7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.18 (aValue_eq7).**

$$aValue7 = - (Real . pi ^{2}) \cdot ((4015736948987 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue_eq7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.19 (bValue_eq7).**

$$bValue7 = Real . pi ^{3} \cdot ((1 : \mathbb{R}) - ((4015736948987 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue_eq7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.20 (a_bound7).**

$$| aValue7 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.a_bound7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.21 (b_bound7).**

$$| bValue7 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.b_bound7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aParameter`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue_eq6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.aValue_eq7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.a_bound6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.a_bound7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bParameter`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue_eq6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.bValue_eq7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.b_bound6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.b_bound7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.determinant_continuous`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.parameter_bounds`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.polynomial_sign6`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.polynomial_sign7`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.short_full_series_tail`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.short_remainder_lt`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapVolterra.solution_volterra`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapDeterminant](WeightedGapDeterminant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapMajorant](WeightedGapMajorant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate](WeightedGapPolynomialCertificate.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapStateSeries](WeightedGapStateSeries.md)
