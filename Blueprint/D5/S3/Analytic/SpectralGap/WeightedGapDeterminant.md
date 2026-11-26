# WeightedGapDeterminant

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Definition 1.1 (solution).**

$$\forall (A B t: \mathbb{R}), solution A B t = (tsum (fun n : \mathbb{N} \mapsto coefficient A B n \cdot t ^{n}))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.solution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The solution is the real power series with the recursively defined coefficients.

**Theorem 1.2 (series_summable).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (\forall (t: \mathbb{R}), (t \in Icc (0 : \mathbb{R}) 1) \Rightarrow (Summable (fun n : \mathbb{N} \mapsto coefficient A B n \cdot t ^{n}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.series_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

For the indicated parameter bounds, the power series converges throughout the closed unit interval.

**Theorem 1.3 (solution_continuous).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (ContinuousOn (solution A B) (Icc 0 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.solution_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

For the indicated parameter bounds, the power-series solution is continuous on the closed unit interval.

**Theorem 1.4 (forcing_hasSum).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (\forall (t: \mathbb{R}), (t \in Icc (0 : \mathbb{R}) 1) \Rightarrow (HasSum (fun n : \mathbb{N} \mapsto (A \cdot coefficient A B n + B \cdot coefficient A B (n - 1)) \cdot t ^{n}) ((A + B \cdot t) \cdot solution A B t))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.forcing_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The affine factor times the solution is the sum of the corresponding coefficient series.

**Theorem 1.5 (volterra_monomial).**

$$\forall (x: \mathbb{R}), \forall (n: \mathbb{N}), (\int_{(0 : \mathbb{R})}^{x} ((x - t) \cdot t ^{n}) d t) = x ^{(n + 2)} / ((n + 1 : \mathbb{R}) \cdot (n + 2 : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.volterra_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The integral of the monomial against the linear kernel has the displayed closed form for every real endpoint.

**Theorem 1.6 (forcing_coefficient_bound).**

$$\forall (A B: \mathbb{R}), (| A | \leq 64) \Rightarrow ((| B | \leq 32) \Rightarrow (\forall (n: \mathbb{N}), | A \cdot coefficient A B n + B \cdot coefficient A B (n - 1) | \leq 128 \cdot (3 : \mathbb{R}) ^{16} \cdot (1 / 2 : \mathbb{R}) ^{n}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.forcing_coefficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The affine combination of adjacent coefficients satisfies the displayed uniform geometric estimate.

**Theorem 1.7 (coefficient_continuous).**

$$\forall (A B: \mathbb{R} \to \mathbb{R}), (Continuous A) \Rightarrow ((Continuous B) \Rightarrow (\forall (n: \mathbb{N}), Continuous (fun z : \mathbb{R} \mapsto coefficient (A z) (B z) n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.coefficient_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Continuous parameter functions give a continuous coefficient function at each fixed index.

**Definition 1.8 (aValue4).**

$$aValue4 = (value ! [ Real . pi ] (Expr . mul (- 61669807176047072268157 / 6250000000000000000000) (- 49335845740837657814209 / 5000000000000000000000) (Expr . mul (- 2004927151687121156875173 / 200000000000000000000000) (- 2004927151687121156862409 / 200000000000000000000000) (Expr . neg (- 253926990157 / 250000000000) (- 253926990157 / 250000000000) (Expr . const (253926990157 / 250000000000) (253926990157 / 250000000000) (253926990157 / 250000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.9 (bValue4).**

$$bValue4 = (value ! [ Real . pi ] (Expr . mul (- 4870453733150241185553 / 1000000000000000000000000) (- 2435226866575120592753 / 500000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 3926990157 / 25000000000000) (- 3926990157 / 25000000000000) (- 3926990157 / 25000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.10 (polynomial_sign4).**

$$(1 : \mathbb{R}) / 10 ^{15} < (state aValue4 bValue4 79) . total$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.polynomial_sign4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.11 (aValue_eq4).**

$$aValue4 = - (Real . pi ^{2}) \cdot ((253926990157 / 250000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue_eq4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.12 (bValue_eq4).**

$$bValue4 = Real . pi ^{3} \cdot ((1 : \mathbb{R}) - ((253926990157 / 250000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue_eq4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.13 (a_bound4).**

$$| aValue4 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.a_bound4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.14 (b_bound4).**

$$| bValue4 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.b_bound4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Definition 1.15 (aValue5).**

$$aValue5 = (value ! [ Real . pi ] (Expr . mul (- 77087258970362420741999 / 7812500000000000000000) (- 1233396143525798731864069 / 125000000000000000000000) (Expr . mul (- 10024635758475084201980223 / 1000000000000000000000000) (- 10024635758475084201916403 / 1000000000000000000000000) (Expr . neg (- 126963495079 / 125000000000) (- 126963495079 / 125000000000) (Expr . const (126963495079 / 125000000000) (126963495079 / 125000000000) (126963495079 / 125000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.16 (bValue5).**

$$bValue5 = (value ! [ Real . pi ] (Expr . mul (- 974090746878098450553 / 200000000000000000000000) (- 2435226867195246126359 / 500000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 1963495079 / 12500000000000) (- 1963495079 / 12500000000000) (- 1963495079 / 12500000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.17 (polynomial_sign5).**

$$(state aValue5 bValue5 79) . total < - (1 : \mathbb{R}) / 10 ^{15}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.polynomial_sign5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.18 (aValue_eq5).**

$$aValue5 = - (Real . pi ^{2}) \cdot ((126963495079 / 125000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue_eq5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.19 (bValue_eq5).**

$$bValue5 = Real . pi ^{3} \cdot ((1 : \mathbb{R}) - ((126963495079 / 125000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue_eq5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.20 (a_bound5).**

$$| aValue5 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.a_bound5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.21 (b_bound5).**

$$| bValue5 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.b_bound5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue_eq4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.aValue_eq5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.a_bound4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.a_bound5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue_eq4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.bValue_eq5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.b_bound4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.b_bound5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.coefficient_continuous`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.forcing_coefficient_bound`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.forcing_hasSum`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.polynomial_sign4`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.polynomial_sign5`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.series_summable`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.solution`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.solution_continuous`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapDeterminant.volterra_monomial`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapMajorant](WeightedGapMajorant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate](WeightedGapPolynomialCertificate.md)
