---
slug: datta-dorlas-jozsa-benatti-2014-conditional-subentropy-conjecture-2
bibkey: datta2014conditionalsubentropy
doi: 10.48550/arXiv.1310.1312
url: https://arxiv.org/abs/1310.1312v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result
---

# Conditional subentropy and guessing min-entropy

## Problem

Datta, Dorlas, Jozsa and Benatti, *Properties of subentropy*, arXiv:1310.1312v1, §2.5.1, Conjecture 2:

> For a c-q state ρ_XB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ H_min(X|B) = − ln p_guess(X|B).

For every finite family of positive semidefinite complex matrices $A_x$ of total trace one, the joint state is $\bigoplus_x A_x$ and its marginal is $\sum_x A_x$. The claim uses equation (4), with normalized simplex measure from equation (3), for subentropy. Natural logarithms are used. Zero blocks, zero eigenvalues and repeated eigenvalues remain in scope.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (2), $C_n=1/2+\cdots+1/n$ | `C` | Inclusive sum from 2 to n. |
| Equation (3), normalized simplex measure | `simplexCoords`, `subentropySpectrum` | Nonnegative first n−1 coordinates of sum at most one; factorial times Lebesgue measure. |
| Equation (4), $Q=n\int\eta(\lambda\cdot x)\,dx-C_n$ | `subentropySpectrum`, `subentropy` | `Real.negMulLog`, the existing simplex `chart`, and all Hermitian eigenvalues. |
| Finite c-q state | `claim` | Arbitrary finite X and B; positive semidefinite blocks, total trace one. |
| Equation (13), $Q(X\mid B)=Q(\rho_{XB})-Q(\rho_B)$ | `claim` | Block diagonal state and summed marginal. |
| All POVMs; guessing min-entropy | `pGuess`, `result` | Supremum of the exact finite POVM scores; negative natural logarithm. |
| Typeclass and Hermitian binders | `claim` | Finite indexing and matrix well-formedness; Hermiticity follows from positivity. |

## Motivation

[Preregistration #18776](https://github.com/the-omega-institute/trureturing/issues/18776) identifies this as a tier-1 explicit published conjecture. The resolving declaration is `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound.result`.

## Gap

The source's literal simplex integral must agree with the repository's determinant-integral subentropy on every positive semidefinite trace-one matrix, including singular and repeated-spectrum matrices. The private `source_eq_determinant` bridge supplies this correspondence. The existing `POVMGram.cq_conditional_subentropy_guessing` is reused for the operational estimate. The settling result is classified bind-only after expansion of same-delivery helpers; its admission basis is `open-problem-resolution (#18776; Proved)`.

## Route

Radial decomposition of the exponential law and its Gamma moments express the normalized simplex integral as a Gaussian quadratic expectation. Spectral transport identifies that expression with determinant-integral subentropy. Normalize every nonzero positive block to a density state, using a harmless density state at zero weights. The canonical record and mixture states then have the same subentropy values as the block diagonal and summed matrices. The frozen conditional guessing theorem gives the conclusion.

All six public definitions retain the preregistered source expressions; the existing `chart` and `Real.negMulLog` are used directly. The private simplex measure uses `RenewalMinorantMaximalityRefutation.Ak` through the consumed `simplexCoords_eq_Ak` correspondence. No owner is published or re-pinned.

## Falsifier

A positive semidefinite finite block family of total trace one with $Q(X\mid B)>-\ln p_{\rm guess}(X\mid B)$ would contradict the formal statement. A discrepancy between the source integral and determinant-integral convention would invalidate the proposed transfer. The compiled result and its correspondence cover both obligations within the stated finite-dimensional model.

## Evidence

Kernel evidence: `D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.result : claim`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The four-slot escape audit is unfinished under [issue #20025](https://github.com/the-omega-institute/trureturing/issues/20025). The sole public theorem is `result`; no Reg mirror or `declared_validated` registration is delivered. The issue identifies the failed template attempt and missing compiled realization, source selection and binding evidence.

### Declaration judgement

| Module | Declaration | proof_shape | escape_witness | Consumers | Direct frozen dependencies |
| --- | --- | --- | --- | --- | --- |
| `D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound` | `D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.result`<br>`sha256:9fcbb1c6e8a8b9fe906f310157309a6c20c843a7cafd6b4ac2ed62f1c983a90b` | bind-only | none | External conjecture settlement | `D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing` + `D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.chart` + `sha256:f12940e4dca0ea47ade5588aa86134efde1ee9d876cebd7029a63dd54cf83706`<br>`D5/S3/Quantum/Foundation/FiniteStateChannel` + `D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState` + `sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5`<br>`D5/S3/Quantum/Information/OrthogonalRecordEntropy` + `D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState` + `sha256:3fbfa607a1bbd397ac41fc4b8f5dfd95bd74c209e2fdf8fc34b226f210886c59`<br>`D5/S3/Quantum/Information/OrthogonalRecordEntropy` + `D5.S3.Quantum.Information.OrthogonalRecordEntropy.recordState` + `sha256:82f2241204cdd35e8336a4202d244cee9e882a89e93959e291896658ab58c93a`<br>`D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace` + `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal` + `sha256:a6348a7a914aad14d232dc4b4361d13353848b8bc54c1eb04c2019f6d00589d8`<br>`D5/S3/Quantum/Subentropy/Basic` + `D5.S3.Quantum.Subentropy.Basic.matrixSubentropy` + `sha256:1c5fdaf526e28e3e61827e243def4b593a85eee0439ad39231d25b0d4934f852`<br>`D5/S3/Quantum/Subentropy/Basic` + `D5.S3.Quantum.Subentropy.Basic.subentropy` + `sha256:d8be09c589dc1b6bbc2eb39baf322dc4cb031b9e00180360783a4d68a987841b`<br>`D5/S3/Quantum/Subentropy/Basic` + `D5.S3.Quantum.Subentropy.Basic.subentropyKernel` + `sha256:3da2f397e20d37e2e5faa36585310fb90c3e711fdef2c50b954771fb59fc526a`<br>`D5/S3/Quantum/Subentropy/ClassicalQuantumGram` + `D5.S3.Quantum.Subentropy.ClassicalQuantumGram.conditionalSubentropy` + `sha256:c8625574ea376aace2bc076dc3733e3554c16b23f9a9eb25a3dba220f2829f4b`<br>`D5/S3/Quantum/Subentropy/GaussianMatrix` + `D5.S3.Quantum.Subentropy.GaussianMatrix.matrix_subentropy_gaussian_entropy` + `sha256:ddc126b442874d917e4b995ee0c2cef8bab9dae916da701befc0aa9848197b61`<br>`D5/S3/Quantum/Subentropy/GaussianMatrix` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic.congr_simp` + `sha256:23178faa1e9937636d7e541a05710c735649890af27c17bf8b283fe247d352d3`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.complexGaussianCoordinates` + `sha256:6fd2ae0a8ed8f70c0781f25b956088ff14ae0a1fd4c0cda95412fa90db63a029`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.complexGaussianCoordinates._proof_1` + `sha256:000cacec289957d214a4b49c6f9b577dc1fbd95068d5256c75d8bea12a43803f`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.complex_coordinate_transport` + `sha256:f36cd84a7550d6fecf5e101bd44189b74a28616b34afa64514dc22feaafdfd19`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic` + `sha256:45e836be7a7690d64fd7bf84825d8221683eda68c284e23112d1974a580f1edb`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_1` + `sha256:b84e336425e73337497a7d20b68a320f349cbb16c794337905b56d9f7a033df4`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_2` + `sha256:e2d8db4cb82afca1a4323b05adf84c8b719155a266d26705a448455fc173e1f0`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.gaussianQuadratic._proof_3` + `sha256:fb561d851ee5a0bba49188425848e4728c1ebd593be940d16d9451f9a1f96731`<br>`D5/S3/Quantum/Subentropy/GaussianQuadratic` + `D5.S3.Quantum.Subentropy.GaussianQuadratic.spectral_transport` + `sha256:728980b7131dcd083b3d9fb10318ada92af378d042d79abe177ec62898c5ab14`<br>`D5/S3/Quantum/Subentropy/GuessingProbability` + `D5.S3.Quantum.Subentropy.GuessingProbability.pGuess` + `sha256:9d0b3f85b9b0480be1af1207d05617b7bae17de09b1531d939cf1974fb2326c2`<br>`D5/S3/Quantum/Subentropy/GuessingProbability` + `D5.S3.Quantum.Subentropy.GuessingProbability.successProbability` + `sha256:41341de581429b0f229e3797b8bf02a59129ed8f9c41b75f285e205e71b504ad`<br>`D5/S3/Quantum/Subentropy/GuessingProbability` + `D5.S3.Quantum.Subentropy.GuessingProbability.successProbabilitySet` + `sha256:fb2cd516d4ae06aca890fd13924b9d3b9407fdd00975dad85f00f14963bc9dc1`<br>`D5/S3/Quantum/Subentropy/POVMGram` + `D5.S3.Quantum.Subentropy.POVMGram.cq_conditional_subentropy_guessing` + `sha256:d4753a2853450488b89e9befd43efcdbf99f83817d39ef95bb624b18b0910e30`<br>`D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation` + `D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation.Ak` + `sha256:1cfa7d89b18df23286fc3e5ccd024c57cb176e806ca772307ebfd19111dbdb1d` |

### Helpers and consumers

| Helper (full Lean name) | proof_shape | Direct consumers (identifiers in the same module) |
| --- | --- | --- |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.lintegral_fin_prod` | bind-only | `pi_withDensity_fin` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.pi_withDensity_fin` | bind-only | `orthantExponential_eq_pi` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexPoint_succ_snoc` | bind-only | `simplexLinear_radial_identity` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.phi_mul_nonneg` | bind-only | `phi_product_integral_ae` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_scale_domain` | bind-only | `simplex_scaled_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.sumFiber` | bind-only | `simplex_sum_boundary_null`, `sumFiber_ne_top` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.sumFiber_ne_top` | bind-only | `simplex_sum_boundary_null` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_sum_boundary_null` | bind-only | `simplex_scaled_open_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_scaled_lintegral` | bind-only | `simplex_scaled_open_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.positive_ray_shift_lintegral` | bind-only | `simplex_radial_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_scaled_open_lintegral` | bind-only | `simplex_radial_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_radial_lintegral` | bind-only | `simplex_radial_weighted_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantTailMeasure` | bind-only | `exponentialTailMeasure`, `exponentialTailMeasure_eq_prod`, `exponentialTail_ae_domain`, `simplex_exponential_radial_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.radialCoordinateMap` | bind-only | `exponential_normalized_radial_map`, `exponential_phi_radial_factorization`, `exponential_radial_integral`, `radialCoordinateMap_measurable`, `simplex_exponential_radial_map`, `simplex_linear_first_moment`, `simplex_volume` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.radialCoordinateMap_measurable` | bind-only | `exponential_radial_integral`, `simplex_exponential_radial_map`, `simplex_volume` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_radial_weighted_lintegral` | bind-only | `simplex_exponential_radial_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponentialMeasure` | bind-only | `exponentialTailMeasure_eq_prod`, `exponentialTailMeasure_probability`, `exponentialTail_linear_moment`, `exponential_snoc_split_map`, `orthantExponentialMeasure_probability`, `orthantExponential_coordinate_integrable`, `orthantExponential_coordinate_moment`, `orthantExponential_eq_pi`, `orthantExponential_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponentialTailMeasure` | bind-only | `exponentialTailMeasure_eq_prod`, `exponentialTailMeasure_probability`, `exponentialTail_ae_domain`, `exponentialTail_linear_moment`, `exponential_normalized_radial_map`, `exponential_phi_radial_factorization`, `exponential_radial_integral`, `exponential_snoc_split_map`, `simplex_exponential_radial_map`, `simplex_linear_first_moment`, `simplex_volume`, `subentropySpectrum_exponential_pi_representation`, `subentropySpectrum_exponential_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.unnormalizedGammaMeasure` | bind-only | `expMeasure_one_density`, `exponential_normalized_radial_map`, `gamma_nat_density`, `normalizedGamma_integral`, `simplex_exponential_radial_map`, `simplex_volume`, `unnormalizedGammaMeasure_mass` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gamma_nat_density` | bind-only | `expMeasure_one_density`, `exponential_normalized_radial_map`, `normalizedGamma_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.expMeasure_one_density` | bind-only | `exponentialTailMeasure_eq_prod`, `orthantExponential_eq_pi`, `stdGaussian_squared_coordinates_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponentialTailMeasure_eq_prod` | bind-only | `exponentialTailMeasure_probability`, `exponentialTail_linear_moment`, `exponential_snoc_split_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_exponential_radial_map` | bind-only | `exponential_normalized_radial_map`, `simplex_volume` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthant_exponential_integral` | bind-only | `orthantExponentialMeasure_probability` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponentialMeasure_probability` | bind-only | `exponentialTailMeasure_probability`, `exponentialTail_linear_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.positiveExponentialMeasure_probability` | bind-only | `baseline_integral`, `exponentialTailMeasure_probability`, `exponentialTail_linear_moment`, `exponential_snoc_split_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponentialTailMeasure_probability` | bind-only | `simplex_volume` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gamma_integer_integral` | bind-only | `normalizedGamma_pow_moment`, `positive_exponential_integral_id`, `unnormalizedGammaMeasure_mass` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.unnormalizedGammaMeasure_mass` | bind-only | `simplex_volume` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_volume` | bind-only | `simplexMeasure_probability` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexCoords_eq_Ak` | bind-only | `subentropySpectrum_as_simplex_phi` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexMeasure` | bind-only | `exponential_normalized_radial_map`, `exponential_phi_radial_factorization`, `exponential_radial_integral`, `simplexMeasure_probability`, `simplex_linear_first_moment`, `simplex_linear_integrable`, `simplex_phi_integrable`, `subentropySpectrum_as_simplex_phi`, `subentropySpectrum_exponential_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropySpectrum_as_simplex_phi` | bind-only | `subentropySpectrum_exponential_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.harmonic_eq_one_add_C` | bind-only | `subentropySpectrum_exponential_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGammaMeasure_probability` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexMeasure_probability` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponential_normalized_radial_map` | bind-only | `exponential_radial_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponential_radial_integral` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gamma_log_moment` | bind-only | `normalizedGamma_phi_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_integral` | bind-only | `normalizedGamma_phi_moment`, `normalizedGamma_pow_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_pow_moment` | bind-only | `normalizedGamma_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_first_moment` | bind-only | `exponential_phi_radial_factorization`, `normalizedGamma_integrable_id`, `positiveExponential_first_moment`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_phi_moment` | bind-only | `exponential_phi_integral`, `exponential_phi_radial_factorization`, `normalizedGamma_phi_integrable` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_integrable_id` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponential_integral` | bind-only | `orthantExponential_coordinate_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthant_exponential_weighted_product` | bind-only | `orthantExponential_coordinate_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.positive_exponential_integral_id` | bind-only | `orthantExponential_coordinate_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponential_coordinate_moment` | bind-only | `exponentialTail_linear_moment`, `orthantExponential_coordinate_integrable` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponential_coordinate_integrable` | bind-only | `exponentialTail_linear_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_coord_le_one` | bind-only | `simplexCoords_isCompact` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexCoords_isClosed` | bind-only | `simplexCoords_isCompact` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexCoords_isCompact` | bind-only | `simplex_linear_integrable`, `simplex_phi_integrable` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexPoint_continuous` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment`, `simplex_linear_integrable`, `simplex_phi_integrable` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_linear_integrable` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_phi_integrable` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.positiveExponential_first_moment` | bind-only | `exponentialTail_linear_moment`, `positiveExponential_integrable_id` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.positiveExponential_integrable_id` | bind-only | `exponentialTail_linear_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponentialTail_linear_moment` | bind-only | `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplexLinear_radial_identity` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponentialTail_ae_domain` | bind-only | `exponential_phi_radial_factorization`, `simplex_linear_first_moment` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.simplex_linear_first_moment` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalizedGamma_phi_integrable` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.phi_product_integral_ae` | bind-only | `exponential_phi_radial_factorization` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponential_phi_radial_factorization` | bind-only | `subentropySpectrum_exponential_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropySpectrum_exponential_representation` | bind-only | `subentropySpectrum_exponential_pi_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.orthantExponential_eq_pi` | bind-only | `exponential_snoc_split_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponential_snoc_split_map` | bind-only | `subentropySpectrum_exponential_pi_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropySpectrum_exponential_pi_representation` | bind-only | `subentropySpectrum_gaussian_half_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.square_pos_image` | bind-only | `square_positive_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.square_positive_lintegral` | bind-only | `complex_sqnorm_radial_lintegral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.complex_sqnorm_radial_lintegral` | bind-only | `complex_sqnorm_volume_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.complex_sqnorm_volume_map` | bind-only | `complex_half_sqnorm_volume_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.map_withDensity_composed` | bind-only | `stdGaussian_complex_density_product`, `stdGaussian_complex_half_sqnorm_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_complex_eq_map_prod` | bind-only | `stdGaussian_complex_density_product` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_complex_density_product` | bind-only | `stdGaussian_complex_density` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gaussianPDF_complex_product` | bind-only | `stdGaussian_complex_density` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_complex_density` | bind-only | `stdGaussian_complex_half_sqnorm_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.complex_half_sqnorm_volume_map` | bind-only | `stdGaussian_complex_half_sqnorm_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_complex_half_sqnorm_map` | bind-only | `stdGaussian_squared_coordinates_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_complex_pi_map` | bind-only | `stdGaussian_squared_coordinates_map` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.stdGaussian_squared_coordinates_map` | bind-only | `baseline_integral`, `gaussian_squared_coordinate_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gaussian_squared_coordinate_integral` | bind-only | `subentropySpectrum_gaussian_half_representation` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropySpectrum_gaussian_half_representation` | bind-only | `subentropySpectrum_gaussian_half_pos` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.spectralCoordinates_quadratic` | bind-only | `gaussian_matrix_spectral_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.spectralCoordinates_gaussian_map` | bind-only | `gaussian_matrix_spectral_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.gaussian_matrix_spectral_integral` | bind-only | `subentropy_matrix_gaussian_half` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.eigenvalues0_sum` | bind-only | `subentropy_matrix_gaussian_half` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.trace_one_card_pos` | bind-only | `source_eq_determinant`, `subentropy_matrix_gaussian_half` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropySpectrum_gaussian_half_pos` | bind-only | `subentropy_matrix_gaussian_half` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.subentropy_matrix_gaussian_half` | bind-only | `source_eq_determinant` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.exponential_phi_integral` | bind-only | `baseline_integral` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.baseline_integral` | bind-only | `source_eq_determinant` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.source_eq_determinant` | bind-only | `result` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.normalize_ensemble` | bind-only | `determinant_cq_bound` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.determinant_reindex` | bind-only | `determinant_cq_bound` |
| `_private.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.0.D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound.determinant_cq_bound` | bind-only | `result` |

### Numerical evidence

The experiment is [the pinned directory in trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/7af205ad662eaabb07976da4cd86b75555e6101c/docs/reports/datta-dorlas-jozsa-benatti-2013-conjecture-2-conditional-subentropy).

Command: `/Users/auric/.sshx/43196ccfd59b1d204c3f3897/attempt-1/experiment-env/bin/python /Users/auric/trureturing-experiments/docs/reports/datta-dorlas-jozsa-benatti-2013-conjecture-2-conditional-subentropy/check.py`; exit 0, `RESULT PASS`. The committed `check.py` SHA-256 is `72c037123411fbde7853e64d3349ec84843b2dbb0706eb5ab06e7a1887d0acd6`; commit membership and local bytes were checked.

Computed scope: equation (4) agrees with equation (1) on spectra $(0.7,0.3)$, $(0.5,0.3,0.2)$ and $(0.61,0.27,0.12)$, with maximum difference $4.93\times10^{-32}$. Across 120 sampled c-q ensembles, the maximum of $Q(X\mid B)-(1-P_{\rm up})$ is $-0.0019293938015541088$ and the maximum primal–dual gap is $2.2579642044995296\times10^{-8}$. Here the script repairs a dual-feasible upper bound on guessing probability numerically. Across 400 sampled probability vectors, the largest tangent-bound residual is $-6.165877369270764\times10^{-9}$. The derivative check gives $1.0$ for $m=2,3,5,8$. The pinching gap is $0.01702$, compared with Monte Carlo relative entropy $0.01752\pm0.00029$. The solver emits an accuracy warning; these finite numerical readings are distinct from kernel evidence and establish no uniform numerical theorem.

## Triage

| Item | Status and evidence |
| --- | --- |
| Classification | Proved, kernel-checked `result`, resolving Conjecture 2 under the source integral convention. |
| Tier | Tier 1: explicit Conjecture 2 in the cited paper; source and literature checks recorded in #18776. |
| Stronger bound $Q(X\mid B)\le1-p_{\rm guess}(X\mid B)$ | Proved in prose below from the consumed frozen theorem and private correspondences; no separate public theorem is claimed. |
| Numerical checker | Computed: pinned experiment, exit 0 and SHA-256 above, with exactly the tested scope reported above. |
| Source Proposition 6 | The general formal result includes its two-pure-signal-state case by specialization. |
| Tightness for perfectly distinguishable states | Proved in prose below; numerical small margins are finite experiment evidence only. |
| Source Conjecture 1 | Outside this module's settlement; the separate repository subadditivity theorem is not on this module's dependency path. |
| A smaller operational upper bound | Open here; this delivery supplies no uniform refinement of $1-p_{\rm guess}$. |
| Literature completeness | `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Mechanism, kernel-checked in `result` and its private live dependencies.** The normalized simplex integral and determinant-integral subentropy agree through Gaussian radial decomposition. The finite c-q block family then fits the existing ensemble estimate. No positive-spectrum or nonzero-prior assumption is added.

**Stronger bound, proved in prose.** Set $p_x=\operatorname{tr}(A_x)$ and write $A_x=p_x\rho_x$, assigning any fixed density state when $p_x=0$; positivity makes a trace-zero block zero. The private normalization and record/marginal correspondences identify the two subentropy differences and the two guessing suprema. The first component of the consumed frozen `POVMGram.cq_conditional_subentropy_guessing` gives $Q(X\mid B)\le1-p_{\rm guess}$. Its second component gives $1-p_{\rm guess}\le-\ln p_{\rm guess}$. The public `result` states only their composite logarithmic inequality.

**Tightness, proved in prose within the perfectly distinguishable case.** Orthogonal signal supports admit a POVM with success one; total trace bounds every success score by one. Thus $p_{\rm guess}=1$. The block joint state and summed marginal have the same nonzero spectrum; the Gaussian/determinant correspondence preserves zero padding. Their subentropies agree, so both bounds are zero. No classification of all equality cases is asserted.

**Scope of source consequences.** Every finite c-q use of the source's conjectured guessing estimate now has the formal logarithmic inequality under its stated convention, and Proposition 6 is contained in this finite-family scope. This module makes no claim about infinite-dimensional states or a complete equality classification. Conjecture 1 and alternative smaller operational bounds are separate questions.

## ASSUMED-UNVERIFIED

The external literature screen recorded in #18776 reads the source and searches conditional subentropy with guessing probability/min-entropy. The additional papers listed there are attributed to the GPT Pro search seat, rather than presented as implementation-seat readings. Completeness remains `ASSUMED-UNVERIFIED`; the formal result does not certify literature novelty. Numerical solver and Monte Carlo outputs are finite computations, not proof of the uniform statement. The four-slot escape audit remains unfinished under #20025.
