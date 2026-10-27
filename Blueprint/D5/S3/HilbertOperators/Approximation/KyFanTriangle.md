# Approximation-number Ky Fan triangle

## Abstract

Finite approximation-number prefixes obey the triangle inequality on arbitrary complex Hilbert spaces.

The approximation number at index n is the infimum of operator-norm errors over actual bounded operators of rank at most n. The source and target Hilbert spaces may have independent universes and unequal dimensions. Every prefix length is a natural number, including zero and lengths above either finite dimension. Compactness, separability and nonzero spaces are not assumptions.

**Theorem 1.1 (lower_bound_of_lt_rank).**

Lean statement: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.lower_bound_of_lt_rank`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.lower_bound_of_lt_rank` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

A subspace of rank greater than n forces every rank-at-most-n approximant to have a nonzero kernel vector in that subspace. A homogeneous lower modulus on the subspace therefore bounds the approximation number from below.

**Theorem 1.2 (singular_value_le_approximation_number).**

Lean statement: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.singular_value_le_approximation_number`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.singular_value_le_approximation_number` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

In finite dimensions the first n plus one right singular directions give the lower spectral bound, by the rank obstruction.

**Theorem 1.3 (approximation_number_le_singular_value).**

Lean statement: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_le_singular_value`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_le_singular_value` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

Projection onto the first n right singular directions gives an actual rank-at-most-n approximant. The ordered Gram eigenvalues bound its complementary error. When n exceeds the source dimension the original operator itself is admissible.

**Theorem 1.4 (approximation_number_eq_singular_value).**

Lean statement: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_eq_singular_value`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_eq_singular_value` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

The two spectral inequalities identify approximation numbers with Mathlib singular values, including zero padding and independent universes.

**Definition 1.5 (Finite approximation-number prefix).**

$$\forall u \in \mathrm{UniverseLevel}\left(\right),\; \forall v \in \mathrm{UniverseLevel}\left(\right),\; \forall E \in \mathrm{Type}\left(u\right),\; \forall F \in \mathrm{Type}\left(v\right),\; [\mathrm{NormedAddCommGroup}\left(E\right)] [\mathrm{InnerProductSpace}\left(\mathrm{Complex}, E\right)] [\mathrm{NormedAddCommGroup}\left(F\right)] [\mathrm{InnerProductSpace}\left(\mathrm{Complex}, F\right)] \forall T \in E \to_{L}[\mathrm{Complex}] F,\; \forall k \in \mathrm{Nat},\; \mathrm{kyFanGauge}\left(T, k\right) = \sum_{n \in \mathrm{range}\left(k\right)} \mathrm{approximationNumber}\left(T, n\right)$$

*Formalization.* `D5/S3/HilbertOperators/Approximation/KyFanTriangle.ky_fan_gauge` (`✓ std3`).

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

The displayed kyFanGauge denotes the native ky_fan_gauge, approximationNumber denotes MinMaxLowerBound.approximation_number, and range denotes Finset.range. The definition is a finite prefix sum of that single native approximation_number. It requires complex inner-product structures but neither completeness instance.

**Theorem 1.6 (exists_finite_restriction_add_gt).**

Lean statement: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.exists_finite_restriction_add_gt`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.exists_finite_restriction_add_gt` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

Every strictly positive tolerance admits a restriction to the span of n plus one actual vectors whose approximation number approaches the ambient one. Completeness of both spaces supplies the strict-threshold min-max input; the zero and small-value cases remain included.

**Theorem 1.7 (ky_fan_gauge_add_le).**

$$\forall u \in \mathrm{UniverseLevel}\left(\right),\; \forall v \in \mathrm{UniverseLevel}\left(\right),\; \forall E \in \mathrm{Type}\left(u\right),\; \forall F \in \mathrm{Type}\left(v\right),\; [\mathrm{NormedAddCommGroup}\left(E\right)] [\mathrm{InnerProductSpace}\left(\mathrm{Complex}, E\right)] [\mathrm{NormedAddCommGroup}\left(F\right)] [\mathrm{InnerProductSpace}\left(\mathrm{Complex}, F\right)] [\mathrm{CompleteSpace}\left(E\right)] [\mathrm{CompleteSpace}\left(F\right)] \forall S \in E \to_{L}[\mathrm{Complex}] F,\; \forall T \in E \to_{L}[\mathrm{Complex}] F,\; \forall k \in \mathrm{Nat},\; \mathrm{kyFanGauge}\left(S + T, k\right) \le \mathrm{kyFanGauge}\left(S, k\right) + \mathrm{kyFanGauge}\left(T, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/KyFanTriangle.ky_fan_gauge_add_le` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5 (2026). *Approximation-number min-max and finite Ky Fan triangle inequalities*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber>.

*Commentary.*

The finite spectral theorem and an attaining orthonormal pair give the rectangular finite-dimensional triangle inequality. Isometric coordinate transport permits independent universes. Compression to the joint range handles an arbitrary target for a finite source. For each positive tolerance, the finitely many near-optimal source restrictions for the prefix are placed in one common finite span. Summing their errors and letting the tolerance decrease proves the stated inequality. Both completeness instances are retained.

These classical results adapt AIQ-Kitware/aiq-dkps-formalization revision 8924c4cc743d2f193bb4f39bee800790698a681b under Apache-2.0. Existing finite rectangular and spectral proofs retain their separate attribution chains. No infinite-prefix, compact-spectrum, Hilbert-Schmidt energy, Shirokov-cost or convex-roof identity follows solely from this statement.

## References

- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_eq_singular_value`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.approximation_number_le_singular_value`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.exists_finite_restriction_add_gt`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.ky_fan_gauge`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.ky_fan_gauge_add_le`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.lower_bound_of_lt_rank`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/KyFanTriangle.singular_value_le_approximation_number`
- Dependency: [D5/S3/HilbertOperators/Approximation/MinMaxLowerBound](MinMaxLowerBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/Rectangular/FiniteSectorRectangularAttainment](../../Quantum/Entanglement/Rectangular/FiniteSectorRectangularAttainment.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
