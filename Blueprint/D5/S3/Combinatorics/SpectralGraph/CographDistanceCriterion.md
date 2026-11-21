# Exact cotree criteria for multiplicity equality

## Abstract

Exact cotree criteria for multiplicity equality.

**Definition 1.1 (Eligible shift).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.Eligible`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.Eligible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The real shift differs from both −1 and −2.

**Definition 1.2 (Local nullity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.kernelCount`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.kernelCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Take the real dimension of the kernel of the local operator.

**Definition 1.3 (Distance multiplicity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Take the real nullity of the ordinary distance matrix shifted by x. Real symmetry identifies geometric and algebraic multiplicity.

**Theorem 1.4 (Local width bound and saturation).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotree_kernelCount_le_and_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotree_kernelCount_le_and_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At eligible shifts and with nonzero internal coupling, nullity is bounded by vicinal width. Saturation forces a kernel vector whose coordinates sum to a nonzero value.

**Theorem 1.5 (Distance multiplicity bound).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At every eligible shift the nullity of a connected cograph is at most its width.

**Definition 1.6 (Join-root criterion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.JoinRootCriterion`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.JoinRootCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

There is a unique nonleaf child and a positive number of root leaves. The leaves are the universal vertices. The child has nullity one below its width and scalar response g with 1+g−ℓ/(x+1)=0.

**Theorem 1.7 (Equality at width above one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_joinRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_joinRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At a fixed eligible real shift equality is equivalent to the join-root criterion.

**Theorem 1.8 (Singleton equality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

A singleton attains exactly at zero.

**Theorem 1.9 (Equality at width one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_width_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_width_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At an eligible shift, equality at width one holds exactly when there is a nonzero distance eigenvector.

**Theorem 1.10 (Attainment at width one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.width_one_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.width_one_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The singleton uses zero. For a nonsingleton the native distance matrix is nonzero and symmetric with zero trace, so it has a positive eigenvalue.

**Definition 1.11 (Cotree scalar state).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At a common real shift record the nullity and either nonzero pairing on the kernel or the scalar response.

**Theorem 1.12 (Correctness of the scalar recursion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The three rank-one transitions compute the native state at every real shift under the stated label condition, including poles and coincident roots.

**Definition 1.13 (Guard data).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.CotreeGuardData`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.CotreeGuardData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Store the response numerator, a monic guard and the set of distinct descendant guards.

**Definition 1.14 (Guard recursion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The leaf guard is X+q. At a node use the product of child guards plus the coupling times the common response numerator.

**Theorem 1.15 (Degrees of uncancelled guards).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Each guard is monic of subtree-size degree. The numerator has degree one lower and leading coefficient minus the subtree size.

**Theorem 1.16 (States away from roots).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_off_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_off_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Outside all descendant guard roots the native nullity vanishes and the scalar response is the uncancelled rational ratio.

**Theorem 1.17 (Exact finite set of shifts).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_guard_candidates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_guard_candidates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

At each real x, eligible equality is equivalent to membership in the distinct guard-root set, eligibility and equality of the recursive nullity with the width. The sum of the distinct guard degrees bounds the cardinality.

**Theorem 1.18 (Classification of attaining cographs).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_attains_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_attains_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Width-one connected cographs attain. At greater width, attainment is equivalent to the join-root criterion holding at an eligible real guard root.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.CotreeGuardData`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.Eligible`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.JoinRootCriterion`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_degrees`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeGuardData_off_roots`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotreeScalarState_spec`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.cotree_kernelCount_le_and_saturation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_attains_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_joinRoot`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_singleton`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_eq_width_iff_width_one`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_guard_candidates`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.distanceMultiplicity_le`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.kernelCount`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion.width_one_attains`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree](CographDistanceCotree.md)
- Dependency: [D5/S3/QuadraticForms/SymmetricRankOneGuards](../../QuadraticForms/SymmetricRankOneGuards.md)
- Dependency: [D5/S3/QuadraticForms/SymmetricRankOneWidth](../../QuadraticForms/SymmetricRankOneWidth.md)
