# Full actual submodules and source criteria

## Abstract

Complete kernel/projection/placement geometry of the received orthogonality result.

**Definition 1.1 (The original fixed coordinate splitting).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The explicit linear equivalence sends the first summand to span(3,12,48) and the second to span(1,4,16).

**Theorem 1.2 (The exact source pairing).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates_dot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates_dot` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

In these coordinates the actual standard pairing is t dot s-prime + s dot t-prime + s dot s-prime over F2.

**Definition 1.3 (The specified isotropic space).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

This is the actual image of the first coordinate summand.

**Definition 1.4 (The specified complement).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

This is the actual image of the second coordinate summand.

**Theorem 1.5 (The original T masks).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T_source` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Prove the actual equality T=span(3,12,48), rather than selecting an unrelated isotropic space.

**Theorem 1.6 (The original S masks).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S_source` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Prove the actual equality S=span(1,4,16), with the same bit ordering as the supplied catalogue.

**Definition 1.7 (The actual inverse coordinate submodule).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.split`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.split` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Pull back the entire original U along the fixed linear equivalence; no vectors or subspaces are discarded.

**Definition 1.8 (The complete original intersection coordinates).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

K is the first-kernel coordinate submodule and maps exactly onto U intersect T.

**Definition 1.9 (The complete original projection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.P`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.P` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

P is the entire second-coordinate image, with its original domain retained.

**Definition 1.10 (The complete original annihilator).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The perfect T/S pairing identifies H with the full P annihilator and with U-perp intersect T.

**Theorem 1.11 (The complete dimension profile).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.dimension_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.dimension_profile` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The actual dimension is dim(K)+dim(P). Thus the full source dimension/K/H profile is recovered from the exact K/P pair.

**Theorem 1.12 (Actual K equals U intersect T).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K_source` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The exact first-kernel coordinates map onto the actual intersection U intersect T.

**Theorem 1.13 (Actual H equals U-perp intersect T).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H_source` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full projection annihilator maps onto the actual orthogonal intersection, for every coordinate submodule.

**Theorem 1.14 (Recover the full projection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_recovered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_recovered` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The perfect first-second pairing recovers P from its annihilator H, without losing placement information.

**Theorem 1.15 (Equivalent exact profile data).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Equality of the actual K/P pair is equivalent to equality of the full dimension/K/H profile. This is a profile equivalence and supplies no coloring rule.

**Definition 1.16 (Actual submodule from full data).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.represented`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.represented` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Map the complete quotient-lift submodule through the fixed coordinate equivalence.

**Theorem 1.17 (Every actual submodule is reconstructed).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.reconstruction` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

All actual six-coordinate Submodules, including zero and the whole space, have unique full quotient placement data.

**Theorem 1.18 (The actual X/Y/Z test).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.orthogonal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.orthogonal_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every full pair of lift data, standard-coordinate orthogonality is equivalent to vanishing of both cross terms and the entire placement pairing. The representative lifts are arbitrary; no successful profile-only coloring rule is supplied.

**Theorem 1.19 (Exact number of full placements).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_card` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The entire actual K/P fiber has cardinality 2^(dim(P)*(3-dim(K))). Degenerate fibers remain included. The supplied 240/139 profile statistics are separate finite-certificate obligations.

**Theorem 1.20 (The actual intersection with S).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.complement_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.complement_kernel` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The pullback of every fully represented U along the original S embedding is exactly the subtype image of ker(f). This retains the actual projection domain and full quotient map.

**Theorem 1.21 (The complete annihilator dimension).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.annihilator_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.annihilator_dimension` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full perfect pairing proves dim(H)=3-dim(P).

**Theorem 1.22 (Detect the complete fixed clique domain).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_eq_bot_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_eq_bot_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The actual full projection is zero exactly when U is contained in the original T.

**Theorem 1.23 (Exhaustive nonclique annihilator dimensions).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.nonclique_annihilator_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.nonclique_annihilator_dimension` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every actual submodule outside T has annihilator dimension at most two; this is derived from the full object and is not a restricted input domain.

**Theorem 1.24 (All fifteen original labels).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_card` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The Gaussian count gives fifteen actual nonzero subspaces of the original three-dimensional T coordinate domain.

**Theorem 1.25 (Every allowed label is counted).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_card` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The complete allowed label set has cardinality 15-N(dim(H)). The already proved general contained-subspace count is reused directly.

**Theorem 1.26 (The exact source list sizes).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_sizes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_sizes` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

At annihilator dimensions zero, one and two the list sizes are respectively fifteen, fourteen and eleven. All nonclique vertices have one of these dimensions.

**Definition 1.27 (Actual fixed-clique label vertices).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.labelVertex`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.labelVertex` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every nonzero subspace of the original T is an actual nonzero Submodule vertex; labels are not scalar color proxies.

**Theorem 1.28 (Exact label availability).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_orthogonal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_orthogonal_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

A label is orthogonal to the entire U exactly when it lies inside H. Thus the allowed labels are precisely the nonzero T-subspaces not contained in the full-projection annihilator.

**Theorem 1.29 (The complete normalized-label equivalence).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.precolor_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.precolor_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every assignment of the fifteen nonzero fixed-T subspaces, normalized on all clique vertices, proper coloring is equivalent to label availability and nonorthogonality of every distinct same-label nonclique pair. The preceding full X/Y/Z theorem supplies the coordinate test. This is a criterion for a candidate, not a new structural construction. The exact n7 values and paused case-exclusion work remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.H_source`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.K_source`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.P`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.S_source`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.T_source`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.allowed_label_sizes`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.annihilator_dimension`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.complement_kernel`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.coordinates_dot`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.dimension_profile`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.labelVertex`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.label_orthogonal_iff`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.nonclique_annihilator_dimension`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.orthogonal_iff`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.precolor_criterion`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.profile_iff`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_eq_bot_iff`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.projection_recovered`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.represented`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry.split`
- Dependency: [D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount](GaussianSubspaceCount.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion](OrthogonalityDegreeDeletion.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge](SixBitSubmoduleBridge.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift](SplitSubmoduleLift.md)
