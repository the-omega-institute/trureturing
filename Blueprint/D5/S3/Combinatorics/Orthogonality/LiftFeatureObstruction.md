# The original full lift-feature obstruction

## Abstract

The original full lift-feature obstruction.

**Definition 1.1 (The whole original projection plane).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.J`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.J` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The exact projection plane consists of all three-coordinate vectors with last coordinate zero.

**Definition 1.2 (The entire first lift).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fu`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fu` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full linear lift sends p to (p1,p0+p1,0); on the source projection basis1,4 its T-coordinate values are12,15.

**Definition 1.3 (The entire second lift).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fw`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fw` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full linear lift sends p to (p0+p1,p0,0); its source-basis values are15,3.

**Definition 1.4 (The actual first quotient map).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.f`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.f` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full placement map has quotient codomain T/K with K zero. The quotient is not replaced by a scalar.

**Definition 1.5 (The actual second quotient map).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.g`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.g` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The entire second original quotient placement map has the same complete domain and quotient codomain.

**Theorem 1.6 (Both entire kernels are zero).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.kernels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.kernels` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Both complete quotient maps are injective.

**Theorem 1.7 (Both entire images agree).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranges` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Each complete image is exactly the image of the full two-dimensional coordinate plane under the canonical quotient map. In original T coordinates this is the span of masks3,12.

**Theorem 1.8 (Both full maps have rank two).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranks` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The actual image submodules have dimension two, using full injectivity and the complete domain equivalence.

**Definition 1.9 (The first full actual plane).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.U`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.U` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Represent the entire source plane from its exact K/P and quotient-valued placement.

**Definition 1.10 (The second full actual plane).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.W`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.W` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Represent the entire second source plane from its exact K/P and placement.

**Theorem 1.11 (Exact original source spans).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.source_planes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.source_planes` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The represented full submodules are exactly span(13,6) and span(9,14), in the original six binary coordinates.

**Theorem 1.12 (The original planes are adjacent).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.planes_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.planes_adjacent` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full reconstructed submodules are distinct and all pairs of their vectors have zero cross pairing. The proof consumes the complete X/Y/Z criterion.

**Definition 1.13 (The actual original shear).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shearElement`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shearElement` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The simultaneous coordinate swaps0/1 and2/3 are exactly the original T/S shear diag(1,1,0). It preserves the full bilinear form and fixes T pointwise, so belongs to the entire orthogonal stabilizer.

**Theorem 1.14 (The original plane orbit).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.plane_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.plane_orbit` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The full mapped-submodule action carries span(13,6) exactly to span(9,14), through the original generator images13 to14 and6 to9.

**Theorem 1.15 (Every clique label is fixed).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shear_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shear_labels` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The actual shear fixes every full nonzero subspace of T, hence the entire original clique-label domain.

**Definition 1.16 (The full lift-feature rule).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.featureClaim`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.featureClaim` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The proposed proper coloring quantifies every actual nonzero six-coordinate Submodule and every entire K/P/placement fiber, with equal actual rank, image and kernel. It includes every degenerate fiber producing a nonzero vertex.

**Definition 1.17 (The original feature and full-group rules).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.claim`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.claim` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The prohibited claim combines the full lift-feature rule with both entire-stabilizer coloring rules. The actual original plane orbit refutes all three branches.

**Theorem 1.18 (Refute the full lift-feature and full-group rules).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The original planes have equal entire K/P, rank, image and kernel but are adjacent. No proper coloring can depend solely on those data. Their actual label-fixing shear orbit also refutes full-stabilizer equivariance and arbitrary-label invariance. The full placement maps still reconstruct every vertex; a structural fifteen-color assignment remains open. Finite witness-profile statistics and the written n7 bounds are separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.J`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.U`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.W`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.claim`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.f`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.featureClaim`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fu`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.fw`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.g`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.kernels`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.plane_orbit`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.planes_adjacent`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranges`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.ranks`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.result`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shearElement`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.shear_labels`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.source_planes`
- Dependency: [D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction](OrthogonalitySymmetryObstruction.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/SixDimensionalProfiles](SixDimensionalProfiles.md)
