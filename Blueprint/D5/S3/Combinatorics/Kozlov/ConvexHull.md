# The real convex hull of proper f-vectors

## Abstract

The consecutive normalized face counts are nonincreasing. The converse hull inclusion uses their consecutive differences as weights of full skeletons.

**Theorem 1.1 (Consecutive local LYM inequality for proper downsets).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.lym`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.lym` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the local LYM bound to the lower shadow of the next layer and use downward closure to bound this shadow by the current layer. Snellman's Spine/LYM.lean, line 46, states the inequality for order ideals.

**Definition 1.2 (Real skeleton vertices).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.skel`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.skel` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Fill the layer capacity up to the cutoff and put zero above it, in real coordinates. See Spine/LYM.lean, line 76.

**Definition 1.3 (Positive skeleton vertices).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.skelSet`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.skelSet` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the skeletons with cutoffs from one through n. See Spine/LYM.lean, line 80.

**Definition 1.4 (Consecutive normalized inequalities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Fix the first two coordinates, compare adjacent ratios to the binomial capacities, and require a nonnegative last coordinate. See Spine/LYM.lean, line 85.

**Theorem 1.5 (Identify the singleton coordinate).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.fin_one_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.fin_one_eq` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The degree-one index used in the inequalities is the same index as the singleton coordinate for positive ground size. See Spine/LYM.lean, line 94.

**Theorem 1.6 (The normalized region is convex).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.convex_lymChain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.convex_lymChain` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The defining equalities and inequalities are linear. They hold under convex combinations. See Spine/LYM.lean, line 102.

**Definition 1.7 (Normalized coordinates extended by zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

At degree k through n, divide x[k] by the binomial coefficient choose(n,k). Extend the ratio by zero beyond n. See Spine/LYM.lean, line 164 and Part III, Proposition 2, equation (14).

**Theorem 1.8 (The ratio inside the coordinate window).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For k at most n, the value is x[k] divided by choose(n,k), including at k = n. See Spine/LYM.lean, line 167.

**Theorem 1.9 (The ratio beyond the coordinate window).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_gt` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For k greater than n, the extended ratio is zero. See Spine/LYM.lean, line 171.

**Theorem 1.10 (Consecutive ratio differences telescope).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.sum_mu_telescope`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.sum_mu_telescope` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Summing each ratio minus the next from degree k through n recovers the ratio at k, since the extended ratio at n+1 is zero. See Spine/LYM.lean, line 176.

**Theorem 1.11 (Normalized inequalities give a skeleton mixture).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_subset_hull`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_subset_hull` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The barycentric weight of the skeleton at cutoff k is the ratio at k minus the ratio at k+1. These weights are nonnegative and sum to one. Their skeleton combination has the same coordinates by telescoping. See Spine/LYM.lean, line 197 and Part III, Proposition 2 at scale one.

**Definition 1.12 (Real f-vector coordinates).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.RVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.RVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use one real coordinate for each face size from zero through n.

**Definition 1.13 (Realize an f-vector over the reals).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.realVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.realVector` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Cast each natural coordinate to the reals, as in the image map in Counting/Duality.lean, line 322.

**Definition 1.14 (Real realizations of proper f-vectors).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.realVectors`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.realVectors` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the image of the literal proper vector set under coordinatewise real casting. Counting/Duality.lean, line 322, identifies this image with the real carrier in Spine/Complexes.lean, line 68.

**Theorem 1.15 (The literal convex hull is the normalized region).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.hull_eq_lymChain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.hull_eq_lymChain` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Actual face vectors satisfy local LYM. Conversely the skeleton mixture expresses every point of the region using actual proper face vectors. See Spine/KozlovThm.lean, line 145.

**Theorem 1.16 (Positive real layer capacities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.cap_pos_real`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.cap_pos_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Cast the positive natural binomial capacity to the reals.

**Definition 1.17 (The normalized coordinates at a scale).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.Normalized`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ConvexHull.Normalized` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Fix the first two coordinates at their scaled capacities. Require nonnegative coordinates and monotone normalized counts.

**Theorem 1.18 (The scale bounds each normalized coordinate).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.ratio_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.ratio_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Compare each degree with degree zero by antitonicity. The degree-zero ratio equals the scale.

**Theorem 1.19 (Adjacent and all-index comparisons at scale one).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_iff_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_iff_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Consecutive comparisons imply antitonicity on the finite chain. The reverse implication restricts to adjacent indices.

**Theorem 1.20 (Test membership in the actual real dilate).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ConvexHull.mem_dilate_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ConvexHull.mem_dilate_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the hull equality and cancel the positive dilation factor in the coordinate and ratio conditions. This is the Kozlov specialization of Part III, Proposition 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.Normalized`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.RVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.cap_pos_real`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.convex_lymChain`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.fin_one_eq`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.hull_eq_lymChain`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.lym`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_iff_normalized`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.lymChain_subset_hull`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.mem_dilate_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_gt`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.muOf_of_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.ratio_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.realVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.realVectors`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.skel`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.skelSet`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ConvexHull.sum_mu_telescope`
- Dependency: [D5/S3/Combinatorics/Kozlov/ChainedCount](ChainedCount.md)
