# Integral decomposition and the literal lattice count

## Abstract

Clipping at one unit of binomial capacity separates an integral point into a residual point and a final chain member. Iterating gives the lattice transfer.

**Definition 1.1 (Integral f-vector coordinates).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.ZVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.ZVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use one integer coordinate for each face size from zero through n.

**Definition 1.2 (Natural vectors as integral vectors).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.intVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.intVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Cast the coordinates from the naturals to the integers.

**Definition 1.3 (Integral vectors as real vectors).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.castIntVector`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.castIntVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Cast the integer coordinates into the real ambient space of the polytope.

**Definition 1.4 (Literal lattice points in the real dilate).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

An integer vector belongs exactly when its real image lies in the scalar dilate of the convex hull of actual proper f-vectors. See Lattice/TransferEhrhart.lean, line 595.

**Theorem 1.5 (The two coordinate casts agree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.cast_intVector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.cast_intVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Casting a natural coordinate through the integers agrees with its direct real cast.

**Definition 1.6 (Natural vectors satisfying the dilation conditions).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.natDilation`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.natDilation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Require that the coordinates cast to the reals satisfy the normalized conditions at scale r.

**Theorem 1.7 (Lattice points come from the normalized natural carrier).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice_eq_image`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice_eq_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The real dilate is nonnegative. Recover a natural vector from the nonnegative integer coordinates and use the positive dilation membership test in both directions.

**Theorem 1.8 (Rank-one lattice vectors are bounded by the capacities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The first normalized coordinate equals one and antitonicity bounds every later normalized coordinate by one.

**Theorem 1.9 (Rank-one lattice vectors have the two fixed coordinates).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Cast back the normalized equalities in degrees zero and one.

**Definition 1.10 (Finite rank-one lattice carrier).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.latticeVectors`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LatticeCount.latticeVectors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Filter a finite box of coordinates bounded by their binomial capacities using the rank-one normalized conditions.

**Theorem 1.11 (Exact membership in the finite lattice carrier).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.mem_latticeVectors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.mem_latticeVectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The normalized conditions imply the box bounds, so filtering the box represents the entire natural rank-one lattice carrier.

**Theorem 1.12 (Positive skeletons lie in the lattice carrier).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.skeleton_mem_latticeVectors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.skeleton_mem_latticeVectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The skeleton is integral and is a proper f-vector, hence lies in the rank-one convex hull.

**Theorem 1.13 (The terminal rank-one lattice vector is full).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If the top coordinate is positive it reaches its unit capacity. Monotonicity of normalized coordinates forces every earlier coordinate to reach capacity too.

**Theorem 1.14 (Chained integral decomposition for every positive rank).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_chained_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_chained_exists` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

This is the equal-shift Kozlov case of Part III, Theorem 6 and Corollary 7. Clip the vector at the rank-one capacities and subtract this last member. The residual ratios are the positive parts after subtracting one, so they are antitone. A deficient coordinate of the clipped member forces the residual to vanish from that degree onward. Induct on rank and append the clipped member.

**Theorem 1.15 (The transfer formula for literal lattice points).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_count_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_count_transfer` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The natural-dilation carrier is the image of chained rank-one lattice tuples. Use the integral decomposition for surjectivity, uniqueness of bounded chained sums, and the injective coordinate cast. See Part III, Corollary 33 and Lattice/TransferEhrhart.lean, line 613.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.ZVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.castIntVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.cast_intVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.dilateLattice_eq_image`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.intVector`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.latticeVectors`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_chained_exists`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_count_transfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.lattice_terminal`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.mem_latticeVectors`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.natDilation`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_bounded`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.normalized_one_fixed`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LatticeCount.skeleton_mem_latticeVectors`
- Dependency: [D5/S3/Combinatorics/Kozlov/ConvexHull](ConvexHull.md)
