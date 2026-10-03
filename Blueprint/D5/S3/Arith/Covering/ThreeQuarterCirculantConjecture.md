# The Three-Quarter Circulant Construction

## Abstract

The specified lattice and three-sector distance work for every positive k; the two steps give degree two from k equal to two onward.

**Definition 1.1 (The source's three sectors).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.SectorReach`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.SectorReach` (`✓ std3`).

*Citation.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

A residue is reached within radius r exactly when nonnegative m,n with m+n at most r represent it by m*a+n*b, -m*a+n*b, or m*a-n*b. The three alternatives may overlap.

**Definition 1.2 (The proposed order).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.order`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.order` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For positive k, (k-1)(k+4)+(k+2) is the source order k squared plus four k minus two.

**Definition 1.3 (The second step).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.stepB`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.stepB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

The second residue is the negative of k+4, written -(k+4), in ZMod of the proposed order.

**Definition 1.4 (The proposed sector relation).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

This specializes the source's three-sector reachability to a=1 and b=-(k+4).

**Definition 1.5 (First source lattice column).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeFirst`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeFirst` (`✓ std3`).

*Citation.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

The integer vector is (k+2,1-k).

**Definition 1.6 (Second source lattice column).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeSecond`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeSecond` (`✓ std3`).

*Citation.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

The integer vector is (2,k).

**Definition 1.7 (The step congruence kernel).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.integerKernel`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.integerKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

This is the kernel of (x,y) mapped to x-(k+4)y modulo the proposed order.

**Definition 1.8 (The displayed integer lattice).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generatedLattice`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generatedLattice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

The set contains every integral linear combination of the two source columns.

**Theorem 1.9 (Exact lattice and determinant).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.kernel_eq_generated`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.kernel_eq_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For every k at least one, the order equals k squared plus four k minus two, the determinant of the displayed columns equals that order, and their integer span is exactly the congruence kernel. The proof gives explicit integer coefficients for every kernel point.

**Theorem 1.10 (Radius-k coverage).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For every k at least one and every residue, a quotient and remainder by k+4 select a witness in one of the source's three sectors with m+n at most k.

**Theorem 1.11 (The exact-radius witness).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_radius_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_radius_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For every k at least one, the residue k has no representation in the three source sectors with m+n at most k-1.

**Theorem 1.12 (Nondegenerate generator pair).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generator_regular_for_k_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generator_regular_for_k_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For every k at least two, both step residues are nonzero and distinct; the set of outgoing neighbors from each vertex has cardinality two.

## References

- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.SectorReach`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generatedLattice`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.generator_regular_for_k_ge_two`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.integerKernel`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.kernel_eq_generated`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeFirst`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.latticeSecond`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.order`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_cover`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.sector_radius_lower`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture.stepB`
