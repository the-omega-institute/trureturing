# Upper-shadow counts and the block exchange

## Abstract

The recursive upper-shadow count for lexicographic segments satisfies two complementary inequalities. Together they control moving mass into an earlier component.

**Definition 1.1 (Recursive upper-shadow size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Split the lex segment by the smallest element. The first block contains that element and the second block avoids it.

**Lemma 1.2 (The empty segment has empty shadow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The recursion preserves zero mass.

**Lemma 1.3 (The shadow of the empty face).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_n0_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_n0_one` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The unique zero-element face has n one-element extensions.

**Lemma 1.4 (The shadow of a full layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_full` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For a full layer the recursion gives the capacity of the next degree.

**Lemma 1.5 (The first block recursion).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R1`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R1` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A segment fitting in the block containing the smallest element has the same shadow size as the corresponding segment on the remaining ground set in one lower degree.

**Lemma 1.6 (The second block recursion).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

After the first block fills, its shadow contributes a full layer and the remaining mass is handled in the second block.

**Lemma 1.7 (The one-face shadow increment).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_incr`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_incr` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Adding one face of size k can add at most n-k upper-shadow faces, as shown by the block recursion.

**Lemma 1.8 (The recursion at a specified overflow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2_at_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2_at_sum` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Write the segment size as the capacity of the first block plus its overflow and use the second block formula.

**Definition 1.9 (Exchange below capacity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PP`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexShadowSize.PP` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The shadow cost of placing both masses in the earlier degree is bounded by their separate costs when they fit.

**Definition 1.10 (Exchange at capacity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.QQ`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexShadowSize.QQ` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The cost of a full earlier block and the remaining mass is bounded by the original cost when the earlier block fills.

**Lemma 1.11 (Both exchanges on the empty ground set).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The capacities are zero or one and the upper-shadow sizes vanish.

**Lemma 1.12 (Exchange with a zero-degree second block).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_succ_second_degree_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_succ_second_degree_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The second mass is at most one. The one-face increment handles moving that mass.

**Theorem 1.13 (The two block exchange inequalities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_all`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_all` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Induct on the ground-set size and split each component at the capacity of the block containing the smallest element. The lower and upper overflow inequalities close the subproblems together.

**Theorem 1.14 (Below-capacity exchange in numerical form).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_P`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_P` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Specialize the first block exchange to the sum of the two input masses.

**Theorem 1.15 (Exchange with overflow in numerical form).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_Q` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Specialize the second block exchange to the sum in excess of the first capacity.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PP`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_all`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_succ_second_degree_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.PQ_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.QQ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_P`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_Q`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R1`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_R2_at_sum`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_full`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_incr`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_n0_one`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexShadowSize.sig_zero`
