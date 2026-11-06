# Maximum cuts of uniform independent blow-ups

## Abstract

For every finite simple graph and every positive integer block size, independent uniform blow-ups multiply the ordinary maximum cut by the square of block size.

**Definition 1.1 (Independent uniform blow-up).**

Lean statement: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.blowup`

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.blowup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let n and s be natural numbers and H a simple graph on Fin n. The vertices of blowup H s are Fin(n*s), encoded by finProdFinEquiv from Fin n times Fin s. Two vertices are adjacent exactly when their first coordinates are adjacent in H. Each fibre is independent; each base edge induces the complete bipartite graph between its two fibres. All edges have weight one.

**Definition 1.2 (Lift a cut to whole blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.liftCut`

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.liftCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite subset T of Fin n, liftCut s T contains exactly the encoded pairs whose first coordinate belongs to T. The second coordinate ranges over the entire block. No choice of a representative is required.

**Theorem 1.3 (Every cut admits a dominating block cut).**

Lean statement: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.exists_block_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.exists_block_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,s, every simple graph H on Fin n with decidable adjacency, every s at least one, and every finite subset S of Fin(n*s), there is a finite subset T of Fin n such that the number of unordered edges of blowup H s crossing S is at most the number crossing liftCut s T. No connectedness, nonempty carrier or nonempty edge set is assumed. An unordered edge crosses a cut when exactly one endpoint belongs to the chosen side.

Let x_i count the selected vertices in block i. The cut size equals the sum, over ordered adjacent base vertices i,j, of x_i times (s minus x_j). This counts each crossing edge once, from its selected endpoint to its unselected endpoint. It equals the usual sum over unordered base edges of the two opposite crossing contributions. The existing CutBoundRefutation.cut_card_eq_sum supplies the oriented-to-unordered counting identity.

The score is affine in each individual occupancy because H has no loops. Multiplying the score by s expresses it as (s minus x_i) times the score with coordinate i set to zero plus x_i times the score with that coordinate set to s. Both coefficients are nonnegative, so at least one endpoint has score no smaller than the current score. Induction over the finite coordinate set selects such endpoints while preserving coordinates already rounded. The final endpoint vector defines T; its block lift has exactly that score.

**Theorem 1.4 (Exact maximum-cut scaling).**

Lean statement: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.maxCut_blowup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.maxCut_blowup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n,s and H as above, if s is at least one, CutBoundRefutation.maxCut (blowup H s) equals s squared times CutBoundRefutation.maxCut H. The same existing maximum-cut definition is used on both graphs: the supremum of the cardinality of the filtered unordered edge set over all finite vertex subsets. Empty carriers and edgeless graphs therefore give zero on both sides.

A lifted base cut has exactly s squared times as many crossing edges, since every crossing base edge contributes all s squared pairs of fibre vertices. The dominating-block-cut construction bounds every blow-up cut by s squared times a base cut. Conversely, a maximum base cut exists because the set of base cuts is finite, and its lift attains this bound. This establishes the exact identity without a factor of two and without any token-state or spectral hypothesis.

This result supplies the general maximum-cut calculation used in the density-limit argument of the repository blow-up theory. It does not by itself establish the energy limit, the matching estimate, the eventual sign conclusions, or the full-state defect certificate. It is a repository derivation of a classical coordinate-rounding argument; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.blowup`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.exists_block_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.liftCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut.maxCut_blowup`
- Dependency: [D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation](CutBoundRefutation.md)
