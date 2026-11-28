# Predecessor width for three-state min-plus walks

## Abstract

Affine predecessor branches and width of three-state min-plus walks.

For a fixed Alice edge, a Bob score records the minimum cost of reaching each of the three Bob states. Matrix rows index sources and columns index destinations. Normalize the scores by subtracting coordinate zero from every coordinate. Keep that coordinate in the triple because any destination can select state zero as its predecessor. The complete-Bob recurrence is the one used for Meyerovitch–Young Question 6.1. https://arxiv.org/html/2603.21449v1#S4.E6

**Theorem 1.1 (The reindexings are closed under composition).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.finite_reindex_semigroup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.finite_reindex_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a predecessor map p, write Tₚx for the triple with coordinate j equal to x(p(j)) − x(p(0)). Applying the reindexing for p first and q second yields the reindexing for p ∘ q, which traces output columns back to the original input. The intermediate normalization cancels. There are only finitely many maps from three states to three states, so the integer reindexings form a finite semigroup.

**Theorem 1.2 (The minimum ranges over actual incoming sources).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.mem_sources_ofGraph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.mem_sources_ofGraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume each destination j has an incoming Bob edge. Its source set comprises exactly the states i for which the graph has an edge from i to j. Matrix entries are supplied on these pairs, for example as minima over parallel edges. The update takes the minimum of x(i) + M(i,j) over the source set of j.

**Theorem 1.3 (Closed comparisons characterize the minimizing choices).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.closedColumnComparisons_iff_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.closedColumnComparisons_iff_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A branch selects a source p(j) in each actual column and compares its score plus cost with the candidates in that column using weak inequalities. The comparisons hold exactly when each selected source attains the column minimum. Each finite nonempty column has an attained minimum, so every input belongs to at least one branch. Ties allow more than one branch at the same input.

**Theorem 1.4 (An attained branch gives the normalized affine update).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_eq_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the branch p, subtract the attained score in column zero from the attained score in column j. The result is Tₚx at j plus the offset M(p(j),j) − M(p(0),0). If successive branches p and q use offsets d and e, their composition reindexes by p ∘ q and adds T_q(d) + e, where T_q is the reindexing for q.

**Theorem 1.5 (The complete-matrix formula at a legal walk extension).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.completeWalk_projective_eq_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.completeWalk_projective_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the complete Bob graph every source is present in every column, and the column minima agree with the canonical Q6.1 assignment update. If an Alice edge leaves the terminal vertex of a legal prefix, impose the branch comparisons at the actual scores produced by that prefix from the supplied initial vector. The affine formula then gives the normalized scores of the extended walk.

**Theorem 1.6 (The same predecessor acts on both integer coefficient triples).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the input as a + αq and the costs on actual pairs as A + αB, with integer coefficients. Evaluate the column comparisons on the combined input scores. On an attained branch, the two resulting coefficient triples are obtained by applying Tₚ to a and q and adding the respective offsets computed from A and B.

**Theorem 1.7 (Aligned coefficient lines give an affine parameter update).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_aligned`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_aligned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q = u + nv lie on an integer coefficient line with normalized base u and normalized primitive direction v. Primitivity means that the two free coordinates admit an integer Bézout combination equal to one. For a target line with base u′ and direction v′, suppose Tₚu plus the B offset equals u′ + cv′ and Tₚv = hv′ with h nonzero. At an input satisfying the branch comparisons, the target coefficient on that line has parameter hn + c.

**Theorem 1.8 (Permutations preserve width and have unit multiplier on aligned lines).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.permutation_width`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.permutation_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The width of an integer triple is its largest coordinate minus its smallest. Reindexing preserves each selected pairwise difference because the anchor cancels, so it cannot increase width. For an injective predecessor map on three states, every pair is selected somewhere and the inverse permutation recovers the normalized input. Applied to an alignment Tₚv = hv′, this inverse expresses the primitive input direction as an integer multiple with factor h. Bézout primitivity forces |h| = 1, so v and v′ have the same width.

**Theorem 1.9 (A nonzero repeated-predecessor output has a width-one direction).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_primitive_direction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_primitive_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A noninjective predecessor map selects at most two source indices. After normalization its output has levels zero and a selected difference d = v(p(r)) − v(p(0)) for some r. When the output is nonzero, it is d times the normalized zero-one indicator of the nonzero level. This indicator is primitive and has width one, and 1 ≤ |d| ≤ width(v).

**Theorem 1.10 (A noninjective aligned branch bounds the multiplier).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_aligned_width`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_aligned_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose Tₚv = hv′ for a noninjective p, a normalized primitive target direction v′, and a nonzero integer h. Cancelling h shows that v′ has at most two levels. Its nonzero level must have absolute value one by primitivity. Thus width(v′) = 1 and 1 ≤ |h| ≤ width(v), using the fact that scaling multiplies width by the absolute value of the scalar.

**Theorem 1.11 (An aligned path has at most one strict drop in width).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.alignedPath_at_most_one_drop`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.alignedPath_at_most_one_drop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a finite segment of coefficient lines with an aligned transition of nonzero multiplier between each pair of successive lines. Width stays the same or falls to one at each step. Normalized primitive directions have width at least one, so after a strict drop every later line in the segment has width one. Each transition with width-one input also has |h| = 1.

The assertion applies separately to each segment of aligned transitions in the rotation-word construction of Section 2 of q61-three-state-single-drift.txt. Constant and transverse transitions are exceptional in that construction and can occur between these segments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.alignedPath_at_most_one_drop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.closedColumnComparisons_iff_attained`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.completeWalk_projective_eq_affine`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.finite_reindex_semigroup`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.mem_sources_ofGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_aligned_width`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.noninjective_primitive_direction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.permutation_width`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_aligned`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_coefficients`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61PredecessorWidth.projectiveUpdate_eq_affine`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards](MeyerovitchYoungQ61AssignmentGuards.md)
