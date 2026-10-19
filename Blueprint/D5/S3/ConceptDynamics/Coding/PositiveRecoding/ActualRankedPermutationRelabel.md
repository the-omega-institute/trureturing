# Ranked permutation factors as actual graph relabelings

## Abstract

Ranked permutation factors as actual graph relabelings.

Construct the permutation factor P from e : Fin n ≃ Fin m and take arbitrary nonnegative q : CountMat m n. The distinguished P half-edge has number zero and is unique. rankedForward joins the old Q half-edge to the P edge at the old target; rankedInverse recovers the preceding P half-edge. The inverse equations use the existing ranked split/join operations, rather than just cardinalities. Their endpoint laws produce rankedRelabel, and ranked_coordinate identifies its action with elementaryHomeomorph on every integer coordinate.

P_mul_Q and Q_mul_P specialize Q e A to recover A and its vertex reindexing. ranked_residue additionally retains hA : P e * q = A, hB : q * P e = B and hv : r.vertex = e; it compares reduced gyration only for d with NeZero d and hd : 3 ∣ d. It does not assert that a graph relabeling has zero integral or unreduced phase. Finite dimensions, including zero, and empty q fibers remain in scope.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (rankedRelabel).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedRelabel`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual ranked elementary recoding is a graph relabel in this case. Both inverses have just been proved using split/join, not cardinality.

**Theorem 1.2 (ranked_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every integer coordinate, the ranked elementary homeomorphism agrees with the edge map of rankedRelabel. This identifies the path action, including the original parallel-edge numbers.

**Theorem 1.3 (ranked_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_residue`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero periods divisible by three, the factor equations for P and q and the prescribed vertex bijection compare the actual relabel gyration with the ranked elementary gyration after reduction to ZMod 3.

**Remark 1.4 (P).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The permutation matrix records one numbered edge from each vertex to its image under e. It is the forward factor in the ranked relabel construction.

**Remark 1.5 (Q).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reindex the rows of A by the inverse vertex bijection. This supplies the complementary nonnegative factor without changing edge multiplicities.

**Remark 1.6 (P_mul_Q).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P_mul_Q`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P_mul_Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplying the permutation factor by its complementary factor recovers A. This is the old-graph endpoint of the elementary recoding.

**Remark 1.7 (Q_mul_P).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q_mul_P`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q_mul_P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reverse product is A reindexed in both vertex coordinates. This identifies the new graph of the same elementary recoding.

**Remark 1.8 (pEdge).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.pEdge`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.pEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished P edge at i exists without any Q-edge existence assumption. In dimension zero this is a function out of the empty type.

**Remark 1.9 (p_target).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_target`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every permutation edge ends at the image of its source. The endpoint constraint is used when joining the two ranked half-edges.

**Remark 1.10 (p_unique).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_unique`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_unique` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge from a given source in the permutation factor is unique, including its number. This lets the inverse construction recover the original edge.

**Remark 1.11 (rankedForward).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedForward`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedForward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shift the actual Q half-edge left and append the unique P edge at the OLD target. This defines an edge map, before any path is considered.

**Remark 1.12 (rankedInverse).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedInverse`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split the target edge, retain its Q half, and insert the unique P half at the recovered old source. This reverses rankedForward using the original split/join operations.

**Remark 1.13 (ranked_left).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_left`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_left` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Splitting after the forward join recovers the original two halves. Uniqueness of the permutation half proves the left inverse on actual numbered edges.

**Remark 1.14 (ranked_right).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_right`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_right` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary split/join cancellation proves the right inverse on every target edge, with no nonempty-fiber premise.

**Remark 1.15 (ranked_timed).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_timed`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_timed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate identity identifies the two time-equivariant path equivalences. Their equality transfers the existing elementary gyration formula to the ranked relabel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.P_mul_Q`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.Q_mul_P`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.pEdge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_target`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.p_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedForward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedInverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.rankedRelabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_left`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_right`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel.ranked_timed`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase](ActualRelabelParallelPhase.md)
