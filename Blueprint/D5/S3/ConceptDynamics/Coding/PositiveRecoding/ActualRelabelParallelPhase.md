# Parallel-edge discrepancy on the original primitive path basis

## Abstract

Parallel-edge discrepancy on the original primitive path basis.

timed packages the actual history homeomorphism and integer-time equivariance. For r and s with the same vertex equivalence, discrepancy acts on the target graph by r.edge after s.edge.symm and fixes vertices. discrepancy_factor verifies that timed s followed by this discrepancy equals timed r on actual paths.

For all n,m and every nonzero d divisible by three, timed_three_zero reuses parallel_edge_offset_sum_three_zero on the original numbered paths and canonical primitive basis. same_vertex_residue then uses additivity to compare the two reduced gyrations. This asserts vanishing of the total reduced discrepancy, not vanishing of every edge phase, and does not assume nonempty edge or orbit fibers.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (timed).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Package the coordinatewise graph-relabel homeomorphism with its integer-time law. Its periodic transport uses the existing canonical primitive paths.

**Definition 1.2 (discrepancy).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine discrepancy is on B, with edge permutation r after s^{-1}. Its two endpoint identities follow from the SAME actual vertex bijection.

**Remark 1.3 (timed_three_zero).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed_three_zero`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed_three_zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuse the owning vanishing proof on the same coordinatewise action and canonical primitive basis, without exporting its private implementation types.

**Remark 1.4 (discrepancy_factor).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy_factor`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy_factor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Following s by the target discrepancy gives r on every path when their vertex maps agree. Additivity then isolates the discrepancy contribution to gyration.

**Remark 1.5 (same_vertex_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.same_vertex_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.same_vertex_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Arbitrary parallel edges may change phase; their TOTAL reduced phase vanishes by the original T proof. No zero phase rule for r is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy_factor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.same_vertex_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed_three_zero`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree](../CountedPositiveTriangleModThree.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport](CountedRelativeGyrationTransport.md)
