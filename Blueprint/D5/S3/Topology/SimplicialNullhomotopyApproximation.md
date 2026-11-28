# Fixed-target simplicial approximation of a nullhomotopy

## Abstract

Fixed-target simplicial approximation of a nullhomotopy

**Theorem 1.1 (Contiguity contractions from nullhomotopies of simplicial maps).**

Lean statement: `D5/S3/Topology/SimplicialNullhomotopyApproximation.realized_simplicial_map_contracts`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SimplicialNullhomotopyApproximation.realized_simplicial_map_contracts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A nullhomotopy of a simplicial map between finite realizations gives a single subdivision threshold of the source. At every depth past that threshold, selecting one original vertex from each refined vertex's carrier gives a composite map joined to a constant by finitely many contiguous simplicial maps in the fixed target. The proof tracks the original support under iterated barycentric averaging and uses one Lebesgue radius on the homotopy cylinder.

## References

- Truth anchor: `D5/S3/Topology/SimplicialNullhomotopyApproximation.realized_simplicial_map_contracts`
- Dependency: [D5/S3/Topology/GeometricGraphTermination](GeometricGraphTermination.md)
- Dependency: [D5/S3/Topology/StableCategory/LebesgueStarAssignment](StableCategory/LebesgueStarAssignment.md)
