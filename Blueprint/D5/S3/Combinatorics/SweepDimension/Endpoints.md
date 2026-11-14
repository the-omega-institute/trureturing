# Sweep dimension and its width endpoints

## Abstract

The general finite-poset sweep identity determines exactly which posets attain either width bound.

**Theorem 1.1 (The identity and both endpoint classifications).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Endpoints.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Endpoints.result` (`✓ std3`). ∎

*Resolves.* `Problems/boldi-vigna-general-sweep-endpoints` (proved) by `D5/S3/Combinatorics/SweepDimension/Endpoints.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"boldi-vigna-general-sweep-endpoints","declaration_gid":"D5/S3/Combinatorics/SweepDimension/Endpoints.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

For every finite poset with at least two points, sweep dimension is theta. It equals the maximum of two and the width exactly when the poset is a chain or an antichain. It equals twice the width exactly when there are two disjoint antichains, each of maximum cardinality. A three-chain-free set splits into its minimal and nonminimal elements, both antichains. Equality at the upper endpoint forces both pieces to have maximum size. At the lower endpoint, a proper maximum antichain can be enlarged by any outside point without creating a strict three-chain; when width is at least two this rules out equality. Width at most one is exactly the chain case.

## References

- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Endpoints.result`
- Dependency: [D5/S3/Combinatorics/SweepDimension/Upper](Upper.md)
