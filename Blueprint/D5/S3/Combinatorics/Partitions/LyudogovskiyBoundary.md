# Boundary thresholds in the integer-partition graph

## Abstract

The first transfer boundary between consecutive exact local clique layers.

**Theorem 1.1 (The first boundary occurs at the threshold of the higher layer).**

$$\forall r \in Nat,\; 1 \le r \Rightarrow \operatorname{IsLeast}\left(\{n:Nat\mid0 < n \land \left(\exists p \in \operatorname{Partition}\left(n\right),\; \exists q \in \operatorname{Partition}\left(n\right),\; \operatorname{Adj}\left(\operatorname{graph}\left(n\right), p, q\right) \land \left(\operatorname{localDimension}\left(p\right) = r \land \operatorname{localDimension}\left(q\right) = r + 1\right)\right)\}, \operatorname{triangular}\left(r + 1\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result` (`✓ std3`). ∎

*Resolves.* `Problems/lyudogovskiy-2026-boundary-threshold` (proved) by `D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lyudogovskiy-2026-boundary-threshold","declaration_gid":"D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. DOI: [10.48550/arXiv.2603.23228](https://doi.org/10.48550/arXiv.2603.23228). URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

Problem 6.3 in the source asks when consecutive exact layers first share a transfer edge. Adj(graph(n), p, q) is literal unit-transfer adjacency between native partitions of n. IsLeast includes attainment and comparison with every positive admissible size. The higher-layer threshold formula identifies the displayed size with the threshold of layer r+1.

Delete the last singleton from the top-row extension of the staircase of rank r+1. The common diagram has r+1 selected addable corners. Their insertions give a clique of size r+1. One endpoint is a first-occurrence partition in layer r+1. The other lacks a required staircase cell, and the clique lower bound and the maximum upper bound give dimension exactly r.

For r=0 the set is empty. Each edge forms a clique of size two, so both endpoints have local dimension at least one. The source defines its boundary threshold only when the defining set is nonempty.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result`
- Dependency: [D5/S3/Combinatorics/Partitions/LyudogovskiySimplex](LyudogovskiySimplex.md)
