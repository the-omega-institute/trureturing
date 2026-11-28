# The nonclique edge bound

## Abstract

Appendix A gives an edge threshold for deletion-resilient graphs without a large clique.

**Theorem 1.1 (The nonclique edge bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound.nonclique_edge_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound.nonclique_edge_bound` (`✓ std3`). ∎

*Citation.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

Let t ≥ 1 and w > t + 3. Suppose a finite graph has at least w + t vertices, minimum degree at least w − 1, and no clique of order w + t. If deletion of any t vertices leaves a w-clique, its number of edges is at least B(w,t), the sum of the two binomial coefficients choosing 2 from w + floor((t − 1)/2) and from w + floor(t/2). The critical-cover bound for the complement forces at least 2w + t − 1 vertices. The colorable induced subgraph estimate bounds the reciprocal-degree sum. Cauchy–Schwarz and the degree sum then give an edge bound increasing from order 2w + t − 1, where it rounds up to B(w,t).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound.nonclique_edge_bound`
- Dependency: [D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph](ColorableInducedSubgraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover](CriticalVertexCover.md)
