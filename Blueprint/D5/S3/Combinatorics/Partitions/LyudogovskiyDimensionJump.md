# A sharp bound on the local simplex dimension jump

## Abstract

The sharp absolute local simplex dimension jump across a partition transfer is two.

**Theorem 1.1 (Universal bound and a sharp family).**

$$\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall p \in \operatorname{Partition}\left(n\right),\; \forall q \in \operatorname{Partition}\left(n\right),\; \operatorname{Adj}\left(n, p, q\right) \Rightarrow \lvert \operatorname{int}\left(\operatorname{dim}\left(p\right)\right) - \operatorname{int}\left(\operatorname{dim}\left(q\right)\right) \rvert \le 2\right)\right) \land \left(\forall k \in \mathbb{N},\; 4 \le k \Rightarrow \left(\exists p \in \operatorname{Partition}\left(3 \cdot k - 1\right),\; \exists q \in \operatorname{Partition}\left(3 \cdot k - 1\right),\; \operatorname{rows}\left(p\right) = [k,k,k - 2,1] \land \left(\operatorname{rows}\left(q\right) = [k,k,k - 1] \land \left(\operatorname{Adj}\left(3 \cdot k - 1, p, q\right) \land \left(\operatorname{dim}\left(p\right) = 4 \land \operatorname{dim}\left(q\right) = 2\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Layers and Phase Boundaries in the Partition Graph*. DOI: [10.48550/arXiv.2603.29988](https://doi.org/10.48550/arXiv.2603.29988). URL: <https://arxiv.org/abs/2603.29988v1>.

*Commentary.*

Partition(n) means all integer partitions of n. Adj(n,p,q) is one nontrivial unit transfer between distinct part occurrences, with a virtual zero recipient allowed. The dimension of a vertex is the maximum clique size through it minus one. The rows function lists the lengths of its Young diagram in descending order. The subtraction in the universal bound is in the integers.

A clique of size at least two lies above a common predecessor or below a common successor. The available corners are counted by distinct positive row lengths, with one additional corner for starting a row. Across a one-cell change, at most one positive length is gained and at most one is lost. Two adjacent diagrams share a predecessor and a successor, so counting the actual cliques built on those diagrams bounds the change in either direction.

For the displayed family, the shared predecessor is (k, k, k−2). Its extensions give a clique of dimension two through the second endpoint. All deletions from that endpoint have at most two distinct positive lengths, and its successors have at most three, giving the matching upper bound. Deleting from the second row of the first endpoint leaves four distinct positive lengths. Its extensions give dimension at least four, and the universal bound gives the matching upper bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.result`
- Dependency: [D5/S3/Combinatorics/Partitions/LyudogovskiySimplex](LyudogovskiySimplex.md)
