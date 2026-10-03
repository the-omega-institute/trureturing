# Božović Conjecture 12: limited domination in Sierpiński graphs

## Abstract

The k-limited domination number of the Sierpiński graph S(n,m) is proved exactly for n ≥ 1, 2 ≤ m, and 1 ≤ k ≤ m − 1.

**Definition 1.1 (Sierpiński adjacency).**

$$\forall r \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall u \in \operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right),\; \forall v \in \operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right),\; (\operatorname{sierAdj}\left(r, m, u, v\right)) \Leftrightarrow (\exists h \in \operatorname{Fin}\left(r + 1\right),\; (\forall t \in \operatorname{Fin}\left(r + 1\right),\; (t < h) \Rightarrow (u\left(t\right) = v\left(t\right))) \land ((u\left(h\right) \ne v\left(h\right)) \land (\forall t \in \operatorname{Fin}\left(r + 1\right),\; (h < t) \Rightarrow ((u\left(t\right) = v\left(h\right)) \land (v\left(t\right) = u\left(h\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.sierAdj` (`✓ std3`).

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

For words u and v, adjacency is witnessed by an index h: the coordinates before h agree, the h-coordinates differ, and every later coordinate of each word is the other's h-coordinate. This is the adjacency rule of Section 2.

**Definition 1.2 (Sierpiński graph).**

$$\forall r \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall u \in \operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right),\; \forall v \in \operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right),\; (\operatorname{Adj}\left(\operatorname{sierGraph}\left(r, m\right), u, v\right)) \Leftrightarrow (\operatorname{sierAdj}\left(r, m, u, v\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.sierGraph` (`✓ std3`).

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

sierGraph r m is the loopless undirected SimpleGraph on functions from Fin (r + 1) to Fin m whose adjacency relation is sierAdj r m.

**Definition 1.3 (k-limited dominating set).**

$$\forall r \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall D \in \operatorname{Finset}\left(\operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right)\right),\; (\operatorname{isKLimited}\left(r, m, k, D\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(\operatorname{sierGraph}\left(r, m\right), (D: \operatorname{Set}\left(\operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right)\right))\right)) \land (\forall u \in \operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right),\; (u \in D) \Rightarrow (\operatorname{card}\left(\operatorname{sdiff}\left(\operatorname{neighborFinset}\left(\operatorname{sierGraph}\left(r, m\right), u\right), D\right)\right) \le k)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.isKLimited` (`✓ std3`).

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

A set is k-limited dominating when it is dominating and every selected vertex has at most k neighbors outside the set.

**Definition 1.4 (Limited domination number).**

$$\forall r \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{gamma}\left(r, m, k\right) = \operatorname{sInf}\left(\{n: \mathrm{Nat} \mid \exists D \in \operatorname{Finset}\left(\operatorname{Fin}\left(r + 1\right) \to \operatorname{Fin}\left(m\right)\right),\; (\operatorname{isKLimited}\left(r, m, k, D\right)) \land (\operatorname{card}\left(D\right) = n)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.gamma` (`✓ std3`).

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

gamma r m k is the infimum of the cardinalities of k-limited dominating subsets of the functions from Fin (r + 1) to Fin m.

**Definition 1.5 (Conjecture 12).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; ((1 \le n) \land ((2 \le m) \land ((1 \le k) \land (k \le m - 1)))) \Rightarrow (\operatorname{gamma}\left(n - 1, m, k\right) = \left(m - k\right) \cdot m^{n - 1}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.claim` (`✓ std3`).

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

Section 6, Conjecture 12 (p. 9) states verbatim: "Let n, m, and k be integers such that n ≥ 1 and 1 ≤ k ≤ m − 1. Then γ_k^L(S(n, m)) = (m−k)·m^(n−1)." The formal encoding uses n,m,k : ℕ, the graph rank n−1, and gamma for γ_k^L.

**Theorem 1.6 (Conjecture 12 proved).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.result` (`✓ std3`). ∎

*Citation.* D. Božović (2026). *On k-limited domination: complexity and Sierpiński graphs*. DOI: [10.48550/arXiv.2610.01584](https://doi.org/10.48550/arXiv.2610.01584). URL: <https://arxiv.org/abs/2610.01584v1>.

*Commentary.*

The theorem result has type claim. Its proof gives a recursive coloring constant on linking edges and bijective on every base clique for the upper bound; the lower bound charges every empty base clique an additional k−1 vertices. The result also specializes the source's Theorems 10 and 11 at k = 1 and m = 3.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.gamma`
- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.isKLimited`
- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.sierAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.sierGraph`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
