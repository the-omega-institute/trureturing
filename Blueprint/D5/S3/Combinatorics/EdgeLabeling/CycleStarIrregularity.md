# Edge irregularity strength of cycle-star graphs

## Abstract

Cycle-star edge irregularity strength attains both conjectured sharp bounds.

**Definition 1.1 (Vertex labels between one and K).**

$$\forall V \in Type,\; \forall K \in Nat,\; \forall f \in V \to Nat,\; (\operatorname{IsKLabeling}\left(K, f\right)) \Leftrightarrow (\forall x \in V,\; (1 \le f\left(x\right)) \land (f\left(x\right) \le K))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsKLabeling` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Section 1, printed page 726: “A vertex labeling φ:V(G) → {1, 2,…,k} is called k-labeling.” Here K is the label bound and V is the vertex type. Every vertex receives a natural number between one and K; vertex labels may repeat.

**Definition 1.2 (An edge weight is its endpoint sum).**

$$\forall V \in Type,\; \forall f \in V \to Nat,\; \forall u \in V,\; \forall v \in V,\; \operatorname{edgeWeight}\left(f, u, v\right) = f\left(u\right) + f\left(v\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.edgeWeight` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Section 1, printed page 726: “The weight of an edge uv in G, written wφ(uv), is the sum of the labels of end vertices u and v, i.e., wφ(uv)=φ(u)+φ(v).” The function f below is the source's phi.

**Definition 1.3 (Different unordered edges have different weights).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall K \in Nat,\; \forall f \in V \to Nat,\; (\operatorname{IsEdgeIrregularLabeling}\left(G, K, f\right)) \Leftrightarrow ((\operatorname{IsKLabeling}\left(K, f\right)) \land (\forall u \in V,\; \forall v \in V,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, u, v\right)) \Rightarrow ((\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, x, y\right)) \Rightarrow ((\operatorname{edgeWeight}\left(f, u, v\right) = \operatorname{edgeWeight}\left(f, x, y\right)) \Rightarrow (s(u,v) = s(x,y))))))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsEdgeIrregularLabeling` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Section 1, printed page 726: “A vertex k-labeling of a graph G is defined to be an edge irregular k-labeling of the graph G if for every two different edges u and v, wφ(u) ≠ wφ(v).” Equality of weights therefore implies equality in Sym2. The notation s(u,v) denotes the unordered pair, so reversing an edge preserves it.

**Definition 1.4 (Attainment and least positive bound).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall K \in Nat,\; (\operatorname{IsEdgeIrregularityStrength}\left(G, K\right)) \Leftrightarrow (\operatorname{IsLeast}\left(\{L : Nat | (1 \le L) \land (\exists f \in V \to Nat,\; \operatorname{IsEdgeIrregularLabeling}\left(G, L, f\right))\}, K\right))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsEdgeIrregularityStrength` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Section 1, printed page 726: “The minimum k for which the graph G has an edge irregular k-labeling is called the edge irregularity strength of G, written es(G).” IsLeast requires a labeling at K and comparison with every positive feasible L.

**Definition 1.5 (The source's cycle with leaves at one vertex).**

$$\forall k \in Nat,\; \forall n \in Nat,\; \operatorname{cycleStar}\left(k, n\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((fun (a : \operatorname{Fin}\left(n\right)) (b : \operatorname{Fin}\left(n\right)) \mapsto ((\operatorname{val}\left(a\right) = 0) \land (((1 \le \operatorname{val}\left(b\right)) \land (\operatorname{val}\left(b\right) \le n - k)) \lor ((\operatorname{val}\left(b\right) = n - k + 1) \lor (\operatorname{val}\left(b\right) = n - 1)))) \lor ((n - k + 1 \le \operatorname{val}\left(a\right)) \land ((\operatorname{val}\left(a\right) \le n - 2) \land (\operatorname{val}\left(b\right) = \operatorname{val}\left(a\right) + 1))))\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.cycleStar` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Section 1, printed page 727: “The cycle-star graph, written CSₖ,ₙ₋ₖ, is a graph with n vertices consisting of the cycle graph of length k and n-k leafs appended to the same vertex of the cycle.” The source gives V(CSₖ,ₙ₋ₖ)={v,vᵢ: 1 ≤ i ≤ n-1} and E(CSₖ,ₙ₋ₖ)={vvᵢ:1≤i≤n-k} ∪ {vvₙ₋ₖ₊₁,vvₙ₋₁} ∪ {vᵢvᵢ₊₁:n-k+1≤i≤n-2}. Fin n has n vertices: zero is v and positive i is vᵢ. SimpleGraph.fromRel adds reverse orientations and removes loops. The value function val reads a Fin index.

**Definition 1.6 (Conjecture 3.1 with both parameter ranges).**

$$(claim) \Leftrightarrow (\forall k \in Nat,\; \forall n \in Nat,\; (8 \le k) \Rightarrow ((1 \le n - k) \Rightarrow ((((k + 1 \le n) \land (n \le 2 \cdot k - 4)) \Rightarrow (\operatorname{IsEdgeIrregularityStrength}\left(\operatorname{cycleStar}\left(k, n\right), \operatorname{Nat}.\operatorname{div}\left(n + 2, 2\right)\right))) \land ((2 \cdot k - 3 \le n) \Rightarrow (\operatorname{IsEdgeIrregularityStrength}\left(\operatorname{cycleStar}\left(k, n\right), n - k + 2\right))))))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.claim` (`✓ std3`).

*Citation.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Conjecture 3.1, end of Section 3, printed page 738: “Let G=CSₖ,ₙ₋ₖ be a cycle-star graph. For k ≥ 8 and n-k ≥ 1,” followed by “es(G):= ⌈(n+1)/2⌉ for k+1 ≤ n ≤ 2k-4; n-k+2 for n ≥ 2k-3.” All parameters are natural numbers. Nat.div is integer division, and Nat.div(n+2,2) equals the source ceiling. Natural subtraction is truncated. Both implications retain their full source ranges and the common hypotheses.

**Theorem 1.7 (Both conjectured bounds are attained and minimal).**

$$\forall k \in Nat,\; \forall n \in Nat,\; (8 \le k) \Rightarrow ((1 \le n - k) \Rightarrow ((((k + 1 \le n) \land (n \le 2 \cdot k - 4)) \Rightarrow (\operatorname{IsEdgeIrregularityStrength}\left(\operatorname{cycleStar}\left(k, n\right), \operatorname{Nat}.\operatorname{div}\left(n + 2, 2\right)\right))) \land ((2 \cdot k - 3 \le n) \Rightarrow (\operatorname{IsEdgeIrregularityStrength}\left(\operatorname{cycleStar}\left(k, n\right), n - k + 2\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result` (`✓ std3`). ∎

*Resolves.* `Problems/cycle-star-irregularity` (proved) by `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cycle-star-irregularity","declaration_gid":"D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Umme Salma; H. M. Nagesh; Narahari N. (2024). *On edge irregularity strength of cycle-star graphs*. DOI: [10.22199/issn.0717-6279-5801](https://doi.org/10.22199/issn.0717-6279-5801). URL: <https://arxiv.org/abs/2405.12263v1>.

*Commentary.*

Put m=n-k and K=max(m+2,Nat.div(m+k+2,2)). An edge irregular labeling needs at least m+2 distinct labels among the common vertex's neighbors. Its m+k distinct edge sums belong to the interval from 2 through 2L, giving m+k<=2L-1 for any feasible bound L. For the upper bound, label the common vertex K. The internal path labels start with Nat.div(j+1,2). When K<=k-2, increase exactly those terms with j>K and j-K odd. Consecutive sums are j+1 below the threshold and j+2 above it. Thus the first closing edge uses the omitted sum K+1. The second closing sum exceeds all internal sums. Fin.succAbove chooses leaf labels while skipping the other endpoint label; all their sums lie in the remaining upper interval and are distinct. When K>=k-1, all internal sums are at most K, and the closing and leaf sums are larger. The resulting labeling attains K, and the two lower bounds prove leastness. Splitting at n=2k-3 gives exactly the displayed assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsEdgeIrregularLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsEdgeIrregularityStrength`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.IsKLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.claim`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.cycleStar`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.edgeWeight`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.result`
