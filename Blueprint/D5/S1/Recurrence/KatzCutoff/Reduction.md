# Reduction

## Abstract

Continuants, path entries and Katz cut-offs.

Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.

**Definition 1.1 (katz).**

$$\forall n: \mathbb{N}, \forall \alpha: \mathbb{R}, \operatorname{katz}\left(n, \alpha\right) = (1 - \alpha \cdot \operatorname{SimpleGraph.pathGraph}\left(n\right).adjMatrix\left(\mathbb{R}\right))^{-1} - 1$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/Reduction.katz` (`✓ std3`).

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Definition 1, page 2: “Let G be a simple graph with adjacency matrix A, and let 0 < α < 1/ρ(A). Then the Katz matrix of G at α is given by K_G(α) = αA + α²A² + α³A³ + ⋯ = ∑_{t=1}^∞ αᵗAᵗ = (I − αA)⁻¹ − I and the Katz similarity index at α between vertices i and j of G is given by K_G(α)_{i,j}.” Here G is SimpleGraph.pathGraph n, on Fin n, and the inverse is the matrix inverse.

**Definition 1.2 (katzEntry).**

$$\forall n: \mathbb{N}, \forall \alpha: \mathbb{R}, \forall i: \mathbb{N}, \forall j: \mathbb{N}, \operatorname{katzEntry}\left(n, \alpha, i, j\right) = (if h: ((i < n) \land (j < n)) then \operatorname{katz}\left(n, \alpha\right)\left(\langle i, h.1 \rangle, \langle j, h.2 \rangle\right) else 0)$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/Reduction.katzEntry` (`✓ std3`).

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Definition 1, page 2: “Let G be a simple graph with adjacency matrix A, and let 0 < α < 1/ρ(A). Then the Katz matrix of G at α is given by K_G(α) = αA + α²A² + α³A³ + ⋯ = ∑_{t=1}^∞ αᵗAᵗ = (I − αA)⁻¹ − I and the Katz similarity index at α between vertices i and j of G is given by K_G(α)_{i,j}.” The indices here start at zero; an out-of-range index gives zero.

**Definition 1.3 (p1).**

$$\forall n: \mathbb{N}, \forall \alpha: \mathbb{R}, \operatorname{p1}\left(n, \alpha\right) = iInf\left((fun i: \operatorname{Fin}\left(n - 1\right) \mapsto \operatorname{katzEntry}\left(n, \alpha, \operatorname{val}\left(i\right), \operatorname{val}\left(i\right) + 1\right))\right) - iSup\left((fun i: \operatorname{Fin}\left(n - 2\right) \mapsto \operatorname{katzEntry}\left(n, \alpha, \operatorname{val}\left(i\right), \operatorname{val}\left(i\right) + 2\right))\right)$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/Reduction.p1` (`✓ std3`).

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Section 4.2, page 13: “Consider the polynomial ₙp_j(α) = min_i K_{P_n}(α)_{i,i+j} − max_i K_{P_n}(α)_{i,i+j+1}.” The display specializes j to one and uses exactly the ranges on which both vertices exist.

**Theorem 1.4 (p1 reduction).**

$$\forall n: \mathbb{N}, (6 \le n) \implies (\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\operatorname{p1}\left(n, \alpha\right) = \frac{\alpha \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(n - 2\right)}{\operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(n\right)} \cdot (1 - \operatorname{RAB}\left(\alpha, \operatorname{Nat.div}\left(n, 2\right), \operatorname{Nat.div}\left(n - 1, 2\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/Reduction.p1_reduction` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Proposition 15, page 14, reduces the comparison of the distance-one and distance-two Katz entries to the scalar ratio RAB.

## References

- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Reduction.katz`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Reduction.katzEntry`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Reduction.p1`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Reduction.p1_reduction`
- Dependency: [D5/S1/Recurrence/KatzCutoff/ProductExtrema](ProductExtrema.md)
