# The straight linear k-tree resistance increment limit

## Abstract

Endpoint resistance in powers of a finite path.

**Definition 1.1 (Straight linear k-tree).**

$$\forall n \in \operatorname{Nat},\; \forall k \in \operatorname{Nat},\; \operatorname{graph}\left(n, k\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\lambda i: \operatorname{Fin}\left(n\right) \mapsto (\lambda j: \operatorname{Fin}\left(n\right) \mapsto \operatorname{Nat}.\operatorname{dist}\left(\operatorname{val}\left(i\right), \operatorname{val}\left(j\right)\right) \le k))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.graph` (`✓ std3`).

*Citation.* Wayne Barrett; Emily J. Evans; Amanda E. Francis (2017). *Resistance distance in straight linear 2-trees*. DOI: [10.1016/j.dam.2018.10.043](https://doi.org/10.1016/j.dam.2018.10.043). URL: <https://arxiv.org/abs/1712.05883v1>.

*Commentary.*

Definition 43 (arXiv:1712.05883v1, p. 20): A straight linear k-tree is a graph Gₙ with n vertices with adjacency matrix that is symmetric, banded, with the first through kth subdiagonals equal to one and first through kth superdiagonals equal to one, and all other entries equal to zero. In other words Gₙ is the graph whose (0,1)-adjacency matrix is defined by aᵢⱼ=1 if 0<|i-j|≤ k, and aᵢⱼ=0 otherwise. The vertex i in Fin n represents source vertex i+1; fromRel removes loops and symmetrizes the relation.

**Definition 1.2 (Kirchhoff resistance sequence).**

$$\forall k \in \operatorname{Nat},\; \forall R \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{IsResistanceSequence}\left(k, R\right) = \left(\forall t \in \operatorname{Nat},\; \exists V \in \operatorname{Fin}\left(t + 2\right) \to \operatorname{Real},\; (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(\operatorname{graph}\left(t + 2, k\right), \operatorname{Real}\right), V\right) = \operatorname{Pi}.\operatorname{single}\left(0, (1: \operatorname{Real})\right) - \operatorname{Pi}.\operatorname{single}\left(\operatorname{Fin}.\operatorname{last}\left(t + 1\right), (1: \operatorname{Real})\right)) \land (R\left(t\right) = V\left(0\right) - V\left(\operatorname{Fin}.\operatorname{last}\left(t + 1\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.IsResistanceSequence` (`✓ std3`).

*Citation.* Wayne Barrett; Emily J. Evans; Amanda E. Francis (2017). *Resistance distance in straight linear 2-trees*. DOI: [10.1016/j.dam.2018.10.043](https://doi.org/10.1016/j.dam.2018.10.043). URL: <https://arxiv.org/abs/1712.05883v1>.

*Commentary.*

The potential difference vᵢ - vⱼ between nodes i and j needed to maintain this current is the effective resistance or resistance distance between i and j since by Ohm's law, the resistance, r_G(i,j) is r_G(i,j) = (vᵢ-vⱼ)/1 = vᵢ-vⱼ. The source vector of currents is s = eᵢ -eⱼ. Then by Kirchoff's law and Ohm's law, L(G)v = s. This is the unit-current equation in section 2, p. 3 of arXiv:1712.05883v1. Unit edge weights give the graph Laplacian. The index t represents size t+2, and the resistance is the first voltage minus the last voltage.

**Definition 1.3 (Conjecture 44).**

$$\operatorname{claim} = \left(\forall k \in \operatorname{Nat},\; (1 \le k) \Rightarrow ((\exists R \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{IsResistanceSequence}\left(k, R\right)) \land (\forall R \in \operatorname{Nat} \to \operatorname{Real},\; (\operatorname{IsResistanceSequence}\left(k, R\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\lambda t: \operatorname{Nat} \mapsto R\left(t + 1\right) - R\left(t\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\frac{(6: \operatorname{Real})}{(k: \operatorname{Real}) \cdot \left((k: \operatorname{Real}) + 1\right) \cdot \left(2 \cdot (k: \operatorname{Real}) + 1\right)}\right)\right))))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.claim` (`✓ std3`).

*Citation.* Wayne Barrett; Emily J. Evans; Amanda E. Francis (2017). *Resistance distance in straight linear 2-trees*. DOI: [10.1016/j.dam.2018.10.043](https://doi.org/10.1016/j.dam.2018.10.043). URL: <https://arxiv.org/abs/1712.05883v1>.

*Commentary.*

Conjecture 44 (arXiv:1712.05883v1, p. 20): Let G be the straight linear k-tree, k ≥ 1, with n vertices and H be the straight linear k-tree with n+1 vertices. Then limₙ→∞ r_H(1,n+1) − r_G(1,n) = 6/(k(k+1)(2k+1)). Evans and Francis restate this as Conjecture 4.5 in arXiv:2108.07942v2. Each k is fixed before the size tends to infinity. Existence is included, and every solution of the Kirchhoff equation has the asserted increment limit.

**Theorem 1.4 (The increment limit for every positive k).**

$$\forall k \in \operatorname{Nat},\; (1 \le k) \Rightarrow ((\exists R \in \operatorname{Nat} \to \operatorname{Real},\; \operatorname{IsResistanceSequence}\left(k, R\right)) \land (\forall R \in \operatorname{Nat} \to \operatorname{Real},\; (\operatorname{IsResistanceSequence}\left(k, R\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\lambda t: \operatorname{Nat} \mapsto R\left(t + 1\right) - R\left(t\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\frac{(6: \operatorname{Real})}{(k: \operatorname{Real}) \cdot \left((k: \operatorname{Real}) + 1\right) \cdot \left(2 \cdot (k: \operatorname{Real}) + 1\right)}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/linear-k-tree-resistance` (proved) by `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"linear-k-tree-resistance","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Emily J. Evans; Amanda E. Francis (2017). *Resistance distance in straight linear 2-trees*. DOI: [10.1016/j.dam.2018.10.043](https://doi.org/10.1016/j.dam.2018.10.043). URL: <https://arxiv.org/abs/1712.05883v1>.

*Commentary.*

The interval Gram matrix Q satisfies I ≤ Q ≤ D I, where D is the sum of the first k squares. Its defect c = D 1 - Q 1 is supported at the two endpoints. Finite propagation stabilizes every polynomial endpoint moment, and geometric approximation to the inverse makes the inverse quadratic correction converge. The identity R = N/D + (1ᵀc + cᵀQ⁻¹c)/D² then yields the increment limit. The sum-of-squares identity gives the displayed slope, including k=1.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.IsResistanceSequence`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.graph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary](LinearKTreeBoundary.md)
- Dependency: [D5/S3/Observer/BlockStructure/UniformResolventRemainder](../../Observer/BlockStructure/UniformResolventRemainder.md)
