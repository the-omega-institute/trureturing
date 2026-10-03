# Non-shortening in the one-wall hypereclectic spin chain

## Abstract

Powers of the one-wall hypereclectic Hamiltonian have maximal rank between levels.

**Definition 1.1 (The inversion level).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}),\; \operatorname{level}\left(w\right) = \sum_{i\in\operatorname{Fin}\left(N\right)} \sum_{j\in\operatorname{Fin}\left(N\right)} \operatorname{ite}\left((i < j \land w\left(i\right) = \operatorname{true} \land w\left(j\right) = \operatorname{false}), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.level` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

A Boolean word records the letters before the fixed wall 3: false denotes 1 and true denotes 2. Its level counts a 2 before a 1. This is S = Σ_{j=1}^{M−1} j n_j in Eq. (3.18), printed p. 10: each 1 in the j-th gap has exactly j twos to its left. All indices are zero-based. Subtraction of natural numbers is truncated at zero throughout these formulas.

**Definition 1.2 (The static sector).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \operatorname{sector}\left(L, M\right) = \left\{w \mid w \in (\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}) \land \operatorname{ones}\left(w\right) = M - 1\right\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.sector` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The K = 1 static sector has L−1 Boolean letters and M−1 twos, with the wall fixed at the right. The function ones is the binary-coordinate count Σ_i ite(w(i) = true, 1, 0), reused from its existing definition.

**Definition 1.3 (The elementary-state level space).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall S \in \mathbb{N},\; \operatorname{W}\left(L, M, S\right) = \operatorname{span}\left(\mathbb{Q}, \left\{\operatorname{basisFun}\left(\mathbb{Q}, \operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}\right)\left(w\right) \mid w \in \operatorname{sector}\left(L, M\right) \land \operatorname{level}\left(w\right) = S\right\}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.W` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Section 3.2, printed p. 10: “As before we define W_S^{L,M} to be spanned by elementary states with this level S.” Here basisFun(ℚ, Fin(L−1) → Bool)(w) is the delta function at w. The span retains these elementary states as independently specified generators over ℚ.

**Definition 1.4 (The adjacent-move Hamiltonian).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall v \in (\left(\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}\right) \to \mathbb{Q}),\; \forall w \in (\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}),\; \operatorname{H}\left(L, M\right)\left(v\right)\left(w\right) = \sum_{p\in\operatorname{Fin}\left(L - 1 - 1\right)} \operatorname{ite}\left((w\left(\operatorname{val}\left(p\right)\right) = \operatorname{false} \land w\left(\operatorname{val}\left(p\right) + 1\right) = \operatorname{true}), v\left((w \circ \operatorname{swap}\left(\operatorname{val}\left(p\right), \operatorname{val}\left(p\right) + 1\right))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.H` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Section 3.2, printed p. 10: “The Hamiltonian acts on (3.16) as” Eq. (3.19), summing the states with n_{j−1} increased by one and n_j decreased by one. A term with n_j = 0 vanishes. Equivalently, each adjacent input 21 becomes 12 with coefficient one. The displayed formula is on output coordinates, so it tests 12 and reads the swapped input. The notation val(p) regards p : Fin((L−1)−1) as a site of Fin(L−1), and val(p)+1 as its adjacent successor; swap exchanges those sites. Composition acts on word coordinates, not on coefficient vectors. M labels the sector and does not affect this operator.

**Definition 1.5 (The map between level spaces).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall v \in \operatorname{W}\left(L, M, S\right),\; \operatorname{coe}\left(\operatorname{restrict}\left(L, M, S, k\right)\left(v\right)\right) = \left((\operatorname{H}\left(L, M\right))^{k}\right)\left(\operatorname{coe}\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.restrict` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The restriction is the linear map H^k from W_S to W_{S−k}; coe includes a level space into the ambient rational word space. Its range dimension is the rank of the matrix A^(k) in the elementary bases, and d_S is finrank(ℚ, W(L,M,S)).

**Definition 1.6 (The non-shortening claim (A.4)).**

$$\operatorname{claim} = (\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; (1 \leq M \Rightarrow M \leq L \Rightarrow \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k \leq S \Rightarrow \operatorname{finrank}\left(\mathbb{Q}, \operatorname{range}\left(\operatorname{restrict}\left(L, M, S, k\right)\right)\right) = \operatorname{min}\left(\operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S\right)\right), \operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S - k\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.claim` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Appendix A, printed p. 24: “We claim that the rank of A^(k) is always maximal:” followed by “rank(A^(k)) = min(d_{S−k}, d_S).” (A.4). The introduction of arXiv:2207.02885v1, printed p. 1, states: “They rest on a compelling and extensively checked but unfortunately still unproven non-shortening conjecture.” The encoding quantifies over all 1 ≤ M ≤ L and all k ≤ S, over ℚ. Only the K = 1 static-sector claim is asserted here; the multi-wall, cyclic and eclectic-universality statements are separate questions.

**Theorem 1.7 (Maximal rank at every level).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; (1 \leq M \Rightarrow M \leq L \Rightarrow \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k \leq S \Rightarrow \operatorname{finrank}\left(\mathbb{Q}, \operatorname{range}\left(\operatorname{restrict}\left(L, M, S, k\right)\right)\right) = \operatorname{min}\left(\operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S\right)\right), \operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S - k\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahn-corcoran-staudacher-2021-hypereclectic-non-shortening` (proved) by `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahn-corcoran-staudacher-2021-hypereclectic-non-shortening","declaration_gid":"D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The quadratic reverse-move coefficients and the diagonal inversion weight give an sl₂ triple. Induction on the remaining raising length proves that a lowering power has zero kernel on the upper half of the weights. The contragredient representation gives surjectivity on the lower half. The two cases establish the minimum of the source and target dimensions, including the empty and one-site bins. This proves the K = 1 claim (A.4).

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.H`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.W`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.level`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.restrict`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.sector`
- Dependency: [D5/S1/Words/ParityCode/OddTopWeight](../../../S1/Words/ParityCode/OddTopWeight.md)
