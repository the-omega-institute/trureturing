# Non-shortening in the one-wall hypereclectic spin chain

## Abstract

Powers of the one-wall hypereclectic Hamiltonian have maximal rank between levels.

**Theorem 1.1 (Zero kernel of a lowering power).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall h \in \operatorname{Module.End}\left(K, V\right),\; \forall e \in \operatorname{Module.End}\left(K, V\right),\; \forall f \in \operatorname{Module.End}\left(K, V\right),\; [\operatorname{IsSl2Triple}\left(h, e, f\right)] \forall n \in \mathbb{N},\; \forall v \in V,\; \forall q \in \mathbb{N},\; \forall k \in \mathbb{N},\; (h\left(v\right) = (q : K) \cdot v) \Rightarrow ((k \le q) \Rightarrow (((e^{n})\left(v\right) = 0) \Rightarrow (((f^{k})\left(v\right) = 0) \Rightarrow (v = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.lowering_kernel_zero` (`✓ std3`). ∎

*Citation.* P. Etingof; O. Golberg; S. Hensel; T. Liu; A. Schwendner; D. Vaintrob; E. Yudovina (2011). *Introduction to representation theory*. DOI: [10.48550/arXiv.0901.0827](https://doi.org/10.48550/arXiv.0901.0827). URL: <https://arxiv.org/abs/0901.0827v5>.

*Commentary.*

Problem 1.55(b) gives the polynomial identity for a primitive vector, and part (f) gives the nonvanishing lowering string. The induction extends this to a vector killed by a raising power.

**Definition 1.2 (The inversion level).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}),\; \operatorname{level}\left(w\right) = \sum_{i\in\operatorname{Fin}\left(N\right)} \sum_{j\in\operatorname{Fin}\left(N\right)} \operatorname{ite}\left((i < j \land w\left(i\right) = \operatorname{true} \land w\left(j\right) = \operatorname{false}), 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.level` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

A Boolean word records the letters before the fixed wall 3: false denotes 1 and true denotes 2. Its level counts a 2 before a 1. This is S = Σ_{j=1}^{M−1} j n_j in Eq. (3.18), printed p. 10: each 1 in the j-th gap has exactly j twos to its left. All indices are zero-based. Subtraction of natural numbers is truncated at zero throughout these formulas.

**Definition 1.3 (The static sector).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \operatorname{sector}\left(L, M\right) = \left\{w \mid w \in (\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}) \land \operatorname{ones}\left(w\right) = M - 1\right\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.sector` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The K = 1 static sector has L−1 Boolean letters and M−1 twos, with the wall fixed at the right. The function ones is the binary-coordinate count Σ_i ite(w(i) = true, 1, 0), reused from its existing definition.

**Definition 1.4 (The elementary-state level space).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall S \in \mathbb{N},\; \operatorname{W}\left(L, M, S\right) = \operatorname{span}\left(\mathbb{Q}, \left\{\operatorname{basisFun}\left(\mathbb{Q}, \operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}\right)\left(w\right) \mid w \in \operatorname{sector}\left(L, M\right) \land \operatorname{level}\left(w\right) = S\right\}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.W` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Section 3.2, printed p. 10: “As before we define W_S^{L,M} to be spanned by elementary states with this level S.” Here basisFun(ℚ, Fin(L−1) → Bool)(w) is the delta function at w. The span retains these elementary states as independently specified generators over ℚ.

**Definition 1.5 (A local lowering move).**

$$\forall N \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(N\right),\; \forall b \in \operatorname{Fin}\left(N\right),\; \forall v \in (\left(\operatorname{Fin}\left(N\right) \to \operatorname{Bool}\right) \to \mathbb{Q}),\; \forall w \in (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}),\; \operatorname{localH}\left(a, b\right)\left(v\right)\left(w\right) = \operatorname{ite}\left((w\left(a\right) = \operatorname{false} \land w\left(b\right) = \operatorname{true}), v\left((w \circ \operatorname{swap}\left(a, b\right))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.localH` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

On output coordinates, the local move tests false at a and true at b, and reads the coefficient of the word with those sites exchanged. Otherwise its value is zero.

**Definition 1.6 (A local reverse move).**

$$\forall N \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(N\right),\; \forall b \in \operatorname{Fin}\left(N\right),\; \operatorname{localR}\left(a, b\right) = \operatorname{localH}\left(b, a\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.localR` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The reverse move exchanges the two site arguments of the local lowering operator.

**Definition 1.7 (The one-bin lowering operator).**

$$\forall N \in \mathbb{N},\; \operatorname{Hbin}\left(N\right) = \sum_{p\in\operatorname{Fin}\left(N - 1\right)} \operatorname{localH}\left(\operatorname{val}\left(p\right), \operatorname{val}\left(p\right) + 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.Hbin` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The bin operator sums all adjacent lowering moves. Here val(p) and val(p)+1 are regarded as sites of Fin(N); the sum is empty for bins of length zero or one.

**Definition 1.8 (The one-bin raising operator).**

$$\forall N \in \mathbb{N},\; \operatorname{Rbin}\left(N\right) = \sum_{p\in\operatorname{Fin}\left(N - 1\right)} \operatorname{smul}\left(\operatorname{asRat}\left(\operatorname{val}\left(p\right) + 1\right) \cdot (\operatorname{asRat}\left(N\right) - \operatorname{asRat}\left(\operatorname{val}\left(p\right) + 1\right)), \operatorname{localR}\left(\operatorname{val}\left(p\right), \operatorname{val}\left(p\right) + 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.Rbin` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Each reverse adjacent move has coefficient (val(p)+1)(N−(val(p)+1)), interpreted in the rational numbers; asRat is the natural-number cast to the rationals. These coefficients give the raising operator paired with Hbin.

**Definition 1.9 (The diagonal word weight).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}),\; \operatorname{weight}\left(w\right) = \sum_{i\in\operatorname{Fin}\left(N\right)} \operatorname{ite}\left(w\left(i\right) = \operatorname{true}, \operatorname{asRat}\left(N\right) - 1 - 2 \cdot \operatorname{asRat}\left(\operatorname{val}\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.weight` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Each true letter at site i contributes N−1−2 val(i), interpreted in the rational numbers. False letters contribute zero.

**Theorem 1.10 (Weight from the inversion level).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}),\; \operatorname{weight}\left(w\right) = 2 \cdot \operatorname{asRat}\left(\operatorname{level}\left(w\right)\right) - \operatorname{asRat}\left(\operatorname{ones}\left(w\right)\right) \cdot (\operatorname{asRat}\left(N\right) - \operatorname{asRat}\left(\operatorname{ones}\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.weight_eq_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal weight equals twice the inversion level minus the product of the numbers of true and false letters. Natural counts are cast to the rational numbers before the displayed arithmetic.

**Theorem 1.11 (The one-bin sl₂ triple).**

$$\forall N \in \mathbb{N},\; (2 \leq N \Rightarrow \operatorname{IsSl2Triple}\left(\operatorname{mulLeft}\left(\mathbb{Q}, ((w : (\operatorname{Fin}\left(N\right) \to \operatorname{Bool})) \mapsto \operatorname{weight}\left(w\right))\right), \operatorname{Rbin}\left(N\right), \operatorname{Hbin}\left(N\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.binSl2Triple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bin of length at least two, multiplication by the word weight, the raising operator and the lowering operator form an sl₂ triple. In particular the diagonal operator is nonzero and the three commutator relations hold. Empty and one-site bins are outside this triple statement.

**Definition 1.12 (The adjacent-move Hamiltonian).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall v \in (\left(\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}\right) \to \mathbb{Q}),\; \forall w \in (\operatorname{Fin}\left(L - 1\right) \to \operatorname{Bool}),\; \operatorname{H}\left(L, M\right)\left(v\right)\left(w\right) = \sum_{p\in\operatorname{Fin}\left(L - 1 - 1\right)} \operatorname{ite}\left((w\left(\operatorname{val}\left(p\right)\right) = \operatorname{false} \land w\left(\operatorname{val}\left(p\right) + 1\right) = \operatorname{true}), v\left((w \circ \operatorname{swap}\left(\operatorname{val}\left(p\right), \operatorname{val}\left(p\right) + 1\right))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.H` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Section 3.2, printed p. 10: “The Hamiltonian acts on (3.16) as” Eq. (3.19), summing the states with n_{j−1} increased by one and n_j decreased by one. A term with n_j = 0 vanishes. Equivalently, each adjacent input 21 becomes 12 with coefficient one. The displayed formula is on output coordinates, so it tests 12 and reads the swapped input. The notation val(p) regards p : Fin((L−1)−1) as a site of Fin(L−1), and val(p)+1 as its adjacent successor; swap exchanges those sites. Composition acts on word coordinates, not on coefficient vectors. M labels the sector and does not affect this operator.

**Definition 1.13 (The map between level spaces).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall v \in \operatorname{W}\left(L, M, S\right),\; \operatorname{coe}\left(\operatorname{restrict}\left(L, M, S, k\right)\left(v\right)\right) = \left((\operatorname{H}\left(L, M\right))^{k}\right)\left(\operatorname{coe}\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.restrict` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The restriction is the linear map H^k from W_S to W_{S−k}; coe includes a level space into the ambient rational word space. Its range dimension is the rank of the matrix A^(k) in the elementary bases, and d_S is finrank(ℚ, W(L,M,S)).

**Definition 1.14 (The non-shortening claim (A.4)).**

$$\operatorname{claim} = (\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; (1 \leq M \Rightarrow M \leq L \Rightarrow \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k \leq S \Rightarrow \operatorname{finrank}\left(\mathbb{Q}, \operatorname{range}\left(\operatorname{restrict}\left(L, M, S, k\right)\right)\right) = \operatorname{min}\left(\operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S\right)\right), \operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S - k\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.claim` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

Appendix A, printed p. 24: “We claim that the rank of A^(k) is always maximal:” followed by “rank(A^(k)) = min(d_{S−k}, d_S).” (A.4). The introduction of arXiv:2207.02885v1, printed p. 1, states: “They rest on a compelling and extensively checked but unfortunately still unproven non-shortening conjecture.” The encoding quantifies over all 1 ≤ M ≤ L and all k ≤ S, over ℚ. Only the K = 1 static-sector claim is asserted here; the multi-wall, cyclic and eclectic-universality statements are separate questions.

**Theorem 1.15 (Maximal rank at every level).**

$$\forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; (1 \leq M \Rightarrow M \leq L \Rightarrow \forall S \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k \leq S \Rightarrow \operatorname{finrank}\left(\mathbb{Q}, \operatorname{range}\left(\operatorname{restrict}\left(L, M, S, k\right)\right)\right) = \operatorname{min}\left(\operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S\right)\right), \operatorname{finrank}\left(\mathbb{Q}, \operatorname{W}\left(L, M, S - k\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahn-corcoran-staudacher-2021-hypereclectic-non-shortening` (proved) by `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahn-corcoran-staudacher-2021-hypereclectic-non-shortening","declaration_gid":"D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The quadratic reverse-move coefficients and the diagonal inversion weight give an sl₂ triple. Induction on the remaining raising length proves that a lowering power has zero kernel on the upper half of the weights. The contragredient representation gives surjectivity on the lower half. The two cases establish the minimum of the source and target dimensions, including the empty and one-site bins. This proves the K = 1 claim (A.4).

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.H`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.Hbin`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.Rbin`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.W`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.binSl2Triple`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.level`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.localH`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.localR`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.lowering_kernel_zero`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.restrict`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.sector`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.weight`
- Truth anchor: `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.weight_eq_level`
- Dependency: [D5/S1/Words/ParityCode/OddTopWeight](../../../S1/Words/ParityCode/OddTopWeight.md)
