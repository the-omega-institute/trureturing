# The printed Chen–Chow conjecture for membranes

## Abstract

A normalized two-letter array satisfies the printed membrane shuffle equations and has no piecewise bilinear realization.

**Definition 1.1 (Piecewise bilinear membranes).**

$$(\operatorname{PiecewiseBilinear}\left(X\right)) \Leftrightarrow (\exists m \in \mathbb{N},\; (\exists n \in \mathbb{N},\; (((0 < m) \land (0 < n)) \land (\forall i \in \operatorname{Fin}\left(m\right),\; (\forall j \in \operatorname{Fin}\left(n\right),\; (\forall c \in \operatorname{Fin}\left(d\right),\; (\exists a \in \mathbb{R},\; (\exists b \in \mathbb{R},\; (\exists e \in \mathbb{R},\; (\exists f \in \mathbb{R},\; (\forall s \in \mathbb{R},\; (\forall t \in \mathbb{R},\; (((s \in \operatorname{I}\left(m, i\right)) \land (t \in \operatorname{I}\left(n, j\right))) \Rightarrow (X\left(s, t, c\right) = a + b \cdot s + e \cdot t + f \cdot s \cdot t))))))))))))))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.PiecewiseBilinear` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Section 4, p. 20, calls a membrane of order (m,n) one that is biaffine on every closed rectangle [(i−1)/m,i/m] × [(j−1)/n,j/n]. In zero-based indices I(m,i) is [i/m,(i+1)/m]. Both grid sizes are arbitrary positive integers. Biaffinity means that each component agrees throughout each closed cell with a polynomial a + bs + et + fst. One function on the whole square gives the same values on shared cell boundaries. The Lean function is a total ambient extension to ℝ × ℝ, with its cell conditions confined to the square.

**Definition 1.2 (Native mixed-partial signature).**

$$\begin{aligned}(l = 0) \Rightarrow (\operatorname{signature}\left(X, l, w, \tau\right) = 1)\\(0 < l) \Rightarrow (\operatorname{signature}\left(X, l, w, \tau\right) = \int_{\operatorname{simplex}\left(l\right) \times \operatorname{simplex}\left(l\right)} \prod_{j\in\operatorname{Fin}\left(l\right)} \operatorname{mixed}\left(X, w\left(j\right), s_{j}, t_{\tau\left(j\right)}\right)\,ds\,dt)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.signature` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Definition 1.1, p. 2, integrates over the product of the two weakly increasing unit simplices. In degree ℓ, w lists ℓ letters and τ permutes ℓ column slots. The j-th factor is the real mixed partial of component w(j) evaluated at (s_j,t_{τ(j)}). The native derivative differentiates in t and then in s. On open cells it equals the biaffine mixed coefficient, and either derivative order gives that coefficient there. The grid lines and their pullbacks through each pair of coordinate evaluations are Lebesgue null. The integral therefore depends only on the square restriction. Degree zero equals one.

**Definition 1.3 (The printed truncated shuffle equations).**

$$(\operatorname{Printed}\left(a\right)) \Leftrightarrow (\forall m \in \operatorname{Fin}\left(k + 1\right),\; (\forall n \in \operatorname{Fin}\left(k + 1\right),\; ((m + n \le k) \Rightarrow (\forall u \in \operatorname{Word}\left(d, m\right),\; (\forall v \in \operatorname{Word}\left(d, n\right),\; (\forall alpha \in \operatorname{Rank}\left(m\right),\; (\forall beta \in \operatorname{Rank}\left(n\right),\; (a\left(m, u, alpha\right) \cdot a\left(n, v, beta\right) = \operatorname{printedRhs}\left(a, m, n, u, v, alpha, beta\right)))))))))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Printed` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Theorem 2.10, p. 6, uses the product in Definition 2.6, p. 5. Test every ordered pair of words u,v and ranks α,β in degrees m,n with m+n ≤ k. In the positive-degree sum, π and λ independently range over the permutations increasing on each of the two source blocks. The word in a summand is the concatenation uv composed with π⁻¹. Its rank is λ ∘ (α ▷ β)⁻¹ ∘ π⁻¹, where α ▷ β extends both ranks on their own blocks. Every shuffle pair contributes once, even when distinct pairs index the same coordinate. The empty word and its unique permutation act as the unit.

**Definition 1.4 (Conjecture 6.10 as printed).**

$$\forall d \in \mathbb{N},\; (\forall k \in \mathbb{N},\; ((2 \le d) \Rightarrow (\forall a \in \operatorname{Array}\left(\mathbb{R}, d, k\right),\; ((\operatorname{Printed}\left(a\right)) \Rightarrow (\exists X \in \operatorname{Membrane}\left(d\right),\; ((\operatorname{PiecewiseBilinear}\left(X\right)) \land (\operatorname{signature}\left(X\right) = a)))))))$$

*Formalization.* `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim` (`✓ std3`).

*Citation.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Conjecture 6.10, p. 32. “For every sequence s ∈ ⊕_{ℓ=0}^k ⊕_{ν∈Σ_ℓ}(ℝ^d)^{⊗ℓ} with entries satisfying the two-parameter shuffle identity (Theorem 2.10) there is a piecewise bilinear membrane such that its k-truncated signature coincides with s.” The real array has one entry for each degree ℓ ≤ k, word on d letters, and permutation of ℓ slots. Equality of signatures means equality at every one of these indices.

**Theorem 1.5 (A normalized array with no membrane realization).**

$$\neg (\forall d \in \mathbb{N},\; (\forall k \in \mathbb{N},\; ((2 \le d) \Rightarrow (\forall a \in \operatorname{Array}\left(\mathbb{R}, d, k\right),\; ((\operatorname{Printed}\left(a\right)) \Rightarrow (\exists X \in \operatorname{Membrane}\left(d\right),\; ((\operatorname{PiecewiseBilinear}\left(X\right)) \land (\operatorname{signature}\left(X\right) = a))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carlos Améndola; Gabriel Riffo; Leonard Schmitz (2026). *Universal Varieties for Signatures of Membranes*. DOI: [10.48550/arXiv.2610.16724](https://doi.org/10.48550/arXiv.2610.16724). URL: <https://arxiv.org/abs/2610.16724v1>.

*Commentary.*

Take d = 2 and k = 4. The rational array has 443 coordinates, with the empty coordinate equal to one and zero whenever the word uses the second letter. Its coefficients satisfy all 1,177 ordered equations of the printed system. For the input pair (1,1) and (111,231) in one-based notation, both the product and the printed sum equal 19/4.

In a product of the degree-one and degree-three integrals, insert the singleton at one of four positions on each axis. Up to null ties, the 16 chambers partition the joint domain. Reindexing the axes sends old row slot j to π(j) and its old column slot (α ▷ β)(j) to λ((α ▷ β)(j)). The new row word uses π⁻¹ and the new rank is λ ∘ (α ▷ β) ∘ π⁻¹. For the same rational input pair this forward shuffle sum equals 7/4, so equality to a membrane signature is impossible.

The same array refutes the printed conjecture with explicit degree-zero normalization. Realizability under the genuine shuffle equations remains open.

## References

- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.PiecewiseBilinear`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.Printed`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.claim`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.refute_conjecture_6_10_v1`
- Truth anchor: `D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.signature`
- Dependency: [D5/S3/Quantum/Transport/MatrixUnitDyson](../../Quantum/Transport/MatrixUnitDyson.md)
