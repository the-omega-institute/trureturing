# Brown–Mol Conjecture 4.2 and the subtree root of a 206-vertex tree

## Abstract

A 206-vertex tree has a subtree root strictly inside the inner circle of the Brown–Mol annulus.

**Definition 1.1 (The subtree polynomial).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Finite}\left(V\right)], \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (z: \mathbb{C}), \left(P_{G}\right)\left(z\right) = \sum_{S \in \operatorname{ConnectedSubsets}\left(G\right)} z^{\left|S\right|}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.subtreePolynomial` (`✓ std3`).

*Citation.* Jason I. Brown; Lucas Mol (2018). *On the roots of the subtree polynomial*. URL: <https://arxiv.org/abs/1810.08655v1>.

*Commentary.*

In Lean, P_G(z) evaluates subtreePolynomial G at z. ConnectedSubsets(G) consists of the nonempty vertex sets S for which the induced graph G[S] is connected. Each set contributes once. For a tree these are exactly its subtrees.

**Definition 1.2 (The proposed translated annulus).**

$$\forall T \in \operatorname{FiniteTree},\; \forall z \in \mathbb{C},\; (2 \le n\left(T\right) \land \left(P_{T}\right)\left(z\right) = 0) \Rightarrow (\frac{1}{2} \le \left|z + \frac{1}{2}\right| \land \left|z + \frac{1}{2}\right| \le \frac{1}{2} + (n\left(T\right) - 1)^{\frac{1}{n\left(T\right) - 1}})$$

*Formalization.* `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.Conjecture42` (`✓ std3`).

*Citation.* Jason I. Brown; Lucas Mol (2018). *On the roots of the subtree polynomial*. URL: <https://arxiv.org/abs/1810.08655v1>.

*Commentary.*

Brown and Mol state Conjecture 4.2 on p. 14 of arXiv:1810.08655v1. “If T is a tree of order n ≥ 2, then the subtree roots of T are contained in the annulus” shown above. Both endpoints are inclusive. FiniteTree ranges over simple graphs with a Fintype vertex instance and the IsTree property. Here n(T) is the vertex cardinality. Lean takes the natural predecessor before casting to the reals and uses real division and real exponentiation.

**Theorem 1.3 (A root strictly inside the inner circle).**

$$\neg \operatorname{Conjecture42}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false` (`✓ std3`). ∎

*Resolves.* `Problems/brown-mol-2018-conjecture-4-2` (refuted) by `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brown-mol-2018-conjecture-4-2","declaration_gid":"D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jason I. Brown; Lucas Mol (2018). *On the roots of the subtree polynomial*. URL: <https://arxiv.org/abs/1810.08655v1>.

*Commentary.*

The witness tree T has a hub and 41 branch centers, each with four private leaves. The connected sets comprise those containing the hub, those in one branch containing its center, and singleton leaves. Their contributions give the factorization P_T(z) = zF(z).

$$
\forall (z: \mathbb{C}), \left(P_{T}\right)\left(z\right) = z \cdot ((1 + z \cdot (1 + z)^{4})^{41} + 41 \cdot (4 + (1 + z)^{4}))
$$

Set D = 1000 and C = −539 + 496i. Write D^205 F((C+h)/D) = Σ a_k h^k, with Gaussian-integer coefficients. Put S = D^205. The O(205) analytic bounds use a linear pass over the coefficients after convolution. They give 1000|a_0| ≤ 2537S, 5225S ≤ 1000|a_1| and 1000 Σ_{k=2}^{205} 2^k |a_k| ≤ 425S, including both tail endpoints. The kernel checks the upper estimates with the coordinate sum norm and the lower estimate with the coordinate maximum norm. The comparison is strict because 2537 + 425 < 5225 on the square boundary, where 1 ≤ |h| ≤ 2.

The pinned rectangle zero-count theorem applies to the shifted polynomial and the linear function a_1 h, whose sole zero in the square is simple. For the resulting root z = (C+h)/D, the bound |C+500| < 498 gives |z+1/2| < (498+2)/1000 = 1/2. Thus z is nonzero and violates the inner bound.

Jin, Ma and Wang, arXiv:2608.07898v2, repeat the translated annulus as Conjecture 5.1. Their Theorem 1.3 proves the separate origin-centered upper bound |z| ≤ 1 + (n−1)^(1/(n−1)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.Conjecture42`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.subtreePolynomial`
- Dependency: [D5/S3/Weil/ZetaAnalytic/RoucheZeroCount](../../../Weil/ZetaAnalytic/RoucheZeroCount.md)
