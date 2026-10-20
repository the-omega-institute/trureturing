# Schmidt-number bounds for incomplete mutually unbiased bases

## Abstract

Incomplete families of mutually unbiased bases obey the Schmidt-number correlation trace-norm bound of Tavakoli and Morelli's Conjecture 3.

The operators, normalized kets, pure projectors, correlation table and SchmidtNumberLE predicate are those of TavakoliMorelliIncompleteEAM. Each unitary matrix supplies an orthonormal basis through its columns. The unitary group consists of square complex matrices U satisfying U adjoint times U = U times U adjoint = identity. The trace norm is the sum of singular values.

**Definition 1.1 (Families of mutually unbiased bases).**

$$\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \operatorname{MUBFamily}\left(d, m\right) = \{U: (\operatorname{Fin}\left(m\right) \to \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \mid \forall (l: \operatorname{Fin}\left(m\right)), \forall (k: \operatorname{Fin}\left(m\right)), (l \ne k) \Rightarrow (\forall (a: \operatorname{Fin}\left(d\right)), \forall (b: \operatorname{Fin}\left(d\right)), (\left\lVert \left(\operatorname{conjTranspose}\left((U\left(l\right)).val\right) \cdot (U\left(k\right)).val\right)\left(a, b\right) \right\rVert)^{2} = \frac{1}{(d: \mathbb{R})})\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.MUBFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Section V B uses m orthonormal bases in dimension d. The squared overlap of a column from one basis with a column from a distinct basis is 1/d. A family is represented by arbitrary unitary matrices with precisely these cross-basis overlaps; the first basis is unrestricted. The type itself imposes no positivity or incompleteness condition on d or m.

**Definition 1.2 (Normalized basis columns).**

$$\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \forall (A: \operatorname{MUBFamily}\left(d, m\right)), \forall (l: \operatorname{Fin}\left(m\right)), \forall (a: \operatorname{Fin}\left(d\right)), ((A).ket\left(l, a\right)).vec = ((i: \operatorname{Fin}\left(d\right)) \mapsto ((A).val\left(l\right)).val\left(i, a\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.ket` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The a-th column of the l-th unitary is the underlying vector of this normalized ket. Unitarity supplies its normalization. A ket is determined by its underlying vector, so the displayed coordinate formula specifies it completely.

**Definition 1.3 (The local rank-one projectors).**

$$\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \forall (A: \operatorname{MUBFamily}\left(d, m\right)), \forall (p: (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(d\right))), (A).effect\left(p\right) = \operatorname{proj}\left((A).ket\left(\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.effect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The outcome label is a pair consisting of a basis label and a column label. Its effect is the pure projector of that column, with no d/n scaling. The d projectors in each basis sum to the identity.

**Definition 1.4 (The rank-one context of a basis).**

$$\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \forall (A: \operatorname{MUBFamily}\left(d, m\right)), \forall (l: \operatorname{Fin}\left(m\right)), \forall (a: \operatorname{Fin}\left(d\right)), ((A).context\left(l\right)).projector\left(a\right) = (A).effect\left((l, a)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.context` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Each basis defines a complete rank-one context whose projectors are its effects. The context carries their Hermitian, idempotent, trace-one and rank-one sandwich identities, together with their sum equal to the identity. These fields hold for every basis of the family.

**Definition 1.5 (The MUB joint-probability table).**

$$\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \forall (rho: \operatorname{BipartiteOp}\left(d\right)), \forall (A: \operatorname{MUBFamily}\left(d, m\right)), \forall (B: \operatorname{MUBFamily}\left(d, m\right)), \operatorname{Qm}\left(rho, A, B\right) = \operatorname{correlation}\left(rho, (A).effect, (B).effect\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.Qm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

As in Section V B and Born's rule in Eq. (8), Qm is the md by md matrix of joint outcome probabilities from the two independently chosen local families. The correlation definition takes the real part of each trace and embeds it in the complex numbers. The complete collection across m bases is used without averaging over the basis labels.

**Definition 1.6 (Tavakoli–Morelli Conjecture 3).**

$$(claim) \Leftrightarrow (\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), \forall (r: \mathbb{N}), (1 \le d) \Rightarrow ((1 \le m) \Rightarrow ((m \le d) \Rightarrow ((1 \le r) \Rightarrow ((r \le d) \Rightarrow (\forall (A: \operatorname{MUBFamily}\left(d, m\right)), \forall (B: \operatorname{MUBFamily}\left(d, m\right)), \forall (rho: \operatorname{BipartiteOp}\left(d\right)), (\operatorname{SchmidtNumberLE}\left(rho, r\right)) \Rightarrow (\operatorname{traceNorm}\left(\operatorname{Qm}\left(rho, A, B\right)\right) \le 1 + \frac{((m: \mathbb{R}) - 1) \cdot (r: \mathbb{R})}{(d: \mathbb{R})})))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.claim` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Section V B, Conjecture 3, Eq. (54), asserts the bound for a state of Schmidt number r and m less than d+1 bases. The statement takes positive d and m with m at most d, and r from one to d. It uses Schmidt number at most r, since the right side increases with r. The subtraction m-1 and the division in the bound are real arithmetic.

**Theorem 1.7 (The incomplete-MUB Schmidt-number bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.result` (`✓ std3`). ∎

*Resolves.* `Problems/tavakoli-morelli-2024-conjecture-3-incomplete-mub-schmidt-bound` (proved) by `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tavakoli-morelli-2024-conjecture-3-incomplete-mub-schmidt-bound","declaration_gid":"D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For Hermitian H, subtract its scalar trace component. Mutual unbiasedness makes the trace-zero diagonal subspaces of distinct bases orthogonal. Their measurement projections obey Pythagoras, so the sum of their squared trace coordinates is at most the squared Hilbert–Schmidt norm of the centered H. Restoring the scalar component gives the second-moment bound tr(H squared) plus (m-1)/d times (tr H) squared. Dimension one is handled directly, since the trace-zero space is zero.

For a pure bipartite state the singular value decomposition of its coefficient matrix gives a Gram factorization of the probability table. The columns of its two factors are vectorized rank-one effects sandwiched by the square roots of the Schmidt diagonal and the local unitaries, with transposed effects on the second side. Hilbert–Schmidt Hölder bounds the trace norm by the product of their Frobenius norms. The sum of squared Schmidt coefficients equals one, and their sum squared is at most r. The common second-moment estimate therefore gives alpha plus beta r with alpha = 1 and beta = (m-1)/d. Linearity of the probability table, together with the trace-norm triangle inequality and homogeneity for nonnegative weights, extends this to every finite convex mixture of Schmidt rank at most r. This is the shared second-moment theorem applied to the MUB projectors, and its bound is exactly claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.MUBFamily`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.Qm`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.context`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.effect`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.ket`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.result`
- Dependency: [D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM](TavakoliMorelliIncompleteEAM.md)
- Dependency: [D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes](../Tomography/MutuallyUnbiasedDiagonalPlanes.md)
