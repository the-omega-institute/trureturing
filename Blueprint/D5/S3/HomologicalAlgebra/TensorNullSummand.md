# He–Tubbenhauer: a null summand in a tensor power

## Abstract

A tensor power of every singular finite-semigroup representation contains a one-dimensional null summand; every indecomposable-summand count is asymptotic to the tensor dimension.

**Definition 1.1 (A one-dimensional null direct summand).**

$$\forall (k: Type), \forall (S: Type), \forall (W: Type), [\operatorname{Field}\left(k\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(k, W\right)] \forall (a: S \to \operatorname{Module}.\operatorname{End}\left(k, W\right)), (\operatorname{HasNullSummand}\left(a\right)) \Leftrightarrow (\exists (L: \operatorname{Submodule}\left(k, W\right)), \exists (U: \operatorname{Submodule}\left(k, W\right)), (\operatorname{Module}.\operatorname{finrank}\left(k, L\right) = 1) \land ((\operatorname{IsCompl}\left(L, U\right)) \land ((\forall (s: S), \forall (x: W), (x \in L) \Rightarrow (a\left(s, x\right) = 0)) \land (\forall (s: S), U \in (a\left(s\right)).invtSubmodule))))$$

*Formalization.* `D5/S3/HomologicalAlgebra/TensorNullSummand.HasNullSummand` (`✓ std3`).

*Citation.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Section 4, page 17: “Unlike in the monoid case, the null representation Z with all elements in S acting as 0 is admitted as a kS-module, and it forms a tensor ideal (in the sense that V⊗Z=Z^{⊕dim V} for all V.)” The summand L has dimension one, every action vanishes on L, and its complementary subspace U is invariant under every action. The complement is an invariant direct summand, rather than a composition factor.

**Definition 1.2 (An indecomposable invariant subspace).**

$$\forall (k: Type), \forall (S: Type), \forall (W: Type), [\operatorname{Field}\left(k\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(k, W\right)] \forall (a: S \to \operatorname{Module}.\operatorname{End}\left(k, W\right)), \forall (P: \operatorname{Submodule}\left(k, W\right)), (\operatorname{IsIndecomposableSummand}\left(a, P\right)) \Leftrightarrow ((P \ne \operatorname{Bot}.\operatorname{bot}) \land ((\forall (s: S), P \in (a\left(s\right)).invtSubmodule) \land (\forall (Q: \operatorname{Submodule}\left(k, W\right)), \forall (R: \operatorname{Submodule}\left(k, W\right)), (Q \le P) \Rightarrow ((R \le P) \Rightarrow ((\forall (s: S), Q \in (a\left(s\right)).invtSubmodule) \Rightarrow ((\forall (s: S), R \in (a\left(s\right)).invtSubmodule) \Rightarrow ((\operatorname{Disjoint}\left(Q, R\right)) \Rightarrow ((\operatorname{Max}.\operatorname{max}\left(Q, R\right) = P) \Rightarrow ((Q = \operatorname{Bot}.\operatorname{bot}) \lor (R = \operatorname{Bot}.\operatorname{bot}))))))))))$$

*Formalization.* `D5/S3/HomologicalAlgebra/TensorNullSummand.IsIndecomposableSummand` (`✓ std3`).

*Citation.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Section 1, page 1 defines b(n) as “# M-indecomposable summands of V^{⊗n} (counted with multiplicity)”. Section 4 applies the growth question to nonunital semigroup modules. A nonzero invariant subspace P is indecomposable when every decomposition into disjoint invariant subspaces Q and R has a zero factor. All three subspaces lie in the same ambient W.

**Definition 1.3 (The number of indecomposable summands).**

$$\forall (k: Type), \forall (S: Type), \forall (W: Type), [\operatorname{Field}\left(k\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(k, W\right)] \forall (a: S \to \operatorname{Module}.\operatorname{End}\left(k, W\right)), \forall (b: \mathbb{N}), (\operatorname{IsSummandCount}\left(a, b\right)) \Leftrightarrow (\exists (P: \operatorname{Fin}\left(b\right) \to \operatorname{Submodule}\left(k, W\right)), (\operatorname{DirectSum}.\operatorname{IsInternal}\left(P\right)) \land (\forall (i: \operatorname{Fin}\left(b\right)), \operatorname{IsIndecomposableSummand}\left(a, P\left(i\right)\right)))$$

*Formalization.* `D5/S3/HomologicalAlgebra/TensorNullSummand.IsSummandCount` (`✓ std3`).

*Citation.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Section 1, page 1: “b(n)=b^{M,V}(n)=# M-indecomposable summands of V^{⊗n} (counted with multiplicity).” A family indexed by Fin b records b individual summands, so repeated isomorphic factors are counted separately. DirectSum.IsInternal states that the natural sum of the subspace inclusions is bijective.

**Definition 1.4 (The diagonal action on a tensor power).**

$$\forall (k: Type), \forall (S: Type), \forall (W: Type), [\operatorname{Field}\left(k\right)] [\operatorname{Semigroup}\left(S\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(k, W\right)] \forall (rho: \operatorname{MulHom}\left(S, \operatorname{Module}.\operatorname{End}\left(k, W\right)\right)), \forall (n: \mathbb{N}), \operatorname{tensorAction}\left(rho, n\right) = fun (s: S) \mapsto \operatorname{PiTensorProduct}.\operatorname{map}\left(fun (\mathord{\cdot}: \operatorname{Fin}\left(n\right)) \mapsto rho\left(s\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/TensorNullSummand.tensorAction` (`✓ std3`).

*Citation.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Section 4, page 17, Conjecture 4.2 refers to “V^{⊗m}”. TensorPower k n W is Mathlib's tensor product indexed by Fin n, and PiTensorProduct.map applies the same endomorphism rho(s) to each factor. The centered dot in the displayed function is an anonymous index. The map rho is multiplicative and need not preserve an identity.

**Definition 1.5 (Conjecture 4.2).**

$$(claim) \Leftrightarrow (\forall (k: Type), \forall (S: Type), \forall (V: Type), [\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{Semigroup}\left(S\right)] [\operatorname{Fintype}\left(S\right)] [\operatorname{Nonempty}\left(S\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (rho: \operatorname{MulHom}\left(S, \operatorname{Module}.\operatorname{End}\left(k, V\right)\right)), (\neg \exists (e: S), \forall (s: S), (e \cdot s = s) \land (s \cdot e = s)) \Rightarrow ((\forall (s: S), \neg \operatorname{IsUnit}\left(rho\left(s\right)\right)) \Rightarrow ((\exists (m: \mathbb{N}), (1 \le m) \land (\operatorname{HasNullSummand}\left(\operatorname{tensorAction}\left(rho, m\right)\right))) \land ((\exists (b: \mathbb{N} \to \mathbb{N}), \forall (n: \mathbb{N}), \operatorname{IsSummandCount}\left(\operatorname{tensorAction}\left(rho, n\right), b\left(n\right)\right)) \land (\forall (b: \mathbb{N} \to \mathbb{N}), (\forall (n: \mathbb{N}), \operatorname{IsSummandCount}\left(\operatorname{tensorAction}\left(rho, n\right), b\left(n\right)\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left(fun (n: \mathbb{N}) \mapsto \frac{(b\left(n\right): \mathbb{R})}{(\operatorname{Module}.\operatorname{finrank}\left(k, V\right): \mathbb{R})^{n}}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(1\right)\right)))))))$$

*Formalization.* `D5/S3/HomologicalAlgebra/TensorNullSummand.claim` (`✓ std3`).

*Citation.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Conjecture 4.2, page 17: “Let V be a kS-module on which no element acts invertibly, then there is some m ≥ 1 such that Z is a summand of V^{⊗m}, and consequently a(n)=(dim V)ⁿ.” The field is algebraically closed, S is a nonempty finite semigroup without a two-sided identity, V is finite dimensional, and rho is a nonunital representation. Section 1, page 1 defines asymptotic equality by a ratio tending to one. The second conjunct supplies a count sequence; the third proves the ratio limit for every such sequence. In particular, the limit does not depend on selecting one decomposition.

**Theorem 1.6 (The null-summand conjecture holds).**

$$\forall (k: Type), \forall (S: Type), \forall (V: Type), [\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{Semigroup}\left(S\right)] [\operatorname{Fintype}\left(S\right)] [\operatorname{Nonempty}\left(S\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (rho: \operatorname{MulHom}\left(S, \operatorname{Module}.\operatorname{End}\left(k, V\right)\right)), (\neg \exists (e: S), \forall (s: S), (e \cdot s = s) \land (s \cdot e = s)) \Rightarrow ((\forall (s: S), \neg \operatorname{IsUnit}\left(rho\left(s\right)\right)) \Rightarrow ((\exists (m: \mathbb{N}), (1 \le m) \land (\operatorname{HasNullSummand}\left(\operatorname{tensorAction}\left(rho, m\right)\right))) \land ((\exists (b: \mathbb{N} \to \mathbb{N}), \forall (n: \mathbb{N}), \operatorname{IsSummandCount}\left(\operatorname{tensorAction}\left(rho, n\right), b\left(n\right)\right)) \land (\forall (b: \mathbb{N} \to \mathbb{N}), (\forall (n: \mathbb{N}), \operatorname{IsSummandCount}\left(\operatorname{tensorAction}\left(rho, n\right), b\left(n\right)\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left(fun (n: \mathbb{N}) \mapsto \frac{(b\left(n\right): \mathbb{R})}{(\operatorname{Module}.\operatorname{finrank}\left(k, V\right): \mathbb{R})^{n}}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(1\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TensorNullSummand.result` (`✓ std3`). ∎

*Resolves.* `Problems/ht2508` (proved) by `D5/S3/HomologicalAlgebra/TensorNullSummand.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ht2508","declaration_gid":"D5/S3/HomologicalAlgebra/TensorNullSummand.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David He and Daniel Tubbenhauer (2025). *Tensor powers of representations of (diagram) monoids*. DOI: [10.48550/arXiv.2508.04054](https://doi.org/10.48550/arXiv.2508.04054). URL: <https://arxiv.org/abs/2508.04054v1>.

*Commentary.*

Write K for the intersection of the operator kernels and I for the sum of their images. A complement of K∩I in K is disjoint from I and extends to an invariant direct-sum decomposition. Its dimension is at least the ambient dimension minus twice the sum of the operator ranks. Tensor ranks are at most the corresponding powers of the original ranks. Every original rank is smaller than dim V, so geometric decay gives a positive exponent with a null line. Strong induction on dimension supplies finite indecomposable decompositions. In every such decomposition, the number of factors lies between the tensor dimension minus twice the sum of the tensor ranks and the tensor dimension. The squeeze theorem gives the stated universal limit. These dimension and convergence arguments work over any field and do not require absence of a semigroup identity.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.HasNullSummand`
- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.IsIndecomposableSummand`
- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.IsSummandCount`
- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/TensorNullSummand.tensorAction`
