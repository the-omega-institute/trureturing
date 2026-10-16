# Gerzon equality without dimension congruence restrictions

## Abstract

At Gerzon equality, the equiangular parameters satisfy a² = (d + 2)b over every field of characteristic different from two and in every dimension at least two.

**Theorem 1.1 (Pairing a linear combination with an equiangular vector).**

$$\forall (F : Type*), \forall (S : Type*), [\operatorname{Field}\left(F\right)] [\operatorname{AddCommGroup}\left(S\right)] [\operatorname{Module}\left(F, S\right)] \forall (n : \mathbb{N}), \forall (K : \operatorname{LinearMap}.\operatorname{BilinForm}(F, S)), \forall (P : (\operatorname{Fin}\left(n\right) \to S)), \forall (a : F), \forall (b : F), (\forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{K}\left(\operatorname{P}\left(i\right), \operatorname{P}\left(j\right)\right) = \operatorname{if}\left(i = j, a^{2}, b\right)) \Rightarrow (\forall (t : (\operatorname{Fin}\left(n\right) \to F)), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{K}\left(\sum_{i: \operatorname{Fin}\left(n\right)} (\operatorname{smul}\left(\operatorname{t}\left(i\right), \operatorname{P}\left(i\right)\right)), \operatorname{P}\left(j\right)\right) = (a^{2} - b) \cdot \operatorname{t}\left(j\right) + b \cdot (\sum_{i: \operatorname{Fin}\left(n\right)} \operatorname{t}\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.gram_pair_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bilinear form with constant diagonal value a squared and constant off-diagonal value b pairs a linear combination with its j-th vector by separating the j-th coefficient from the sum of all coefficients. The scalar field and the module are arbitrary; neither symmetry nor nondegeneracy is needed.

**Definition 1.2 (Equiangular systems).**

$$\forall (F : \operatorname{Type}), [\operatorname{Field}\left(F\right)] \forall (d : \mathbb{N}), \forall (n : \mathbb{N}), \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}(F, (\operatorname{Fin}\left(d\right) \to F))), \forall (\varphi : (\operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(d\right) \to F))), \forall (a : F), \forall (b : F), \operatorname{IsEquiangularSystem}\left(B, \varphi, a, b\right) = ((\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{B}\left(\varphi(j), \varphi(j)\right) = a) \land (\forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(n\right)), (i \neq j) \Rightarrow (\operatorname{B}\left(\varphi(i), \varphi(j)\right)^{2} = b)))$$

*Formalization.* `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.IsEquiangularSystem` (`✓ std3`).

*Citation.* Gary R. W. Greaves, Joseph W. Iverson, John Jasper, Dustin G. Mixon (2021). *Frames over finite fields: Equiangular lines in orthogonal geometry*. DOI: [10.48550/arXiv.2012.13642](https://doi.org/10.48550/arXiv.2012.13642). URL: <https://arxiv.org/abs/2012.13642v2>.

*Commentary.*

Definition 2.8, page 5: “Let Φ = {ϕⱼ}ⱼ∈[n] be a sequence of vectors in a quadratic space W over F_q. For a, b ∈ F_q, Φ is called an (a, b)-equiangular system if: (i) ⟨ϕⱼ, ϕⱼ⟩ = a for every j ∈ [n], (ii) ⟨ϕᵢ, ϕⱼ⟩² = b for every i ≠ j in [n].” The sequence is represented by φ : Fin n → Fin d → F, the pairing by B, and the field parameters by a and b. Fin n indexes n vectors from zero; [n] in the paper indexes the same number from one. The predicate is polymorphic in the field and does not require its finiteness.

**Definition 1.3 (The unrestricted parameter identity).**

$$\operatorname{claim} = (\forall (F : \operatorname{Type}), [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] (\operatorname{ringChar}\left(F\right) \neq 2) \Rightarrow (\forall (d : \mathbb{N}), (2 \leq d) \Rightarrow (\forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}(F, (\operatorname{Fin}\left(d\right) \to F))), (B.\operatorname{IsSymm}) \Rightarrow ((B.\operatorname{Nondegenerate}) \Rightarrow (\forall (\varphi : (\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{choose}((d + 1), 2)\right) \to (\operatorname{Fin}\left(d\right) \to F))), \forall (a : F), \forall (b : F), (\operatorname{IsEquiangularSystem}\left(B, \varphi, a, b\right)) \Rightarrow ((a^{2} \neq b) \Rightarrow (a^{2} = ((d : F) + 2) \cdot b)))))))$$

*Formalization.* `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.claim` (`✓ std3`).

*Citation.* Gary R. W. Greaves, Joseph W. Iverson, John Jasper, Dustin G. Mixon (2021). *Frames over finite fields: Equiangular lines in orthogonal geometry*. DOI: [10.48550/arXiv.2012.13642](https://doi.org/10.48550/arXiv.2012.13642). URL: <https://arxiv.org/abs/2012.13642v2>.

*Commentary.*

Example 5.8, page 21: “The authors do not know how to construct an ETF with any of the parameters given in Table 4. In particular, every instance of Gerzon equality that we currently know satisfies the identity a² = (d + 2)b, but this equation does not occur anywhere in Table 4 (where b = 1). Proposition 2.10 implies that a² = (d + 2)b whenever Gerzon’s bound is saturated, d ≢ₚ 0, and d ≢ₚ 1. The authors do not know if these conditions can be removed.” Here F is finite, ringChar F differs from two, d is any natural number at least two, and B is symmetric and nondegenerate. The number of vectors is exactly Nat.choose (d + 1) 2, the Gerzon bound of Proposition 2.9. The inequality a² ≠ b is retained. Casting d into F precedes field addition and multiplication. There is no restriction on d modulo the characteristic. Proposition 2.10 supplies the earlier ETF parameter equation, while this statement asks for the identity without the two dimension congruences.

**Theorem 1.4 (Gerzon equality fixes the parameters).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/greaves-iverson-jasper-mixon-2021-gerzon-equality-identity` (proved) by `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"greaves-iverson-jasper-mixon-2021-gerzon-equality-identity","declaration_gid":"D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gary R. W. Greaves, Joseph W. Iverson, John Jasper, Dustin G. Mixon (2021). *Frames over finite fields: Equiangular lines in orthogonal geometry*. DOI: [10.48550/arXiv.2012.13642](https://doi.org/10.48550/arXiv.2012.13642). URL: <https://arxiv.org/abs/2012.13642v2>.

*Commentary.*

The statement holds, including dimensions congruent to zero or one in the field. An orthogonal basis reduces the form to diagonal coordinates. The rank-one operators either form a basis of the selfadjoint-matrix space or span its trace-zero hyperplane. Their fourth-moment operator has the form α·id + β·tr·I; comparison of a diagonal matrix unit and a symmetric off-diagonal pair forces α = 2β. The resulting parameter equation uses no division by d or d − 1. The proof also works over infinite fields of characteristic different from two. Dimension one is excluded: with one vector the off-diagonal equation has no instances, so b can vary independently of a.

## References

- Truth anchor: `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.IsEquiangularSystem`
- Truth anchor: `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.claim`
- Truth anchor: `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.gram_pair_sum`
- Truth anchor: `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result`
