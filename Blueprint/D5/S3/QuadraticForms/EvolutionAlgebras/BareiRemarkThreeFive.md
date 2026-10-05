# A three-dimensional minimal idempotent subspace

## Abstract

A five-dimensional complex evolution algebra contains a three-dimensional idempotent subspace with no nonzero proper idempotent subspace. This answers the existence search in Barei's Remark 3.5.

**Definition 1.1 (The ambient complex vector space).**

$$E = (\operatorname{Fin}\left(5\right) \to \mathbb{C})$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient vector space has five complex coordinates. The product used in the theorem is bilinear and has an actual natural basis; associativity and a unit are not imposed.

**Definition 1.2 (The square of a subspace).**

$$\forall \mu : E \to_{\mathbb{C}} E \to_{\mathbb{C}} E, \forall U \in \operatorname{Submodule}\left(\mathbb{C}, E\right),\; \operatorname{Square}\left(\mu, U\right) = \left(\operatorname{span}_{\mathbb{C}}\right)\left(\{z \in E \mid \exists x \in U,\; \exists y \in U,\; \mu\left(x, y\right) = z\}\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.Square` (`✓ std3`).

*Citation.* Andres Barei (with Muse Spark via meta.ai; reviewed by Nicolás Jaramillo Torres) (2026). *On solvable evolution algebras and a conjecture by García-Martínez and Pérez-Rodríguez*. URL: <https://ai.meta.com/research/publications/on-solvable-evolution-algebras-and-a-conjecture-by-garcia-martinez-and-perez-rodriguez/>.

*Commentary.*

The square is the complex linear span of every product of two vectors from the subspace. Idempotence means equality to the subspace. This is a property of subspaces, rather than a restriction to coordinate spans or to idempotent elements.

**Theorem 1.3 (Affirmative answer to Remark 3.5).**

$$\exists \mu : E \to_{\mathbb{C}} E \to_{\mathbb{C}} E, \exists b \in \left(\operatorname{Basis}_{\mathbb{C}}\right)\left(\operatorname{Fin}\left(5\right), E\right),\; \exists V \in \operatorname{Submodule}\left(\mathbb{C}, E\right),\; (\left(\operatorname{finrank}_{\mathbb{C}}\right)\left(E\right) = 5) \land ((\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; (i \ne j) \Rightarrow \mu\left(b\left(i\right), b\left(j\right)\right) = 0) \land ((\left(\operatorname{finrank}_{\mathbb{C}}\right)\left(V\right) = 3) \land ((\operatorname{Square}\left(\mu, V\right) = V) \land (\forall U \in \operatorname{Submodule}\left(\mathbb{C}, E\right),\; (U \leq V) \Rightarrow \left((U \ne \left\{0\right\}) \Rightarrow \left((\operatorname{Square}\left(\mu, U\right) = U) \Rightarrow U = V\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result` (`✓ std3`). ∎

*Resolves.* `Problems/barei-2026-remark-3-5-minimal-idempotent` (proved) by `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barei-2026-remark-3-5-minimal-idempotent","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andres Barei (with Muse Spark via meta.ai; reviewed by Nicolás Jaramillo Torres) (2026). *On solvable evolution algebras and a conjecture by García-Martínez and Pérez-Rodríguez*. URL: <https://ai.meta.com/research/publications/on-solvable-evolution-algebras-and-a-conjecture-by-garcia-martinez-and-perez-rodriguez/>.

*Acknowledgement.* Xing-Yu Hu; Ran Wen (2026). *Idempotent-free non-solvable evolution algebras over C*. DOI: [10.48550/arXiv.2609.25023](https://doi.org/10.48550/arXiv.2609.25023). URL: <https://arxiv.org/abs/2609.25023v1>.

*Acknowledgement.* Cristina Costoya; Amir Fernández Ouaridi; Antonio Viruel (2026). *Commutative algebras are ideals of evolution algebras*. DOI: [10.48550/arXiv.2609.32784](https://doi.org/10.48550/arXiv.2609.32784). URL: <https://arxiv.org/abs/2609.32784v1>.

*Commentary.*

Choose natural basis e1 through e5. Put u equal to their sum, v equal to e2 minus e3, and w equal to e4 minus e5. The basis squares are 4u + 2w, v, -v, v + w, and -v - w; mixed basis products vanish. The injective linear map (a,b,c) to (a,a+b,a-b,a+c,a-c) identifies its range with the span of u,v,w and preserves multiplication.

In intrinsic coordinates, the products are u squared equal to 4u + 2w, uv equal to 2v, uw equal to 2v + 2w, and all products in the plane spanned by v,w equal to zero. These products span the whole three-dimensional space, so its square equals itself.

Let a multiplication-closed subspace contain x = au + bv + cw with a nonzero. Set s = x squared minus 4ax. Then s = 4acv + 2a squared w and xs - 2as = 4a cubed v. Dividing by nonzero coefficients puts v, then w, then u in the subspace. All remaining subalgebras lie in the square-zero plane. Therefore every nonzero idempotent subspace of the range equals the range. The quantifier includes every complex linear subspace.

The question is credited to Barei with Muse Spark. Hu and Wen's related counterexamples and Costoya, Fernández Ouaridi and Viruel's evolution-envelope framework are prior literature. The general-dimensional family and its embedding bound are written arguments in the dossier, not additional Lean theorems in this module.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.E`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.Square`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result`
