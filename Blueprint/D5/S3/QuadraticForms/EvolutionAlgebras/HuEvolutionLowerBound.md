# Square-zero subspaces and evolution embedding dimension

## Abstract

A perfect complex bilinear algebra with a square-zero subspace of rank s requires at least d+s evolution coordinates.

**Definition 1.1 (Complex coordinate spaces).**

$$\forall d \in \mathbb{N},\; \operatorname{Coord}\left(d\right) = \operatorname{Fin}\left(d\right) \to \mathbb{C}$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Coord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dimension d is arbitrary, including zero.

**Definition 1.2 (Bilinear multiplication).**

$$\forall d \in \mathbb{N},\; \operatorname{Product}\left(d\right) = \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(d\right), \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(d\right), \operatorname{Coord}\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication is complex bilinear. Associativity and a unit are not assumed.

**Definition 1.3 (Span of all pair products).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; \forall U \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Coord}\left(d\right)\right),\; \operatorname{square}\left(mu, U\right) = \operatorname{span}\left(\mathbb{C}, \left\{mu\left(x, y\right) \mid (x,y) \in U \times U\right\}\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.square` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The span includes every product of two elements of U; U need not be an ideal or a coordinate subspace.

**Definition 1.4 (Commutativity).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; (\operatorname{commutative}\left(mu\right)) \Leftrightarrow (\forall x \in \operatorname{Coord}\left(d\right),\; \forall y \in \operatorname{Coord}\left(d\right),\; mu\left(x, y\right) = mu\left(y, x\right))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.commutative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This source hypothesis is retained explicitly, although the dimension-bound proof does not use it.

**Definition 1.5 (Perfectness).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; (\operatorname{perfect}\left(mu\right)) \Leftrightarrow (\operatorname{square}\left(mu, \operatorname{top}\right) = \operatorname{top})$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.perfect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Perfectness means that pair products span the entire intrinsic coordinate space.

**Definition 1.6 (An actual natural basis).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; (\operatorname{hasNaturalBasis}\left(mu\right)) \Leftrightarrow (\exists b \in \operatorname{Basis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, \operatorname{Coord}\left(d\right)\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; (i \ne j) \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.hasNaturalBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A basis has zero products between every pair of distinct basis vectors. Its squares may be dependent.

**Definition 1.7 (An actual evolution embedding).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; (\operatorname{hasEvolutionEmbedding}\left(mu, n\right)) \Leftrightarrow (\exists nu \in \operatorname{Product}\left(n\right),\; \exists f \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(d\right), \operatorname{Coord}\left(n\right)\right),\; (\operatorname{hasNaturalBasis}\left(nu\right)) \land ((\operatorname{Injective}\left(f\right)) \land (\forall x \in \operatorname{Coord}\left(d\right),\; \forall y \in \operatorname{Coord}\left(d\right),\; f\left(mu\left(x, y\right)\right) = nu\left(f\left(x\right), f\left(y\right)\right))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.hasEvolutionEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness includes a bilinear ambient multiplication, its natural basis and an injective complex-linear map preserving every pair product.

**Theorem 1.8 (The general dimension bound).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; \forall W \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Coord}\left(d\right)\right),\; (\operatorname{commutative}\left(mu\right)) \Rightarrow \left((\operatorname{perfect}\left(mu\right)) \Rightarrow \left((\operatorname{square}\left(mu, W\right) = \operatorname{bot}) \Rightarrow \left((\operatorname{hasEvolutionEmbedding}\left(mu, n\right)) \Rightarrow d + \operatorname{finrank}\left(\mathbb{C}, W\right) \le n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.square_zero_embedding_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xing-Yu Hu; Ran Wen (2026). *Idempotent-free non-solvable evolution algebras over C*. DOI: [10.48550/arXiv.2609.25023](https://doi.org/10.48550/arXiv.2609.25023). URL: <https://arxiv.org/abs/2609.25023v1>.

*Acknowledgement.* Cristina Costoya; Amir Fernández Ouaridi; Antonio Viruel (2026). *Commutative algebras are ideals of evolution algebras*. DOI: [10.48550/arXiv.2609.32784](https://doi.org/10.48550/arXiv.2609.32784). URL: <https://arxiv.org/abs/2609.32784v1>.

*Commentary.*

The bound and argument are credited to Wenlin Zhang and Haobo Ma, Structure tests for stable derived terms. Hu and Wen supply the stable-derived-term setting; Costoya, Fernández Ouaridi and Viruel supply related evolution-envelope methods. No priority claim is made.

In natural ambient coordinates write the product as M(x times y), with coordinatewise multiplication. Perfectness puts the embedded d-dimensional space into the range of M. Choose a vector in the embedded square-zero subspace that is nonzero on every coordinate appearing in its support. Such a vector exists over the infinite field of complex numbers, because finitely many proper coordinate kernels cannot cover the subspace. Coordinatewise multiplication by that vector is injective on the subspace, and its image lies in the kernel of M. Rank-nullity gives d plus finrank W at most n.

The bound holds for every complex linear W, including W equal to zero, and for d equal to zero. It assumes neither ideal nor hyperplane status for W, and does not require the ambient evolution algebra to be perfect.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Coord`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.Product`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.commutative`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.hasEvolutionEmbedding`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.hasNaturalBasis`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.perfect`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.square`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound.square_zero_embedding_lower_bound`
