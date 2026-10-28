# Minimal perfect Jordan-block algebras

## Abstract

Every positive Jordan-block family member is minimal perfect, lacks a natural basis and attains its exact evolution embedding dimension.

**Definition 1.1 (Minimality among all complex subspaces).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; (\operatorname{minimalPerfect}\left(mu\right)) \Leftrightarrow ((\operatorname{perfect}\left(mu\right)) \land (\forall U \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Coord}\left(d\right)\right),\; (U \ne \operatorname{bot}) \Rightarrow \left((\operatorname{square}\left(mu, U\right) = U) \Rightarrow U = \operatorname{top}\right)))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.minimalPerfect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every nonzero complex linear subspace is included, rather than just ideals or coordinate spans.

**Definition 1.2 (Attained minimal dimension).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; \forall n \in \mathbb{N},\; (\operatorname{isEmbeddingDimension}\left(mu, n\right)) \Leftrightarrow ((\operatorname{hasEvolutionEmbedding}\left(mu, n\right)) \land (\forall q \in \mathbb{N},\; (\operatorname{hasEvolutionEmbedding}\left(mu, q\right)) \Rightarrow n \le q))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.isEmbeddingDimension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first conjunct provides an actual embedding. The second bounds every possible ambient dimension.

**Definition 1.3 (Both stable-square equalities).**

$$\forall d \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(d\right),\; \forall n \in \mathbb{N},\; (\operatorname{hasStableSquareEmbedding}\left(mu, n\right)) \Leftrightarrow (\exists nu \in \operatorname{Product}\left(n\right),\; \exists f \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(d\right), \operatorname{Coord}\left(n\right)\right),\; ((\operatorname{hasNaturalBasis}\left(nu\right)) \land ((\operatorname{Injective}\left(f\right)) \land (\forall x \in \operatorname{Coord}\left(d\right),\; \forall y \in \operatorname{Coord}\left(d\right),\; f\left(mu\left(x, y\right)\right) = nu\left(f\left(x\right), f\left(y\right)\right)))) \land ((\operatorname{square}\left(nu, \operatorname{top}\right) = \operatorname{range}\left(f\right)) \land (\operatorname{square}\left(nu, \operatorname{range}\left(f\right)\right) = \operatorname{range}\left(f\right))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.hasStableSquareEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witnesses are an actual bilinear evolution law and an injective complex-linear multiplication-preserving map. Both the square of the ambient space and the square of the embedded range equal that range.

**Definition 1.4 (The source coordinate law).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Coord}\left(m + 1\right),\; \forall y \in \operatorname{Coord}\left(m + 1\right),\; \forall k \in \operatorname{Fin}\left(m + 1\right),\; \operatorname{jordanProduct}\left(m, x, y\right)\left(k\right) = \operatorname{ite}\left(\operatorname{val}\left(k\right) = 0, 4 \cdot x\left(0\right) \cdot y\left(0\right), 2 \cdot x\left(0\right) \cdot y\left(k\right) + 2 \cdot x\left(k\right) \cdot y\left(0\right) + \operatorname{ite}\left(\operatorname{val}\left(k\right) + 1 < m + 1, 2 \cdot x\left(0\right) \cdot y\left(\operatorname{val}\left(k\right) + 1\right) + 2 \cdot x\left(\operatorname{val}\left(k\right) + 1\right) \cdot y\left(0\right), 0\right) + \operatorname{ite}\left(\operatorname{val}\left(k\right) = m, 2 \cdot x\left(0\right) \cdot y\left(0\right), 0\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordanProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate zero is u, and coordinate i is wi for 1 through m. For m at least one: u squared is 4u plus 2wm; uwi and wiu are 2wi plus 2w(i−1); wiwj is zero, with w0 zero. The next coordinate is evaluated only in the branch where its integer index is in range. The conditional formula also defines the dimension-one induction base without making a no-natural-basis claim there.

**Definition 1.5 (Equality with the source law).**

$$\forall m \in \mathbb{N},\; \forall mu \in \operatorname{Product}\left(m + 1\right),\; (\operatorname{jordanLaw}\left(m, mu\right)) \Leftrightarrow (\forall x \in \operatorname{Coord}\left(m + 1\right),\; \forall y \in \operatorname{Coord}\left(m + 1\right),\; mu\left(x, y\right) = \operatorname{jordanProduct}\left(m, x, y\right))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordanLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is equality on all pairs of coordinate vectors, not just a table asserted without bilinearity.

**Definition 1.6 (The bilinear implementation).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Coord}\left(m + 1\right),\; \forall y \in \operatorname{Coord}\left(m + 1\right),\; \operatorname{jordan}\left(m\right)\left(x, y\right) = \operatorname{jordanProduct}\left(m, x, y\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Lean construction supplies the four linearity proofs needed to inhabit Product(m+1).

**Definition 1.7 (A linear structure map defines an evolution product).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(n\right), \operatorname{Coord}\left(n\right)\right),\; \forall x \in \operatorname{Coord}\left(n\right),\; \forall y \in \operatorname{Coord}\left(n\right),\; \operatorname{coordinateProduct}\left(M\right)\left(x, y\right) = M\left(x \cdot y\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinateProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any complex linear structure map M, multiply coordinates first and then apply M. This gives a bilinear product with zero mixed standard-basis products.

**Theorem 1.8 (The standard coordinate law has a natural basis).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(n\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{hasNaturalBasis}\left(\operatorname{coordinateProduct}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinate_product_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate basis is natural for every linear structure map: the coordinatewise product of distinct coordinate vectors is zero.

**Theorem 1.9 (The entire product span is the structure-map range).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Coord}\left(n\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{square}\left(\operatorname{coordinateProduct}\left(M\right), \operatorname{top}\right) = \operatorname{range}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinate_product_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair product lies in range(M). Conversely each image of a coordinate vector is its square and these images span range(M). Thus invertible structure maps give perfect products.

**Theorem 1.10 (The complete positive family and its exact embedding dimension).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow \left(\exists mu \in \operatorname{Product}\left(m + 1\right),\; (\operatorname{jordanLaw}\left(m, mu\right)) \land ((\operatorname{commutative}\left(mu\right)) \land ((\operatorname{minimalPerfect}\left(mu\right)) \land ((\neg \operatorname{hasNaturalBasis}\left(mu\right)) \land ((\operatorname{hasStableSquareEmbedding}\left(mu, 2 \cdot m + 1\right)) \land (\operatorname{isEmbeddingDimension}\left(mu, 2 \cdot m + 1\right))))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordan_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xing-Yu Hu; Ran Wen (2026). *Idempotent-free non-solvable evolution algebras over C*. DOI: [10.48550/arXiv.2609.25023](https://doi.org/10.48550/arXiv.2609.25023). URL: <https://arxiv.org/abs/2609.25023v1>.

*Acknowledgement.* Yolanda Cabrera Casado; Mercedes Siles Molina; M. Victoria Velasco (2017). *Description of three-dimensional evolution algebras*. DOI: [10.48550/arXiv.1701.07219](https://doi.org/10.48550/arXiv.1701.07219). URL: <https://arxiv.org/abs/1701.07219v2>.

*Acknowledgement.* Cristina Costoya; Amir Fernández Ouaridi; Antonio Viruel (2026). *Commutative algebras are ideals of evolution algebras*. DOI: [10.48550/arXiv.2609.32784](https://doi.org/10.48550/arXiv.2609.32784). URL: <https://arxiv.org/abs/2609.32784v1>.

*Commentary.*

The family and its realization are credited to Wenlin Zhang and Haobo Ma, Structure tests for stable derived terms. Related literature is Hu and Wen, arXiv:2609.25023v1; Cabrera Casado, Siles Molina and Velasco, arXiv:1701.07219v2; and Costoya, Fernández Ouaridi and Viruel, arXiv:2609.32784v1. The formalization makes no global priority claim.

Left multiplication by u has invertible diagonal entries and a nilpotent shift, so products span the intrinsic space. For minimality, drop the first square-zero coordinate w1 and induct on m. A nonzero perfect subspace has a nonzero perfect image, which equals the quotient by induction. Lift u, then recover w1 by subtracting 4x from x squared in the smallest case, or by subtracting 2y from xy using a lifted w2. The subspace then contains the kernel and maps onto the quotient, so it is the whole space.

Map intrinsic coordinates x to x0 followed by all x0+xi and all x0−xi. This is injective. An intrinsic coefficient map sends coordinatewise products of embedded vectors to their intrinsic product. Compose that coefficient map with the embedding to prescribe the ambient basis squares. Mixed standard-basis products vanish. Surjectivity of the coefficient map makes the entire ambient square equal the embedded range; perfectness and product preservation give the second stable-square equality.

The square-zero hyperplane has rank m. The general lower bound therefore gives 2m+1 for every evolution embedding. The explicit construction attains it, and rules out an intrinsic natural basis whenever m is at least one. Jordan-block names a nilpotent block, not a Jordan algebra identity. Neither the general idempotent obstruction nor the general nilpotent/cyclic classification is assumed or proved here.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinateProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinate_product_natural`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.coordinate_product_square`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.hasStableSquareEmbedding`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.isEmbeddingDimension`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordan`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordanLaw`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordanProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.jordan_family`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily.minimalPerfect`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound](HuEvolutionLowerBound.md)
