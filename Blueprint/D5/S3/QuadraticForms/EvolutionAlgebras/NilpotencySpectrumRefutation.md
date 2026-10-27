# An ordinary nilpotency index outside the proposed binary spectrum

## Abstract

An ordinary nilpotency index outside the proposed binary spectrum.

**Definition 1.1 (productSpace).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall mu \in \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right),\; \forall U \in \operatorname{Submodule}\left(K, V\right),\; \forall W \in \operatorname{Submodule}\left(K, V\right),\; \operatorname{productSpace}\left(mu, U, W\right) = \operatorname{span}\left(K, \{z:V \mid \exists x \in V,\; \operatorname{mem}\left(x, U\right) \land \left(\exists y \in V,\; \operatorname{mem}\left(y, W\right) \land mu\left(x, y\right) = z\right)\}\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.productSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The product of two subspaces is the linear span of all products of their elements. Multiplication is bilinear; associativity is not assumed.

**Definition 1.2 (ordinaryPower).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall mu \in \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right),\; \operatorname{ordinaryPower}\left(mu, 0\right) = \operatorname{bot} \land \left(\operatorname{ordinaryPower}\left(mu, 1\right) = \operatorname{top} \land \left(\forall n \in \mathbb{N},\; \operatorname{ordinaryPower}\left(mu, n + 2\right) = \operatorname{iSup}\left(\operatorname{fun} (i:\operatorname{Fin}\left(n + 1\right)) \mapsto \operatorname{productSpace}\left(mu, \operatorname{ordinaryPower}\left(mu, \operatorname{val}\left(i\right) + 1\right), \operatorname{ordinaryPower}\left(mu, n + 1 - \operatorname{val}\left(i\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.ordinaryPower` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For degree n+2 the supremum runs over i from 0 through n. Thus it contains every split into the positive degrees i+1 and n+1-i. This is the ordinary lower series in section 1.1, including every parenthesization. The zeroth power is unused for positive k.

**Definition 1.3 (indexExists).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{indexExists}\left(K, n, k\right) = \left(\exists V \in \operatorname{Type},\; \exists [\operatorname{AddCommGroup}\left(V\right)], \exists [\operatorname{Module}\left(K, V\right)], \exists [\operatorname{FiniteDimensional}\left(K, V\right)], \exists mu \in \operatorname{LinearMap}\left(K, V, \operatorname{LinearMap}\left(K, V, V\right)\right),\; \operatorname{finrank}\left(K, V\right) = n \land \left(\operatorname{IsEvolutionAlgebra}\left(mu\right) \land \left(\operatorname{ordinaryPower}\left(mu, k + 1\right) = \operatorname{bot} \land \operatorname{ordinaryPower}\left(mu, k\right) \ne \operatorname{bot}\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.indexExists` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The existential quantifiers range over the vector space, its additive group and scalar module structures, its finite-dimensionality, and the bilinear product. The natural-basis predicate is the existing evolution-algebra definition: commutativity and a basis with zero mixed products. Zero squares are permitted.

**Definition 1.4 (predicted).**

$$\forall n \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \operatorname{predicted}\left(n, k\right) = \left(\left(\exists a \in \mathbb{N},\; k = 2^{a} \land \operatorname{Int}\left(a\right) \le n - 1\right) \lor \left(2 \le \operatorname{count}\left(\operatorname{digits}\left(2, \operatorname{toNat}\left(k\right)\right), 1\right) \land \operatorname{Int}\left(\operatorname{log}\left(2, \operatorname{toNat}\left(k\right)\right)\right) + \operatorname{Int}\left(\operatorname{count}\left(\operatorname{digits}\left(2, \operatorname{toNat}\left(k\right)\right), 1\right)\right) \le n - 1\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.predicted` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The first branch is a power of two. In the second branch the number of digits equal to one in the base-two expansion is at least two. The function log here means the integer floor of the base-two logarithm. The dimension bound is the integer n minus one. Int denotes the cast from natural numbers to integers; toNat converts the nonnegative integer argument to its natural-number representative.

**Definition 1.5 (claim).**

$$\operatorname{claim} = \left(\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Infinite}\left(K\right)] \forall n \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; 0 \le n \Rightarrow \left(1 \le k \Rightarrow \left(\operatorname{indexExists}\left(K, \operatorname{toNat}\left(n\right), \operatorname{toNat}\left(k\right)\right) \Leftrightarrow \operatorname{predicted}\left(n, k\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Conjecture 9 of Kaygorodov, Martin Gonzalez and Viruel, arXiv:2610.22248v1, section 2.3, asserts this equivalence for every infinite field and every nonnegative integer dimension n, at each positive integer k. The nilpotency index in its wording is k+1.

**Definition 1.6 (product).**

$$\forall x \in (\operatorname{Fin}\left(15\right) \to \mathbb{Q}),\; \forall y \in (\operatorname{Fin}\left(15\right) \to \mathbb{Q}),\; \operatorname{product}\left(x, y\right) = \operatorname{vector}\left(0, x\left(0\right) \cdot y\left(0\right), x\left(0\right) \cdot y\left(0\right), x\left(2\right) \cdot y\left(2\right) - x\left(1\right) \cdot y\left(1\right), x\left(0\right) \cdot y\left(0\right) + x\left(2\right) \cdot y\left(2\right) - x\left(1\right) \cdot y\left(1\right), x\left(4\right) \cdot y\left(4\right) - x\left(3\right) \cdot y\left(3\right), x\left(5\right) \cdot y\left(5\right), x\left(4\right) \cdot y\left(4\right) - x\left(3\right) \cdot y\left(3\right) + x\left(5\right) \cdot y\left(5\right), x\left(7\right) \cdot y\left(7\right) - x\left(6\right) \cdot y\left(6\right), x\left(8\right) \cdot y\left(8\right), x\left(9\right) \cdot y\left(9\right), x\left(10\right) \cdot y\left(10\right), x\left(11\right) \cdot y\left(11\right), x\left(7\right) \cdot y\left(7\right) - x\left(6\right) \cdot y\left(6\right) + x\left(11\right) \cdot y\left(11\right), x\left(13\right) \cdot y\left(13\right) - x\left(12\right) \cdot y\left(12\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.product` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

In one-based coordinates the natural square rows r are: e2+e3+e5; -e4-e5; e4+e5; -e6-e8; e6+e8; e7+e8; -e9-e14; e9+e14; e10; e11; e12; e13+e14; -e15; e15; 0. The displayed vector uses zero-based coordinate subscripts; the square-row description uses one-based subscripts. The standard coordinate vectors form a natural basis. All mixed products vanish.

**Theorem 1.7 (result).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kaygorodov-martin-gonzalez-viruel-2026-nilpotency-spectrum-conjecture-9` (refuted) by `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kaygorodov-martin-gonzalez-viruel-2026-nilpotency-spectrum-conjecture-9","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Over the infinite field Q this fifteen-dimensional algebra has A^256=0 and A^255 nonzero. The triangular spanning vectors, in order, are e1; e2+e3+e5; e3; e4+e5; e5; e6+e8; e7+e8+e9+e14; e8; e9+e14; e10+e15; e11; e12; e13+e14; e14; e15. Their weights are 1,2,1,3,1,5,10,1,15,30,60,120,240,1,255. Every nonzero product of two such vectors is another vector whose weight is at least the sum of the input weights. Bilinearity therefore gives F_r F_s contained in F_(r+s) for every positive r,s, where F_m spans vectors of weight at least m. Strong induction over all splits gives A^m contained in F_m; F_256 is zero. Starting from e1, and using e3 as the separate degree-one leaf at the second step, the input degree pairs are (1,1), (2,1), (3,2), (5,5), (10,5), (15,15), (30,30), (60,60), (120,120), (240,15). Their outputs are respectively the second, fourth, sixth, seventh, ninth, tenth, eleventh, twelfth, thirteenth and fifteenth spanning vectors. The final product has 255 leaves and equals e15. Hence the ordinary index is exactly 256. At k=255 there are eight one digits and floor(log2(k))=7; their sum 15 exceeds n-1=14, and k is not a power of two. Existence is true and both arithmetic alternatives are false.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.indexExists`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.ordinaryPower`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.predicted`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.product`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.productSpace`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
