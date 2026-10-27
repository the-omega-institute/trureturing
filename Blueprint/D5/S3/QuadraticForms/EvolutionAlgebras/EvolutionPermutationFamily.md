# Attaining permutation algebras

## Abstract

Coefficient-one permutation evolution algebras realize the complete root kernel and permutation centralizer.

**Theorem 1.1 (permutationLinear_basis).**

$$\forall (n : \mathbb{N}), (\forall (sigma : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (i : \operatorname{Fin}\left(n\right)), (\operatorname{permutationLinear}\left(sigma\right)\left(\operatorname{Pi}.\operatorname{basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\left(i\right)\right) = (\operatorname{Pi}.\operatorname{basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\left(sigma\left(i\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate permutation sends each coordinate basis vector to the basis vector at its permuted index.

**Theorem 1.2 (permutation_mixed).**

$$\forall (n : \mathbb{N}), (\forall (sigma : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (i : \operatorname{Fin}\left(n\right)), (\forall (j : \operatorname{Fin}\left(n\right)), ((i \ne j) \Rightarrow (\operatorname{permutationProduct}\left(sigma\right)\left(\operatorname{Pi}.\operatorname{basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\left(i\right), \operatorname{Pi}.\operatorname{basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right)\left(j\right)\right) = (0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct coordinate basis vectors have zero product.

**Theorem 1.3 (permutation_support).**

$$\forall (n : \mathbb{N}), (\forall (sigma : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (i : \operatorname{Fin}\left(n\right)), (\forall (j : \operatorname{Fin}\left(n\right)), (\operatorname{supportRelation}\left(\operatorname{permutationProduct}\left(sigma\right), \operatorname{Pi}.\operatorname{basisFun}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right), i, j\right) \Leftrightarrow j = (sigma\left(i\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arrow of the coefficient-one permutation product goes exactly from an index to its image under the permutation.

**Definition 1.4 (The coordinate permutation).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall x \in \operatorname{Coord}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{coordinate}\left(\operatorname{apply}\left(\operatorname{permutationLinear}\left(sigma\right), x\right), j\right) = \operatorname{coordinate}\left(x, \operatorname{inverseApply}\left(sigma, j\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear equivalence P_sigma sends coordinate vector e_i to e_(sigma(i)); its j-th output coordinate is x_(sigma inverse(j)).

**Definition 1.5 (The bilinear evolution law).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall x \in \operatorname{Coord}\left(n\right),\; \forall y \in \operatorname{Coord}\left(n\right),\; \operatorname{ApplyProduct}\left(\operatorname{permutationProduct}\left(sigma\right), x, y\right) = \operatorname{apply}\left(\operatorname{permutationLinear}\left(sigma\right), x \cdot y\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationProduct` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The product is P_sigma applied to coordinatewise multiplication. The original coordinateProduct construction supplies bilinearity. Its basis squares are e_i squared=e_(sigma(i)) and distinct basis vectors multiply to zero. The structure map is invertible, so all pair products span the whole space.

**Definition 1.6 (Every commuting permutation lifts).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall tau \in \operatorname{centralizer}\left(sigma\right),\; \operatorname{Member}\left(\operatorname{centralizerLift}\left(sigma, tau\right), \operatorname{Aut}\left(\operatorname{permutationProduct}\left(sigma\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.centralizerLift` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For each tau commuting with sigma, P_tau preserves the product on all vector pairs. It is therefore an actual member of the full LinearEquiv automorphism group. Its support permutation is tau itself. These explicit lifts prove equality of the actual projection image and the full centralizer.

**Theorem 1.7 (Exact full-group cardinality).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Finite}\left(\operatorname{Aut}\left(\operatorname{permutationProduct}\left(sigma\right)\right)\right) \land \operatorname{NatCard}\left(\operatorname{Aut}\left(\operatorname{permutationProduct}\left(sigma\right)\right)\right) = \operatorname{weight}\left(\operatorname{parts}\left(\operatorname{partition}\left(sigma\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_aut_card` (`✓ std3`). ∎

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The entire algebra group is finite. Monomiality identifies its actual permutation image; preservation of basis squares forces that image to commute with sigma, and the lifts prove the converse inclusion. The actual kernel is exactly the unit assignments a_(sigma(i))=a_i squared. Existing independent cycle-root realization counts it, including the singleton root factor one. Kernel cardinality times image cardinality is therefore the full partition weight, with every singleton multiplicity factorial retained. The source states attainment by sums of cyclic algebras; this proof derives the exact cardinality directly without assuming a wreath-product classification.

**Theorem 1.8 (All algebraic witness conditions).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{commutative}\left(\operatorname{permutationProduct}\left(sigma\right)\right) \land \left(\operatorname{hasNaturalBasis}\left(\operatorname{permutationProduct}\left(sigma\right)\right) \land \left(\operatorname{perfect}\left(\operatorname{permutationProduct}\left(sigma\right)\right) \land \left(\operatorname{Finite}\left(\operatorname{Aut}\left(\operatorname{permutationProduct}\left(sigma\right)\right)\right) \land \operatorname{NatCard}\left(\operatorname{Aut}\left(\operatorname{permutationProduct}\left(sigma\right)\right)\right) = \operatorname{weight}\left(\operatorname{parts}\left(\operatorname{partition}\left(sigma\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_family` (`✓ std3`). ∎

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Every permutation gives a commutative, perfect complex evolution algebra on Fin(n) to C. It need not be associative. Naturality and perfection use the original coordinate-product facts. The same actual algebra and same full automorphism group satisfy the exact order formula.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.centralizerLift`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationLinear_basis`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutationProduct`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_aut_card`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_family`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_mixed`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily.permutation_support`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound](EvolutionSharpBound.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily](HuEvolutionJordanFamily.md)
