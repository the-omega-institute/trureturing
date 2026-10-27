# The simple evolution algebra automorphism maximum

## Abstract

The full automorphism maximum for simple complex evolution algebras.

A complex evolution algebra has a finite natural basis with zero mixed products. Its multiplication need not be associative or unital. The full automorphism group consists of all complex linear equivalences preserving multiplication on every pair of vectors.

**Definition 1.1 (Simplicity).**

$$\forall (A : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(A\right)] [\operatorname{Module}\left(\mathbb{C}, A\right)] \forall (mu : \operatorname{LinearMap}\left(\mathbb{C}, A, \operatorname{LinearMap}\left(\mathbb{C}, A, A\right)\right)), (\operatorname{IsSimple}\left(mu\right) = ((\operatorname{productSpan}\left(mu\right) \ne \operatorname{Bot}.\operatorname{bot}) \land (\forall (J : \operatorname{Submodule}\left(\mathbb{C}, A\right)), ((\forall (x : A), ((x \in J) \Rightarrow (\forall (y : A), ((mu\left(x, y\right) \in J) \land (mu\left(y, x\right) \in J))))) \Rightarrow ((J = (\operatorname{Bot}.\operatorname{bot})) \lor (J = (\operatorname{Top}.\operatorname{top}))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.IsSimple` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The survey's Theorem 6 uses simplicity in the usual ideal sense. Its cited Cabrera Casado, Siles Molina and Velasco source, arXiv:1601.01832v2, section 4, page 18, states: “We recall that an algebra A is simple if A² ≠ 0 and 0 is the only proper ideal.” Here A² is productSpan, and ideals are all complex vector subspaces absorbing products on both sides. They are not restricted to spans of natural-basis vectors.

**Definition 1.2 (Conjecture 4).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), ((1 \le n) \Rightarrow ((\forall (A : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(A\right)] [\operatorname{Module}\left(\mathbb{C}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, A\right)] \forall (I : \operatorname{Type}), ([\operatorname{Fintype}\left(I\right)] \forall (mu : \operatorname{LinearMap}\left(\mathbb{C}, A, \operatorname{LinearMap}\left(\mathbb{C}, A, A\right)\right)), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, \mathbb{C}, A\right)), ((\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, A\right) = (n)) \Rightarrow ((\forall (i : I), (\forall (j : I), ((i \ne j) \Rightarrow (mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (x : A), (\forall (y : A), (mu\left(x, y\right) = (mu\left(y, x\right))))) \Rightarrow ((\operatorname{IsSimple}\left(mu\right)) \Rightarrow ((\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right)) \land (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{max}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right), n \cdot (2^{n} - 1)\right))))))))))) \land (\exists (mu : \operatorname{Product}\left(n\right)), ((\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, \operatorname{Coord}\left(n\right)\right) = (n)) \land ((\operatorname{commutative}\left(mu\right)) \land ((\operatorname{hasNaturalBasis}\left(mu\right)) \land ((\operatorname{IsSimple}\left(mu\right)) \land ((\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right)) \land (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) = (\operatorname{max}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right), n \cdot (2^{n} - 1)\right))))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Conjecture 4, section 2.3, page 28: “Over ℂ, the maximal order of the automorphism group of a simple n-dimensional evolution algebra is max{n!, n(2ⁿ−1)}.” The dimension n is positive. The universal part ranges over arbitrary complex vector spaces A, finite index types I, bilinear products mu and natural bases b, with finrank equal to n. The existential part gives a product on Coord n attaining the bound. Finite is stated before Nat.card, so an infinite group cannot meet the bound by having natural cardinality zero.

**Theorem 1.3 (The attained maximum).**

$$\forall (n : \mathbb{N}), ((1 \le n) \Rightarrow ((\forall (A : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(A\right)] [\operatorname{Module}\left(\mathbb{C}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, A\right)] \forall (I : \operatorname{Type}), ([\operatorname{Fintype}\left(I\right)] \forall (mu : \operatorname{LinearMap}\left(\mathbb{C}, A, \operatorname{LinearMap}\left(\mathbb{C}, A, A\right)\right)), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, \mathbb{C}, A\right)), ((\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, A\right) = (n)) \Rightarrow ((\forall (i : I), (\forall (j : I), ((i \ne j) \Rightarrow (mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (x : A), (\forall (y : A), (mu\left(x, y\right) = (mu\left(y, x\right))))) \Rightarrow ((\operatorname{IsSimple}\left(mu\right)) \Rightarrow ((\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right)) \land (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{max}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right), n \cdot (2^{n} - 1)\right))))))))))) \land (\exists (mu : \operatorname{Product}\left(n\right)), ((\operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, \operatorname{Coord}\left(n\right)\right) = (n)) \land ((\operatorname{commutative}\left(mu\right)) \land ((\operatorname{hasNaturalBasis}\left(mu\right)) \land ((\operatorname{IsSimple}\left(mu\right)) \land ((\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right)) \land (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) = (\operatorname{max}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right), n \cdot (2^{n} - 1)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/kmvc4-simpleaut` (proved) by `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kmvc4-simpleaut","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Simplicity forces the support graph to be strongly connected. Every support path projects to an orbit of the successor permutation on the least successor-compatible quotient, so this permutation has a single orbit. Invertibility of the structure map supplies a permutation supported on the arrows. Restricting it to consecutive quotient fibers gives bijections, forcing every fiber to have the same positive size k. If the quotient has h elements, then n=hk.

The joint bound for the actual algebra group becomes h(2ʰ−1)(k!)ʰ. For h,k at least two, an induction using ascending factorials bounds this by (hk)!. The cases h=1 and k=1 give n! and n(2ⁿ−1), respectively. The argument uses the actual kernel and permutation image of the same algebra.

The cyclic product has full group order n(2ⁿ−1). The product with structure matrix I+J, where every entry of J is one, is simple and has full group order n!: every permutation lifts, while loops force every diagonal automorphism to be the identity. Choosing the larger family proves attainment in every positive dimension, including dimension one. The upper-bound argument also works without a separate commutativity hypothesis when the mixed products of a finite natural basis vanish.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.IsSimple`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily](EvolutionPermutationFamily.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks](NondegenerateDerivationBlocks.md)
