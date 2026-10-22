# The full automorphism maximum

## Abstract

The partition weight is the attained maximum of the full automorphism orders of perfect complex evolution algebras in every positive finite dimension.

Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1, section 2.3, Conjecture 3, pages 27-28, conjecture that the maximum order in dimension n is the maximum over all multiplicities m_l with sum_l l m_l=n of product_l [l(2^l-1)]^(m_l) m_l!. The source states the attaining cyclic examples, and reports the upper bound checked only for n<=4. The assertion is conjectural in that source; the universal proof below is a separate result. No global priority claim is made.

**Theorem 1.1 (The universal bound and actual attainment).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\left(\forall A \in Type,\; \operatorname{FiniteDimensionalComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall I \in Type,\; \operatorname{Fintype}\left(I\right) \Rightarrow \left(\operatorname{finrank}\left(A\right) = n \Rightarrow \left(\forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \forall b \in \operatorname{Basis}\left(I, \mathbb{C}, A\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{productSpan}\left(mu\right) = Top \Rightarrow \left(\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right) \land \operatorname{NatCard}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{maximumWeight}\left(n\right)\right)\right)\right)\right)\right)\right) \land \left(\exists mu \in \operatorname{Product}\left(n\right),\; \operatorname{finrank}\left(\operatorname{Coord}\left(n\right)\right) = n \land \left(\operatorname{commutative}\left(mu\right) \land \left(\operatorname{hasNaturalBasis}\left(mu\right) \land \left(\operatorname{productSpan}\left(mu\right) = Top \land \left(\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right) \land \operatorname{NatCard}\left(\operatorname{Aut}\left(mu\right)\right) = \operatorname{maximumWeight}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/kaygorodov-martin-gonzalez-viruel-2026-evolution-automorphism-maximum` (proved) by `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kaygorodov-martin-gonzalez-viruel-2026-evolution-automorphism-maximum","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For every positive n, every arbitrary complex module of finrank n with any finite natural basis and with all pair products spanning the module has a finite full multiplication-preserving LinearEquiv group of order at most maximumWeight(n). For the same n there exists an actual commutative, perfect bilinear evolution product on Fin(n) to C, whose finrank is exactly n, with a natural basis and full automorphism order equal to maximumWeight(n). Associativity and a unit are never assumed. The bound retains all quotient fibers and their internal kernel. The attaining product sends e_i squared to e_(sigma(i)). Choose the identity for n=1 and every n>=7; one cycle of lengths 2, 3, and 5 in those dimensions; two 2-cycles in dimension 4; three 2-cycles in dimension 6. The exact full-group count follows from the constructed kernel and centralizer lifts. The existing arithmetic theorem gives the values 1, 6, 21, 72, 155, 1296 and n! for n>=7. The witnesses establish a maximum rather than merely an upper bound or a supremum. No realization of every integer partition is needed.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily](EvolutionPermutationFamily.md)
