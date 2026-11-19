# Splitting the paper's symmetric-power coefficient submodule

## Abstract

The coefficient-sum copy of V_(pk+1) is an actual equivariant direct summand of Sym^k(V_(p+1)) for every 1<=k<p.

The external target is the unnumbered direct-summand question immediately after Lemma 3.9 in Section 3.2 of Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, arXiv:2510.07939v1, DOI 10.1007/s13366-026-00855-9. The retrieved primary text states that S^k(V_(p+1)) contains a copy of V_(pk+1) for k<p but that it is not clear whether this is a direct summand. This is an actual splitting question, separate from the binary relative tensor Conjecture 3.7. No worldwide novelty or priority claim is made.

**Theorem 1.1 (Iterated bounded polarization has factorial scalar).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_block_polarization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_block_polarization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, a characteristic-p field K and every positive k, the theorem constructs an equivariant ordered tensor map delta from polynomials of degree at most pk to the k-fold tensor power of polynomials of degree at most p. Ordinary multiplication mu composed with delta equals (k!:K) times the identity. This denominator-free identity includes k>=p, where it gives no splitting assertion.

The construction iterates the existing BoundedTensorPolarization map at degrees p and np. Its multiplication scalar is choose((n+1)p,p). The already proved low-digit binomial identity identifies that scalar with n+1 in K. Induction gives k!, and every tensor reassociation and diagonal action is constructed through the tensor universal properties.

**Theorem 1.2 (The polynomial coefficient inclusion splits).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_polynomial_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_polynomial_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 1<=k<p, k! is nonzero in K. Normalizing the constructed block polarization gives an actual equivariant section of polynomial multiplication. Multiplication is invariant under factor permutations. The quotient-averaging theorem therefore constructs an actual equivariant retraction of the unnormalized ordered coefficient inclusion V_(pk+1)->Sym^k(V_(p+1)). There is no finite-field or finite-group hypothesis and no additional comparison between polynomial degree and group order; the displayed 1<=k<p restriction remains. No tensor section is assumed by this theorem.

**Theorem 1.3 (The author's submodule splits for the original W).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.coefficient_sum_is_actual_summand`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.coefficient_sum_is_actual_summand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any characteristic-p field, E a nontrivial additive commutative group of exponent p, and rho a faithful representation of E on a two-dimensional K-vector space W. Define V_d as the ordinary contragredient of the genuine quotient SymmetricPower K (Fin (d-1)) W. For every 1<=k<p, the theorem constructs an equivariant injection i:V_(pk+1)->Sym^k(V_(p+1)) and an equivariant retraction r with r i=id. It also proves that the range of i is exactly the span of the paper's ordered coefficient sums, including all multiplicities and signs. Thus it identifies the specified submodule, rather than only some isomorphic summand.

Faithfulness and the exponent-p action supply a two-vector unipotent basis and an injective additive alpha:E->K. The proved genuine symmetric-power coordinate equivalences transport the constructed polynomial inclusion and retraction to the original W. On the transported dual monomial bases, the inclusion maps each basis vector to the exact ordered coefficient sum. Multiplying each degree-j generator by (-1)^j matches the signed generators; equivalently, the sign is distributed across every factor of each degree-j word. These nonzero signs preserve the span. The basis, alpha, maps, left inverse and image equality are conclusions, never caller hypotheses.

The original finite elementary abelian range q>=p^2 is included, since k<p implies pk+1<=q there. The proof itself needs no cardinality bound or finite-field assumption. The current Fin-index Mathlib quotient forces K:Type; E and W retain independent universes. Only k! is inverted. There is no inversion of p!, no negligible-map replacement, and no assumption that a relative stable equivalence is an actual direct summand.

The auxiliary typed DependentFamily registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/30512. No declared_validated status is asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.coefficient_sum_is_actual_summand`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_block_polarization`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting.exists_polynomial_retraction`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion](ElmerKadrResidueCriterion.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification](EmbeddedOriginalClassification.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting](SymmetricPowerBlockSplitting.md)
