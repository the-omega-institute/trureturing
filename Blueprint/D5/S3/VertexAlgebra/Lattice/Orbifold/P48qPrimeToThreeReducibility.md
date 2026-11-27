# Rational Reducibility for Prime-to-Three Subgroups of SL₂(F₄₇)

## Abstract

Every faithful rational representation in dimension 48 of a subgroup of SL₂(F₄₇) whose order is prime to three has a nonzero proper invariant subspace.

Nebe identifies the automorphism group of the rank-48 extremal lattice P48q in Table 1 of arXiv:1312.3780. The reducibility argument concerns rational representations of its subgroups.

**Theorem 1.1 (Cyclotomic degree divides rational dimension).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime and let T be a rational linear endomorphism with Tᵖ = 1 and ker(T − 1) = 0. Then p − 1 divides the rational finrank. Factoring Xᵖ − 1 and using injectivity of T − 1 shows that the p-th cyclotomic polynomial annihilates T. The resulting action of the cyclotomic field makes its degree p − 1 a divisor of the finrank.

**Theorem 1.2 (An order bound or a normal cyclic subgroup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.card_le_32_or_exists_normal_zpowers`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.card_le_32_or_exists_normal_zpowers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite group whose order divides 32 × 23 × 47 has order at most 32 or has a normal cyclic subgroup of order 23 or 47. If 47 divides the order, the number of Sylow 47-subgroups divides 32 × 23 and is congruent to one modulo 47. Only one meets both conditions. After excluding 47, the same argument uses divisors of 32 modulo 23.

**Theorem 1.3 (An invariant subspace from the order divisor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.exists_invariant_subspace_of_card_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.exists_invariant_subspace_of_card_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite group of order dividing 32 × 23 × 47 act faithfully on a 48-dimensional rational vector space. For order at most 32, the orbit span of a nonzero vector is invariant and has dimension at most 32. Otherwise the fixed space of the normal cyclic subgroup is invariant. It is nonzero because neither 22 nor 46 divides 48, and proper because the action is faithful.

**Theorem 1.4 (Reducibility for subgroups of SL₂(F₄₇)).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.sl47_prime_to_three_exists_invariant_subspace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.sl47_prime_to_three_exists_invariant_subspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

Let H be a subgroup of SL₂(F₄₇) with order prime to three. Every faithful rational representation of H of dimension 48 has a nonzero proper subspace preserved by every element of H. The ambient order is 3 × 32 × 23 × 47. The subgroup order divides it and is coprime to three, so the previous order-divisibility result applies.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.card_le_32_or_exists_normal_zpowers`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.exists_invariant_subspace_of_card_dvd`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.sl47_prime_to_three_exists_invariant_subspace`
