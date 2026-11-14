# Cyclic Projectivity over a Finite Coefficient Field

## Abstract

Prime-field restriction and one actual cyclic norm give the finite-coefficient-field ceiling bound.

Let p be prime, let K be any finite field of characteristic p, and write f=finrank over ZMod p of K using the canonical algebra ZMod.algebra K p. Let E be the actual group Multiplicative (Fin r → ZMod p). For a nonzero finite-dimensional K-vector space V with an actual representation rho of E, assume that restriction to every actual cyclic subgroup H is projective over K[H]. The result is p*ceil(r/f) ≤ finrank_K V. The field and vector-space universes are independent.

**Theorem 1.1 (The finite-field ceiling lower bound).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension.prime_mul_ceilDiv_finrank_le_finrank_of_cyclic_projective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension.prime_mul_ceilDiv_finrank_le_finrank_of_cyclic_projective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact public telescope (independent universes uK uV): (p r : ℕ) [Fact p.Prime] {K : Type uK} [Field K] [Finite K] [CharP K p] {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K (Multiplicative (Fin r → ZMod p)) V) (hproj : ∀ H : Subgroup (Multiplicative (Fin r → ZMod p)), IsCyclic H → Module.Projective K[H] (Representation.asModule (ρ.comp H.subtype))) : letI : Algebra (ZMod p) K := ZMod.algebra K p; p * (r ⌈/⌉ Module.finrank (ZMod p) K) ≤ Module.finrank K V. No additional algebra, scalar tower, coefficient-projectivity, scalar-restricted projectivity, faithfulness or local-freeness hypothesis is present.

The private primeRestriction restricts each actual rho(g) by LinearMap.restrictScalars. Its underlying vector action is unchanged. For any actual finite subgroup, its invariant predicate is therefore literally the same predicate on V. The consumed private primeRestriction_norm proves equality of the two actual unnormalised norms by expanding the finite sums. The consumed private primeRestriction_projective takes norm-surjectivity from the necessary K direction of PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective with exponent a=1. It regards each prime-field invariant as the same K-invariant vector and transfers its norm preimage. Every prime-field invariant space is an ordinary vector space, hence free and projective; the sufficient prime-field direction of the same public criterion then gives actual ZMod p[H]-projectivity. Projectivity descent is proved through these norms, never assumed.

The consumed public elementary_isPGroup computes the cardinality of the actual E as p^r and applies IsPGroup.of_card. IsPGroup.to_subgroup proves the required p-group fact for every actual H, including the trivial subgroup. Finite K supplies finite dimension over its canonical prime field. Module.compHom supplies the scalar action on V, ZMod's scalar-tower instance supplies compatibility, and FiniteDimensional.trans supplies finite dimension of V over the prime field. Nontriviality of the field and Module.finrank_pos give f>0.

The public endpoint PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective is applied exactly once to this actual scalar-restricted representation and the derived actual cyclic projectivity hypotheses. Module.finrank_mul_finrank then converts its conclusion to r*p ≤ f*finrank_K V. No fixed-vector counting, Burnside argument, prime-power divisibility argument, or private proof from the parent is reproduced.

For positive r, the constant vector with value 1 gives an actual nonidentity g in E, witnessed by evaluation at an index of Fin r. The ZMod module identity p • x=0 proves g^p=1 coordinatewise. Mathlib's orderOf_eq_prime and Fintype.card_zpowers give |H|=p for the actual subgroup H=zpowers g. Its cyclicity is the standard actual-subgroup instance, so hproj applies to precisely this restriction.

The consumed private finrank_eq_card_mul_invariants derives the dimension formula for an actual finite p-group over K. The public norm criterion supplies surjectivity of the norm onto W=rho.invariants. LinearMap.codRestrict forms the ordinary K-linear surjection V to W, using Representation.self_norm_apply for invariance of its image. Since W is a K-vector space, Module.projective_lifting_property lifts its identity to a K-linear section L. The public PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section gives V linearly equivalent to H → W. LinearEquiv.finrank_eq and Module.finrank_pi_fintype yield finrank_K V=|H|*finrank_K W. In the chosen actual subgroup this is d=p*n. The owner's private norm_section_of_projective is neither imported by name nor copied.

Substitute d=p*n in r*p ≤ f*d, commute the natural-number products, and cancel the positive prime p to obtain r ≤ f*n. The existing ceilDiv_le_iff_le_mul for f>0 gives r⌈/⌉f ≤ n. Multiplication by p yields the stated lower bound. Every private declaration is consumed on this public endpoint's proof path; there are no additional public specializations.

For r=0, the proof returns only the bound 0≤d before choosing any nonidentity element; it makes no p-divisibility assertion in that case. For r=1, f>0 gives ceil(1/f)=1, hence d≥p, consistently with projectivity on the entire cyclic group. Characteristic two follows the same proof with no exceptional branch. For positive rank the argument also gives p-divisibility of d. This module supplies no equality construction and claims no historical novelty.

The imported prime-field endpoint is used only through its public statement. The coefficient restriction, ordinary norm section, dimension tower and ceiling adjunction give this classical derived lower bound. Equality constructions and historical novelty are outside the scope of this module.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension.prime_mul_ceilDiv_finrank_le_finrank_of_cyclic_projective`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension](PrimeFieldUniformCyclicDimension.md)
