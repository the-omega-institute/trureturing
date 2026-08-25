# CRT as a Nilpotent Abelian Victory

## Abstract

Additive ZMod has a Sylow decomposition that does not extend to all finite groups.

**Theorem 1.1 (The additive group of positive ZMod decomposes into Sylow factors).**

$$\forall n \in \mathbb{N}, n \ne 0 \Rightarrow \operatorname{SylowPrimePowerDecomposable}(\operatorname{Multiplicative}(\operatorname{ZMod}(n))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.zmod_additive_group_is_prime_power_decomposable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive modulus n, Multiplicative (ZMod n) denotes the multiplicative wrapper of the additive group, so its group operation is ring addition rather than ring multiplication.

The group is finite and commutative, hence nilpotent. The existing finite prime-power quotient TFAE then supplies its exact Sylow direct-product decomposition without rebuilding CRT.

**Lemma 1.2 (The nonzero modulus hypothesis is necessary).**

$$\neg\operatorname{SylowPrimePowerDecomposable}(\operatorname{Multiplicative}(\operatorname{ZMod}(0))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.ne_zero_is_necessary_for_zmod_sylow_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus zero, ZMod is the infinite additive group of integers. Its natural cardinal is zero, so the Sylow prime-factor index is empty and its product is subsingleton, while the source is nontrivial.

**Theorem 1.3 (Prime-primary decomposition does not lift unconditionally).**

$$\exists G, \operatorname{FiniteGroup}(G) \land \operatorname{Noncommutative}(G) \land AllPrimePrimaryHomomorphismsTrivial(G) \land \neg\operatorname{Injective}(\operatorname{primePowerQuotientObserver}(G)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.prime_primary_decomposition_does_not_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a finite noncommutative group for which every map to every finite p-group is trivial and whose canonical prime-power quotient observer is therefore not injective.

The witness is A5. The imported A5 theorem supplies uniform triviality of all target maps; two distinct elements then receive identical values in every prime-power quotient.

This is an existential obstruction only. It does not claim that every noncommutative finite group lacks a prime-primary decomposition; noncommutative nilpotent groups are outside that false claim.

**Theorem 1.4 (The additive CRT case and its noncommutative boundary).**

$$\forall n \in \mathbb{N}, n \ne 0 \Rightarrow \operatorname{SylowPrimePowerDecomposable}(\operatorname{Multiplicative}(\operatorname{ZMod}(n))) \land \exists G, \operatorname{FiniteGroup}(G) \land \operatorname{PrimePrimaryDecompositionCounterexample}(G).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.crt_is_a_nilpotent_abelian_victory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive n, the Sylow decomposition of additive ZMod n is paired with the finite A5 counterexample to an unrestricted prime-primary decomposition principle.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.crt_is_a_nilpotent_abelian_victory`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.ne_zero_is_necessary_for_zmod_sylow_decomposition`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.prime_primary_decomposition_does_not_lift`
- Truth anchor: `D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.zmod_additive_group_is_prime_power_decomposable`
- Dependency: [D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness](FinitePrimePowerQuotientCompleteness.md)
- Dependency: [D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial](SimpleToPGroupTrivial.md)
