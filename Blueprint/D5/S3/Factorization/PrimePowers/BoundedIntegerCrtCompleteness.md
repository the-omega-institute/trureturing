# Bounded Integer CRT Completeness

## Abstract

Prime-power CRT has exactly its product capacity on bounded integers.

**Theorem 1.1 (Bounded prime-power residues have exact product capacity).**

$$\forall N: \mathbb{N}, S: \operatorname{Finset}(\mathbb{N}), kappa: \mathbb{N} \to \mathbb{N},\\{}\operatorname{PrimeSet}(S) \Rightarrow \operatorname{Injective}(q_{S, kappa}: X_{N} \to \prod_{p \in S} \operatorname{ZMod}(p^{kappa(p)})) \iff N \le \prod_{p \in S} p^{kappa(p)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness.bounded_integer_crt_complete_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named boundedIntegerWindow is Fin N, hence consists of the N integers from zero through N minus one. It is not the inclusive interval from zero through N.

The named primePowerResidueReading casts each bounded integer into every labeled prime-power residue ring. The modulus is the existing primePowerProduct from FiniteCrtJoin.

The forward implication reuses the general retained-moduli capacity criterion. The reverse implication applies finite_crt_join and then uses the strict bounds carried by Fin N.

The statement includes the empty window, empty prime support, and zero exponents. Empty support and all-zero exponents both have capacity one, so only windows of size at most one are faithful.

**Lemma 1.2 (Overlapping composite moduli refute the unrestricted criterion).**

$$\neg(\operatorname{Injective}(q_{\{2, 4\}, 1}: X_{5} \to \prod_{p \in \{2, 4\}} \operatorname{ZMod}(p^{1})) \iff 5 \le 8).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness.prime_support_condition_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With labels two and four and exponent one, the formal product is eight. Nevertheless zero and four already collide in both coordinates on the five-element window, so product capacity alone is insufficient.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness.bounded_integer_crt_complete_iff`
- Truth anchor: `D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness.prime_support_condition_is_necessary`
- Dependency: [D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion](../../ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion.md)
- Dependency: [D5/S3/Factorization/PrimePowers/FiniteCrtJoin](FiniteCrtJoin.md)
