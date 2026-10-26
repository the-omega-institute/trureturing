# Two or Three Prime Occurrences in Bouras A363102

## Abstract

Every occurring prime has two or three indices in Bouras A363102.

The continued fraction is rational, and Rat.den gives its positive reduced denominator. Indices are natural numbers, and occurrences are counted only for n at least three. Set.ncard is zero on infinite sets; the proof constructs either a pair or a triple.

**Definition 1.1 (The continued-fraction denominator).**

$$\forall n \in \mathbb{N},\; \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = \operatorname{Rat}.\operatorname{den}\left(\operatorname{BourasA356360}.\operatorname{K}\left(n, -2\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.a` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

OEIS A363102, NAME (unpaginated): "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))." The sequence is Rat.den of K n (-2), where K is the reciprocal right-folded fraction. Its offset is n = 3.

**Definition 1.2 (Bouras's Conjecture 2).**

$$\operatorname{BourasA363102}.\operatorname{claim} = (\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(\left(\exists n \in \mathbb{N},\; 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\right) \Rightarrow \left(\operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\}\right) = 2 \lor \operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\}\right) = 3\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.claim` (`✓ std3`).

*Citation.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

OEIS A363102, COMMENTS, Conjecture 2 (unpaginated): "Conjecture 2: All prime numbers appear either twice (same as A356247 and A357127) or three times." The quantifier ranges over prime values that occur in the sequence. This reading follows the comparison with the other sequences; it does not assert that every prime occurs. The set includes every index at least three giving the chosen prime.

**Theorem 1.3 (Two or three occurrences).**

$$\forall p \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(\left(\exists n \in \mathbb{N},\; 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\right) \Rightarrow \left(\operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\}\right) = 2 \lor \operatorname{Set}.\operatorname{ncard}\left(\{n: \mathbb{N} \mid 3 \le n \land \operatorname{BourasA363102}.\operatorname{a}\left(n\right) = p\}\right) = 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bouras-a363102` (proved) by `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bouras-a363102","declaration_gid":"D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Bouras (2023). *OEIS A363347 and A363102, prime multiplicities of continued-fraction denominators*. URL: <https://oeis.org/A363347>.

*Commentary.*

The roots of n squared equal to two in ZMod p give exactly two indices below p, paired by n mapping to p-n. Every further index must satisfy n squared equal to twice p squared plus two, which permits at most one natural index. Thus the full occurrence set is a pair or a triple. The converse from a solution of that equation to a further occurrence is not asserted.

## References

- Truth anchor: `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.a`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.claim`
- Truth anchor: `D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity.result`
- Dependency: [D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity](BourasA363347PrimeMultiplicity.md)
