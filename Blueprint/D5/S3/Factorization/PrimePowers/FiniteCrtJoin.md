# Finite CRT Join

## Abstract

Finite prime-power CRT retains empty support and labeled trivial factors.

**Theorem 1.1 (Finite prime-power factors join by CRT).**

$$\forall S: \operatorname{Finset}(\mathbb{N}), kappa: \mathbb{N} \to \mathbb{N}, \operatorname{PrimeSet}(S) \Rightarrow \operatorname{Nonempty}(\operatorname{ZMod}(\prod_{p \in S} p^{kappa(p)}) \sim \prod_{p \in S} \operatorname{ZMod}(p^{kappa(p)})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite set of primes and let kappa assign a natural exponent to each prime. The named primePowerProduct is the product of the resulting prime powers.

Pinned Mathlib's exact ZMod.prodEquivPi equivalence is applied to the subtype indexed by S. Nat.coprime_pow_primes discharges its pairwise-coprimality premise for distinct labels.

Unlike ZMod.equivPi, this indexing retains primes whose exponent is zero. Those coordinates are ZMod 1 and therefore trivial.

**Lemma 1.2 (Empty support gives the trivial ring).**

$$\forall kappa: \mathbb{N} \to \mathbb{N}, \operatorname{Nonempty}(\operatorname{ZMod}(\prod_{p \in \emptyset} p^{kappa(p)}) \sim \prod_{p \in \emptyset} \operatorname{ZMod}(p^{kappa(p)})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty product is one, and the dependent product over the empty index type is a trivial ring. The main equivalence covers this case without a nonemptiness hypothesis.

**Lemma 1.3 (A zero exponent gives a trivial labeled coordinate).**

$$\operatorname{PrimeSet}(S) \land p \in S \land kappa(p) = 0 \Rightarrow \operatorname{Nonempty}(\operatorname{ZMod}(\prod_{p \in S} p^{kappa(p)}) \sim \prod_{p \in S} \operatorname{ZMod}(p^{kappa(p)})) \land \operatorname{Subsingleton}(\operatorname{ZMod}(p^{kappa(p)})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_zero_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If kappa(p) is zero, the p-coordinate is ZMod 1 and is subsingleton. The global CRT equivalence remains valid with that label present.

**Lemma 1.4 (A singleton family needs no primality premise).**

$$\forall p, e \in \mathbb{N}, \operatorname{Nonempty}(\operatorname{ZMod}(p^{e}) \sim \prod_{q \in \{p\}} \operatorname{ZMod}(q^{e})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairwise coprimality is vacuous for a singleton index type. Hence the singleton CRT equivalence holds for every natural label and every natural exponent, so no unused primality premise is retained.

**Lemma 1.5 (All zero exponents still form a trivial product).**

$$\operatorname{Nonempty}(\operatorname{ZMod}(1) \sim \prod_{p \in \{2, 3\}} \operatorname{ZMod}(1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_all_zero_exponents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the nonempty prime set containing two and three, assigning exponent zero to both labels gives modulus one and two labeled ZMod 1 coordinates. Both sides are trivial rings.

**Lemma 1.6 (Overlapping composite labels invalidate the unrestricted claim).**

$$\neg\operatorname{Nonempty}(\operatorname{ZMod}(8) \sim \operatorname{ZMod}(2) \times \operatorname{ZMod}(4)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.prime_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dropping the prime-set condition admits labels two and four with exponent one. ZMod 8 cannot be ring-equivalent to ZMod 2 times ZMod 4: four vanishes in both target coordinates but not in ZMod 8.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_all_zero_exponents`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_empty`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_singleton`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.finite_crt_join_zero_exponent`
- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCrtJoin.prime_hypothesis_is_necessary`
