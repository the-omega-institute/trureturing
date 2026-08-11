# Prime-Power Codes for Finite Sequences

## Abstract

Shifted prime-power products injectively encode finite natural sequences.

**Theorem 1.1 (Shifted prime-power coding is injective).**

$$\operatorname{Injective}(\operatorname{primeSequenceCode})$$

*Proof.* Machine-checked in Lean as `D5/S0/History/PrimeSequenceCode.prime_sequence_code_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite sequence of natural numbers is encoded as a finite product of consecutive primes. The entry at position i, plus one, is the exponent of the i-th prime. Shifting every exponent by one is essential: it records the length in the prime support, so a trailing zero cannot disappear from the code. Equality of two codes first forces equal lengths at the first prime missing from either product, then equality of every remaining prime exponent recovers the entries pointwise.

The pinned library was searched before proving. It supplies the injective increasing enumeration of primes through Nat.nth_injective and Nat.prime_nth_prime, together with finite product and prime-power factorization through Nat.factorization_prod_apply and Nat.Prime.factorization_pow. No direct declaration packages the shifted finite-sequence injection, so the Lean theorem is a new assembly of those library facts rather than a direct wrapper. The source atom contains no numerical certificate.

## References

- Truth anchor: `D5/S0/History/PrimeSequenceCode.prime_sequence_code_injective`
