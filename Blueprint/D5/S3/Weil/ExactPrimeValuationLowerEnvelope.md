# Exact Prime Valuation Lower Envelope

## Abstract

Arbitrarily late lower Gronwall witnesses with all selected prime valuations exact.

**Theorem 1.1 (Lower envelope in every fixed exact valuation fibre).**

Lean statement: `D5/S3/Weil/ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set S of primes, every exponent function A, every positive epsilon, and every natural threshold N, there exists m at least max N 5041 whose valuation at each p in S is exactly A p and whose actual Robin ratio is at least the product over S of 1 minus p inverse to the power A p plus 1, less epsilon. Empty S and zero exponents are included. The proof replaces one selected prime part at a time, proves preservation of every other valuation, and carries the sigma divided by n inequality through finite-set induction. The upstream bound sigma one m at most m squared forces the resulting integer beyond N. Its size is at most a fixed multiple of the global Gronwall witness, so the existing fixed-scale loglog limit transfers the lower envelope. The set and exponents are fixed before the witness; no growing-profile uniformity, explicit threshold, or RH claim is asserted. The finite-replacement strategy was supplied by the caller; the proof terms connect it to the existing Gronwall, local-factor, and Mathlib APIs.

## References

- Truth anchor: `D5/S3/Weil/ExactPrimeValuationLowerEnvelope.exact_finite_prime_valuation_robin_lower_envelope`
- Dependency: [D5/S3/Weil/PrimeValuationGap](PrimeValuationGap.md)
