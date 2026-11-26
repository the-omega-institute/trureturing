# The restricted lemniscatic derivation at odd primes

## Abstract

Iterating the derivation p times over the field of p elements gives a scalar multiple of the original derivation. The scalar vanishes at primes congruent to three modulo four.

Alpöge’s CM derivative argument motivates the prime-by-prime analysis. The proof uses polynomial pairs and the coefficient support of the square of the derivation.

**Lemma 1.1 (Iterated Leibniz rule).**

Lean statement: `D5/S3/Arith/CMJet/Prime.iter_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Prime.iter_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order n, the coefficient of the product of the order n−k and k derivatives is the binomial coefficient n choose k. The induction uses the first-order Leibniz rule and Pascal's identity.

**Definition 1.2 (The restricted derivation).**

Lean statement: `D5/S3/Arith/CMJet/Prime.primeIter`

*Formalization.* `D5/S3/Arith/CMJet/Prime.primeIter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime p, each interior binomial coefficient at order p vanishes in the residue field. The two end terms give the derivation law for the actual p-fold iterate.

**Theorem 1.3 (The scalar is determined by the derivative of X).**

Lean statement: `D5/S3/Arith/CMJet/Prime.prime_iter_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Prime.prime_iter_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd prime p, write D^pX = YF, where F has degree at most p−1. The curve relation and commutation with D force (1 − X⁴)F′ = 0. Thus F is constant, and the action on X and Y determines D^p on all pairs.

**Theorem 1.4 (Vanishing at inert primes).**

Lean statement: `D5/S3/Arith/CMJet/Prime.inert_iter_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Prime.inert_iter_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

When p ≡ 3 modulo 4, the coefficient of X in Q^(p/2)X is zero by the modulo-four support rule. That coefficient gives the scalar of the restricted derivative, so D^p vanishes on every pair over the residue field.

## References

- Truth anchor: `D5/S3/Arith/CMJet/Prime.inert_iter_zero`
- Truth anchor: `D5/S3/Arith/CMJet/Prime.iter_mul`
- Truth anchor: `D5/S3/Arith/CMJet/Prime.primeIter`
- Truth anchor: `D5/S3/Arith/CMJet/Prime.prime_iter_scalar`
- Dependency: [D5/S3/Arith/CMJet/Basic](Basic.md)
