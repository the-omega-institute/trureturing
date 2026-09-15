# The OEIS A072872 Prime-Index Upper-Bound Conjecture

## Abstract

The n = 6298 certificate refutes Cloitre's A072872 prime-index upper bound.

**Definition 1.1 (The least positive power-minus-index witness).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{sInf}\left(\{k \in \mathrm{Nat} \mid (0 < k \land n \mid 2^{k} - k)\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.a` (`✓ std3`).

*Citation.* Benoit Cloitre (2002). *OEIS A072872, a(n) is the smallest positive number k such that n divides 2^k - k*. URL: <https://oeis.org/A072872>.

*Commentary.*

For each natural n, a(n) is the least positive k for which n divides 2^k - k. The natural-number convention gives sInf of an empty set the value zero; no general existence assertion is made.

**Definition 1.2 (Cloitre's prime-index upper-bound conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; 47 < n \Rightarrow \operatorname{a}\left(n\right) < \operatorname{nth}\left(Prime, n - 1\right))$$

*Formalization.* `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim` (`✓ std3`).

*Citation.* Benoit Cloitre (2002). *OEIS A072872, a(n) is the smallest positive number k such that n divides 2^k - k*. URL: <https://oeis.org/A072872>.

*Commentary.*

For every natural n greater than 47, the conjecture says that a(n) is less than the n-th prime, with the source's prime(n) notation represented by Nat.nth Nat.Prime (n - 1).

**Theorem 1.3 (The conjecture fails at n = 6298).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a072872-power-minus-index-prime-bound-refutation` (refuted) by `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a072872-power-minus-index-prime-bound-refutation","declaration_gid":"D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benoit Cloitre (2002). *OEIS A072872, a(n) is the smallest positive number k such that n divides 2^k - k*. URL: <https://oeis.org/A072872>.

*Commentary.*

The modular certificate proves a(6298) = 77742, while the prime-count certificate proves that the 6298th prime is 62753. Hence the universal upper bound is false.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.a`
- Truth anchor: `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result`
