# The radical quotient and two divisor sums

## Abstract

A radical quotient below the least missing prime forces the joint divisor-sum inequality.

For a positive integer N, let rad(N) be the product of its distinct prime divisors. Let U(N) be the sum of its positive unitary divisors, and S(N) the sum of its positive squarefree divisors; both include one. The reciprocal conjecture lines in the two source entries express one implication, recorded in the linked problem dossier.

**Definition 1.1 (The least missing prime).**

Lean statement: `D5/S3/Arith/Divisors/KarttunenA401714.leastMissingPrime`

*Formalization.* `D5/S3/Arith/Divisors/KarttunenA401714.leastMissingPrime` (`✓ std3`).

*Citation.* Antti Karttunen (2026). *OEIS A401714 and A401715: radical quotient and joint divisor sums*. URL: <https://github.com/oeis/oeisdata/blob/24e9613f999e4d1e98e6d8a4c2b6ae0124d79ed8/seq/A401/A401714.seq>.

*Commentary.*

The least missing prime is the smallest prime that does not divide N. The frozen least-missing-prime threshold theorem supplies existence. Nat.find selects the least witness to primality and nondivisibility.

**Theorem 1.2 (The divisor-sum implication).**

Lean statement: `D5/S3/Arith/Divisors/KarttunenA401714.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/KarttunenA401714.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2026). *OEIS A401714 and A401715: radical quotient and joint divisor sums*. URL: <https://github.com/oeis/oeisdata/blob/24e9613f999e4d1e98e6d8a4c2b6ae0124d79ed8/seq/A401/A401714.seq>.

*Commentary.*

For every positive integer N, if N/rad(N) is less than its least missing prime, then U(N)+S(N) is at least 2N. The strict inequality forces every prime at most N/rad(N) to divide N. The mandatory support theorem then gives the claimed inequality. No bound on N, parity restriction or restriction on its number of prime divisors is imposed.

## References

- Truth anchor: `D5/S3/Arith/Divisors/KarttunenA401714.leastMissingPrime`
- Truth anchor: `D5/S3/Arith/Divisors/KarttunenA401714.result`
- Dependency: [D5/S3/Arith/Divisors/UnitaryProductBridge](UnitaryProductBridge.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime](../GoldenResource/GoldenSmallestMissingPrime.md)
