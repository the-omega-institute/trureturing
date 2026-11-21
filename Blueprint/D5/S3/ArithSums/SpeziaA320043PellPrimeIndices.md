# Prime terms of the Pell sequence and square values of A320043

## Abstract

For a prime p, the A320043 value a(p − 1) is a square exactly when p is a term of A001075; for p > 2 exactly when p = x_{2^h}, and then p ≡ 7 (mod 30).

**Definition 1.1 (The Pell sequence A001075).**

Lean statement: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.r`

*Formalization.* `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.r` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)*. DOI: [10.5281/zenodo.24058057](https://doi.org/10.5281/zenodo.24058057). URL: <https://zenodo.org/records/24058057>.

*Commentary.*

r_0 = 1, r_1 = 2 and r_{j+2} = 4r_{j+1} − r_j; equivalently r_j = ((2 + √3)^j + (2 − √3)^j)/2.

**Definition 1.2 (The even-index subsequence).**

Lean statement: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.x`

*Formalization.* `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.x` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)*. DOI: [10.5281/zenodo.24058057](https://doi.org/10.5281/zenodo.24058057). URL: <https://zenodo.org/records/24058057>.

*Commentary.*

x_0 = 1, x_1 = 7 and x_{t+2} = 14x_{t+1} − x_t, the first coordinates of (7 + 2√12)^t.

**Theorem 1.3 (Square values at prime rows and Pell primes).**

Lean statement: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.result`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)*. DOI: [10.5281/zenodo.24058057](https://doi.org/10.5281/zenodo.24058057). URL: <https://zenodo.org/records/24058057>.

*Commentary.*

For a(n) = Σ_{k=1}^{n} (n + 1 − k)² k / gcd(n + 1 − k, k)³ every quotient is exact. Moreover r_{2t} = x_t; a prime p has a(p − 1) a square exactly when p is a term of (r_j); a prime p > 2 has a(p − 1) a square exactly when p = x_{2^h} for some h ≥ 0; and every x_{2^h} is 7 modulo 30.

The terms r_j are the first coordinates of the powers of the fundamental solution 2 + √3 of X² − 3Y² = 1, hence all positive first coordinates of solutions. With the prime-row criterion a(p − 1) square ⟺ p² − 12y² = 1 for p ≥ 5, a(1) = 1 and a(2) = 6, this gives the first equivalence: odd-index terms are even, and even-index terms pair with an even second coordinate. The identity r_{i+2k} + r_i = 2 r_{i+k} r_k shows that r_m divides r at every odd multiple of m, so with 1 < r_m < r_{mk} a prime x_t forces t = 2^h; the doubling r_{2k} = 2r_k² − 1 maps the residue 7 modulo 30 to itself. This is Corollary 4 of H. Ma and W. Zhang, OEIS A320043, COMMENTS, revision 43 (2026); the index restriction is Zhu's (2011), the congruence and divisibility appear in Tiffin's 2016 OEIS comments, and the paper credits the odd-multiple argument to Andrews (2019).

## References

- Truth anchor: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.r`
- Truth anchor: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.result`
- Truth anchor: `D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.x`
- Dependency: [D5/S3/ArithSums/SpeziaA320043PrimeRowCriterion](SpeziaA320043PrimeRowCriterion.md)
