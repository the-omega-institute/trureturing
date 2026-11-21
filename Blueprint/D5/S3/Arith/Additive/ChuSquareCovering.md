# Additive covers of an initial interval

## Abstract

Sets A, B of sizes a, b in {0, …, N − 1} with A + B covering {0, …, N − 1} exist exactly when N ≤ ab, a ≤ N and b ≤ N; for N = n² the least common size is n.

**Theorem 1.1 (All achievable pairs of sizes).**

Lean statement: `D5/S3/Arith/Additive/ChuSquareCovering.achievable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/ChuSquareCovering.achievable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural numbers N, a and b, there are sets A, B ⊆ {0, …, N − 1} with |A| = a, |B| = b and A + B ⊇ {0, …, N − 1} exactly when N ≤ ab, a ≤ N and b ≤ N.

Necessity: N ≤ |A + B| ≤ |A| |B|, and A, B lie in a set of N elements. Sufficiency for a ≥ 1: every m < N is m mod a plus a multiple of a below N, so {0, …, a − 1} plus the multiples of a below N covers the interval; there are at most b such multiples because a multiple ja below N ≤ ab has j < b, and they are completed to b elements of the interval. For a = 0 the conditions force N = b = 0. This extends the argument of Proposition 9.1 of R. Blanco Gómez, Open statements in core entries of the OEIS, III (2026), from N = n² and a = b = n to every interval and every pair of sizes.

**Theorem 1.2 (Chu's question).**

Lean statement: `D5/S3/Arith/Additive/ChuSquareCovering.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/ChuSquareCovering.result` (`✓ std3`). ∎

*Citation.* Roberto Blanco Gómez (2026). *Open statements in core entries of the OEIS, III: Benford's law for the Bell numbers, Bala's congruences for the Motzkin numbers, and further proofs*. DOI: [10.5281/zenodo.23150301](https://doi.org/10.5281/zenodo.23150301). URL: <https://zenodo.org/records/23150301>.

*Commentary.*

For every n, the least k such that some A, B ⊆ {0, …, n² − 1} with |A| = |B| = k satisfy A + B ⊇ {0, …, n² − 1} is n. This is M. Chu's question (2022) in OEIS A000290, answered by Proposition 9.1 of Blanco Gómez (2026), stated there for n ≥ 1; for n = 0 the least size is 0.

By the characterization of achievable sizes, k is achievable exactly when n² ≤ k² and k ≤ n², that is n ≤ k ≤ n².

## References

- Truth anchor: `D5/S3/Arith/Additive/ChuSquareCovering.achievable_iff`
- Truth anchor: `D5/S3/Arith/Additive/ChuSquareCovering.result`
