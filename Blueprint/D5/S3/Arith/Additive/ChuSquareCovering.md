# Additive covers of an initial interval

## Abstract

Sets A, B of sizes a, b in {0, …, N − 1} with A + B covering {0, …, N − 1} exist exactly when N ≤ ab, a ≤ N and b ≤ N; for N = n² and a = b the least size is n.

**Theorem 1.1 (All achievable pairs of sizes).**

Lean statement: `D5/S3/Arith/Additive/ChuSquareCovering.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/ChuSquareCovering.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Blanco Gómez (2026). *Open statements in core entries of the OEIS, III: Benford's law for the Bell numbers, Bala's congruences for the Motzkin numbers, and further proofs*. DOI: [10.5281/zenodo.23150301](https://doi.org/10.5281/zenodo.23150301). URL: <https://zenodo.org/records/23150301>.

*Commentary.*

For natural numbers N, a and b, there are sets A, B ⊆ {0, …, N − 1} with |A| = a, |B| = b and A + B ⊇ {0, …, N − 1} exactly when N ≤ ab, a ≤ N and b ≤ N.

Necessity: N ≤ |A + B| ≤ |A| |B|, and A, B lie in a set of N elements. Sufficiency for a ≥ 1: every m < N is m mod a plus a multiple of a below N, so {0, …, a − 1} plus the multiples of a below N covers the interval; there are at most b such multiples because a multiple ja below N ≤ ab has j < b, and they are completed to b elements of the interval. For a = 0 the conditions force N = b = 0.

With N = n² and a = b = k the condition reads n ≤ k ≤ n², so the least k is n. This is M. Chu's conjecture (2022) in OEIS A000290, proved as Proposition 9.1 of R. Blanco Gómez, Open statements in core entries of the OEIS, III (2026), for n ≥ 1; for n = 0 the least size is 0. The theorem extends the source's argument to every interval and every pair of sizes.

## References

- Truth anchor: `D5/S3/Arith/Additive/ChuSquareCovering.result`
