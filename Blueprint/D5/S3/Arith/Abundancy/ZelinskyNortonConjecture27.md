# Zelinsky's Conjecture 27

## Abstract

Every Norton threshold at alpha greater than one has unbounded first differences.

**Theorem 1.1 (Every fixed positive increment is eventually exceeded).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-norton-conjecture-27` (proved) by `D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-norton-conjecture-27","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Zelinsky (2023). *On the small prime factors of a non-deficient number*. URL: <https://math.colgate.edu/~integers/x13/x13.pdf>.

*Commentary.*

For every real alpha>1 and every real C>0, all sufficiently large natural n satisfy aAlpha(alpha,n)+C<aAlpha(alpha,n+1), with each natural threshold length cast to the real numbers. Both parameters are fixed before the eventual index is chosen. This is Conjecture 27 on page 13 of Zelinsky's Integers 23 article A13.

Adjacent cancellation gives a positive constant c, depending on alpha, such that c*p_n^(alpha-1) is at most one plus the real first difference for every sufficiently large n. The primes p_n tend to infinity, and alpha-1 is positive. Hence this lower bound tends to infinity and eventually exceeds C+1, giving the required strict inequality.

The assertion concerns eventual growth for each fixed alpha and C. It does not supply a uniform starting index over all alpha>1, and it does not claim an exact asymptotic equivalence for the first difference.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.result`
- Dependency: [D5/S3/Arith/Abundancy/BeriZelinskyQuestion6](BeriZelinskyQuestion6.md)
