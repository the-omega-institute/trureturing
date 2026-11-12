# The eventual three-prefix conjecture is false

## Abstract

The odd-root continued-fraction conjecture fails on an unbounded arithmetic progression of indices.

Kim and Stolarsky, A Balanced Three-term Generalization of Nicomachus' Identity, arXiv:2511.15133v1, Theorem 1 and Remark 4, conjecture three simultaneous ordinary continued-fraction prefixes for the negatives of real roots tending to minus four. The journal version, A Balanced Three or More-term Generalization of Nicomachus' Identity, Integers 26, A98, retains these formulas in Remark 3. The claim here includes all three original polynomial sums, the shift from m to m+1 for L and R, all three root limits, and one eventual threshold.

**Theorem 1.1 (No common eventual threshold exists).**

Lean statement: `D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kim-stolarsky-eventual-three-prefix-conjecture` (refuted) by `D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kim-stolarsky-eventual-three-prefix-conjecture","declaration_gid":"D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Seon-Hong Kim and Kenneth B. Stolarsky (2026). *A Balanced Three or More-term Generalization of Nicomachus' Identity*. DOI: [10.5281/zenodo.21678529](https://doi.org/10.5281/zenodo.21678529). URL: <https://math.colgate.edu/~integers/aa98/aa98.pdf>.

*Commentary.*

Put m=10^(4n+2). The shifted R polynomial is the square of T_(2m+1)+(1+T_m)x. Its unique distinct real root is r=-2(2m+1)(m+1)/(m^2+m+2). For m greater than ten, the number y=-r satisfies y-4=(2m-6)/(m^2+m+2), which lies strictly between zero and 2/m. Thus the actual root branch tends to minus four.

The reciprocal of y-4 is exactly m/2+2+7/(m-3). Since m is even and 0<7/(m-3)<1, the coefficient after four is m/2+2=50*10^(4n)+2. The next complete quotient is (m-3)/7. If n=3k+2, then m is congruent to four modulo seven. Writing m=7q+4, this complete quotient is q+1/7, so its floor is q. The printed formula is floor(m/7)-1=q-1. The subsequent coefficient is seven, so the rational continued fraction does not terminate at the disputed position.

For every proposed threshold N, the index 3N+2 lies beyond it and violates the R prefix. Hence the complete eventual conjunction is false. No individual conclusion about the L or Q prefixes, or the even case, follows. The formal proof derives the contradiction for every R root; its root-limit hypothesis need not be used.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result`
- Dependency: [D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic](QuadraticImpliesPeriodic.md)
