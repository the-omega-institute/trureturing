# Cigler Conjecture 7.5 printed second-line refutation

## Abstract

Refutes only the printed second line of equation 7.11, Conjecture 7.5 in arXiv:1801.05608v3, at k = n = 1; literature-attested, new_counterexample_claimed = false. No claim that the intended proposition is false or its proof has a gap; no verdict on the first line or Conjecture 7.6 (the reported 7.6 counterexample was a transcription error). No priority is claimed for the determinant values or identification of the printing error.

Johann Cigler, Catalan numbers, Hankel determinants and Fibonacci polynomials, arXiv:1801.05608v3, printed page 30, Conjecture 7.5, equation 7.11, says For k > 0 we have. Its second line asserts that D at 2kn minus 1, 2k, plus D at 2kn plus 2, 2k, equals minus k times (2k minus 3) times (2n plus 1) to the power k minus 1. It prints no restriction k >= 2 and no lower bound on n. The formal claim quantifies over every positive natural k and every natural n, with integer subtraction in the factor 2k minus 3. At the witness both determinant indices are positive, so natural index subtraction is exact. The rendered PDF pages 2, 26 and 30 were visually checked on 2026-09-10.

**Theorem 1.1 (The printed second line is false).**

Lean statement: `D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k = n = 1 the left side is D(1,2) plus D(4,2). Both determinants equal 1, so their sum is 2 while the printed right side is 1. The kernel proof reuses the frozen unshifted Hankel definition from MotzkinConvolutionHankelRefutation and the Cauchy powers from CatalanConjectureSevenRefutation, whose module is unfrozen at this lane's base. Finite computations stay inside the proof. Independent exact calculations use the page 2 binomial formula with Bareiss elimination, and the Catalan recurrence with Cauchy multiplication and full Leibniz expansion. The 21 positive controls all agree: D(m,2) for m from 0 through 6, Theorem 7.3's D(m,4) for m from 0 through 7, and the page 30 list D(m,8) for m from 0 through 5. All 683 divisions in the first computation are verified exact; the second has no divisions or floating point. These values are literature-attested: Johann Cigler, Catalan numbers, Hankel determinants and Fibonacci polynomials, arXiv:1801.05608v3, already prints D(n,2) = 1 on pages 2 and 26. The first line of equation 7.11 on page 30 also implies them at k = 1. Thus the two lines on page 30 already imply the contradiction. This is not a claim to a new counterexample; new_counterexample_claimed = false. Only the printed second line at k = n = 1 is refuted. No claim is made that the author's intended proposition is false or that its proof has a gap. No verdict is given on the first line or Conjecture 7.6; the reported 7.6 counterexample was a transcription error, not a counterexample. Neither first discovery of these values nor first identification of the printing error is claimed. FromRepo records this repository's formal derivation because no LibraryNoteRef for this paper is present; it does not assert literature novelty, and no L-plane note is introduced.

## References

- Truth anchor: `D5/S0/Certificates/CiglerConjectureSevenFiveRefutation.result`
- Dependency: [D5/S0/Certificates/CatalanConjectureSevenRefutation](CatalanConjectureSevenRefutation.md)
- Dependency: [D5/S0/Certificates/MotzkinConvolutionHankelRefutation](MotzkinConvolutionHankelRefutation.md)
