# Krizek's Triangular-Square Divisor-Sum Characterization

## Abstract

A positive triangular number is square exactly when its index and value have odd divisor sums.

**Theorem 1.1 (The triangular-square divisor-sum characterization).**

$$\forall n \in \mathbb{N},\; (n > 0) \Rightarrow ((IsSquare\left((n \cdot (n + 1)) / 2\right)) \Leftrightarrow ((Odd\left(\left(\sigma_{1}\right)\left(n\right)\right)) \land (Odd\left(\left(\sigma_{1}\right)\left((n \cdot (n + 1)) / 2\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/KrizekTriangularSquareSigmaParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a001108-krizek-triangular-square-sigma-parity` (proved) by `D5/S3/Arith/KrizekTriangularSquareSigmaParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a001108-krizek-triangular-square-sigma-parity","declaration_gid":"D5/S3/Arith/KrizekTriangularSquareSigmaParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane; Jaroslav Krizek (2016). *OEIS A001108, a(n)-th triangular number is a square*. URL: <https://oeis.org/A001108>.

*Commentary.*

The classical divisor-sum parity characterization reduces each odd divisor sum to a square-or-twice-square alternative. A coprime-product split for consecutive integers proves the forward direction, and a twice-square exclusion for triangular numbers proves the reverse direction. At n=0 the triangular number is zero and square, while its divisor sum is even, so positivity excludes that boundary.

## References

- Truth anchor: `D5/S3/Arith/KrizekTriangularSquareSigmaParity.result`
