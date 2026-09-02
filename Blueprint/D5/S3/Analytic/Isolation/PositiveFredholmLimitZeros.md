# Positive Fredholm Limits Preserve the Negative Real Zero Locus

## Abstract

Locally uniform limits of finite positive spectral determinants have only nonpositive real zeros.

**Theorem 1.1 (Positive spectral determinant limits preserve their zero locus).**

$$\forall r: \mathbb{N} \to \mathbb{N}, \\{}\lambda: {N: \mathbb{N}} \to Fin\left(r\left(N\right)\right) \to \mathbb{R}, \\{}F: \mathbb{C} \to \mathbb{C}, \\{}{{\forall N\in \mathbb{N}, \forall j\in Fin\left(r\left(N\right)\right), 0 \le \lambda\left(N, j\right)} \land {TendstoLocallyUniformly\left((N, w) \mapsto \prod_{j\in Fin\left(r\left(N\right)\right)} {1 + w \cdot \lambda\left(N, j\right)}, F, atTop\right)}} \Rightarrow \\{}\forall w\in \mathbb{C}, F\left(w\right) = 0 \Rightarrow {Im\left(w\right) = 0 \land Re\left(w\right) \le 0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_fredholm_limit_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite rank and every indexed nonnegative real spectrum, form the determinant polynomial as the product of the factors one plus the complex argument times an eigenvalue. If these polynomials converge locally uniformly on the complex plane, every zero of the limit has zero imaginary part and nonpositive real part.

The normalization at zero is automatic from the displayed spectral product and local uniform convergence, so the Lean statement proves a strictly stronger form without adding that redundant premise.

Repository and pinned-library searches found locally uniform limit regularity and analytic isolated-zero theorems, but no existing theorem that preserves this zero locus. The proof instead compares each off-axis factor with the same factor on a suitable positive real point. Boundedness at that point supplies a positive lower bound at the candidate zero, contradicting convergence there.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros.positive_fredholm_limit_zeros`
