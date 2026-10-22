# Residues and Mellin inversion

## Abstract

The Gamma quotient is the Mellin transform of a compactly supported Rodrigues kernel.

**Theorem 1.1 (The finite residue expansion).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Mellin.gammaQuot_family`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Mellin.gammaQuot_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n and d with d at least two, positive real c, and complex s with positive real part, take a=(n+c,n+c) and b=(c,2n+d+c). The Gamma quotient is the sum over k from zero through N=n+d-1 of A(k)/(s+c+n+k), where A(k)=(-1)^(n+k)(n+k)!/((k!)^2(N-k)!). Gamma recurrence gives the quotient of ascending factorial polynomials. Lagrange interpolation at the consecutive negative integers gives the residues.

**Theorem 1.2 (The Mellin transform of the kernel).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Mellin.mellin_f`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Mellin.mellin_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same parameters and every complex s with positive real part, the Mellin transform of f(n,d,c) equals the Gamma quotient. On the unit interval the kernel is the finite sum of A(k) times x^(n+c+k), and outside it the kernel is zero. Each power term has Mellin transform one divided by s+c+n+k. The finite sum is integrable, and endpoint values do not affect the integral.

**Theorem 1.3 (Identification by Mellin inversion).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Mellin.meijerG_eq_f`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Mellin.meijerG_eq_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, every natural d at least two, every positive real c, and every x strictly between zero and one, Meijer's G for a=(n+c,n+c) and b=(c,2n+d+c) equals f(n,d,c,x). Along s=1+it the norm of the Gamma quotient is at most 1/(1+t^2): pair the n numerator factors with shifted denominator factors, and retain two additional denominator factors. This integrable bound, Mellin convergence, and continuity of the kernel at x discharge Mellin inversion along the line of real part one.

## References

- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Mellin.gammaQuot_family`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Mellin.meijerG_eq_f`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Mellin.mellin_f`
- Dependency: [D5/S3/Analytic/MeijerZeroCount/Rodrigues](Rodrigues.md)
