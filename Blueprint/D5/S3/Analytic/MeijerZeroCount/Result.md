# The zero-count refutation

## Abstract

A two-component Gamma quotient violates the proposed comparison of interior zero counts.

**Theorem 1.1 (The counterexample family).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Result.family`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Result.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and d at least two and every positive real c, set a=(n+c,n+c) and b=(c,2n+d+c). In the unit interval with endpoints excluded, Meijer's G has exactly n distinct zeros and the control function has exactly one zero. Mellin inversion identifies G with the Rodrigues kernel, whose zero count follows from Rolle's theorem and the polynomial degree. The control zero count follows from strict monotonicity of its normalized factor.

**Theorem 1.2 (Failure of the comparison).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proposition claim is false. Taking n=d=2 and c=1 gives nonnegative a=(3,3), b=(1,7), and sum of b(i)-a(i) equal to two, which is greater than one. The interior zero counts are two for G and one for the control function, contradicting the proposed inequality. The family theorem also exhibits arbitrarily large discrepancies while keeping two components and d=2.

## References

- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Result.family`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Result.result`
- Dependency: [D5/S3/Analytic/MeijerZeroCount/Control](Control.md)
- Dependency: [D5/S3/Analytic/MeijerZeroCount/Mellin](Mellin.md)
