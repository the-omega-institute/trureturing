# The two-component control family

## Abstract

A single interior zero for the control function.

**Theorem 1.1 (Exactly one control zero).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Control.zeros_control`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Control.zeros_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural numbers n and d and any real c, take a=(n+c,n+c) and b=(c,2n+d+c). The control function has exactly one zero in the interval from zero to one, with both endpoints excluded.

For positive x, the function is x to the power c times 2x to the power n minus one minus x to the power 2n+d. Factoring the latter expression by x-1 leaves the geometric-sum polynomial H(x)=sum over i below n of x to the power i minus x to the power n times the sum over i below n+d of x to the power i. Its endpoint values are one and minus d, so continuity gives an interior zero.

After division by x to the power n, the first sum consists of real powers with negative exponents. Every such term strictly decreases on the positive axis. Every term of the second sum is nondecreasing. The resulting difference strictly decreases, which gives uniqueness. The factors x to the power c and x-1 do not vanish in the interval.

## References

- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Control.zeros_control`
- Dependency: [D5/S3/Analytic/MeijerZeroCount/Defs](Defs.md)
