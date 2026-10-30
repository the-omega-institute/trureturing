# General-parameter Mills remainder classification

## Abstract

The exact general-parameter Mills remainder classification target, with compiled endpoint-sign consequences.

**Definition 1.1 (Original signed remainder normalization).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F`

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F n a x is the original signed remainder (-1)^n * D n x a, where D is imported from the frozen Xu-Yang Mills source and retains the Gaussian Mills ratio, Gamma coefficients, and finite truncation.

**Definition 1.2 (Theorem 2.1 target).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21`

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n >= 2 and real a, the positive global-sign predicate is equivalent to complete monotonicity and to a <= theta (n-2); the negative global-sign predicate is equivalent to complete monotonicity of -F and to a >= theta (n-1), with both endpoints included. The proposition is retained as the exact source target.

The current compiled checkpoint proves the zeroth-order sign projection from complete monotonicity and proves the general one-sided endpoint-limit sign lemma. The general-a coefficient identity, strict adjacent weighted-moment comparison, and the two Mills endpoint limits remain open.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21`
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
