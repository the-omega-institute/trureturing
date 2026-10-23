# The entire Kummer series

## Abstract

Convergence, regularity, positivity and recurrences of the Kummer series.

**Theorem 1.1 (Convergence for every real argument).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.summable_kummer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.summable_kummer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real upper parameter s, positive lower parameter c and real argument x, the defining series is summable. The recurrence between successive coefficients gives a multiplier tending to zero. The norm ratio bound proves absolute convergence even when the rising factorial in the numerator vanishes.

**Theorem 1.2 (The value at zero).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.kummer_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.kummer_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real s and c, M(s;c;0)=1. Only the constant term contributes, so this identity does not require positivity of c.

**Theorem 1.3 (A positive lower bound).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.one_le_kummer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.one_le_kummer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When s and x are nonnegative and c is positive, all terms are nonnegative. The constant term is one, and hence M(s;c;x) is at least one.

**Theorem 1.4 (Differentiation shifts both parameters).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.hasDerivAt_kummer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.hasDerivAt_kummer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real s, positive c and every real x, the derivative of M(s;c;x) is (s/c) M(s+1;c+1;x). On each bounded interval, the differentiated terms are bounded by a constant multiple of an absolutely summable Kummer series at a larger nonnegative argument. Termwise differentiation therefore applies.

**Theorem 1.5 (Continuity on the real line).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.continuous_kummer`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.continuous_kummer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real s and positive c, the function x mapped to M(s;c;x) is continuous on the whole real line, as a consequence of its derivative formula.

**Theorem 1.6 (The confluent hypergeometric equation).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.kummer_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.kummer_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real s, positive c and every real x, the shifted series satisfy x (s/c) ((s+1)/(c+1)) M(s+2;c+2;x)+(c-x) (s/c) M(s+1;c+1;x)-s M(s;c;x)=0. The coefficient recurrence cancels every coefficient. The derivative formula identifies this identity with x y''+(c-x)y'-s y=0, including x=0.

**Theorem 1.7 (A relation between lower parameters).**

Lean statement: `D5/S3/Analytic/KummerRatio/Series.kummer_contiguous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Series.kummer_contiguous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real s, positive c and every real x, M(s;c;x)=M(s;c+1;x)+s x/(c(c+1)) M(s+1;c+2;x). The rising factorial identity c (c+1)_n=(c+n)(c)_n gives the coefficient identity; absolute convergence justifies summing it.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.continuous_kummer`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.hasDerivAt_kummer`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.kummer_contiguous`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.kummer_ode`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.kummer_zero`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.one_le_kummer`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Series.summable_kummer`
- Dependency: [D5/S3/Analytic/KummerRatio/Defs](Defs.md)
