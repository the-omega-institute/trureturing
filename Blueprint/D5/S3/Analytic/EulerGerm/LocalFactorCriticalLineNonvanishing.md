# Golden Local-Factor Critical-Line Nonvanishing

## Abstract

Prime local factors at least five do not vanish on the pulled-back critical line.

**Theorem 1.1 (Prime local factors are nonzero on the pulled-back critical line).**

$$\forall p \in \mathbb{N}, t \in \mathbb{R},\; \left(\operatorname{Prime}\left(p\right) \land 5 \le p\right) \Rightarrow \operatorname{germLocalFactor}\left({\frac{1}{2 \times {Real.goldenRatio}^{2}}} + i \times t, p\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing.germLocalFactor_critical_line_nonzero_of_five_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p at least five and every real ordinate t, the golden local factor is nonzero at real part one over twice the square of the golden ratio.

The statement makes no claim for the primes two or three.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing.germLocalFactor_critical_line_nonzero_of_five_le`
