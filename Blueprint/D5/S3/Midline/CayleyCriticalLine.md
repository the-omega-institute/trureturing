# Cayley Ratio and the Critical Line

## Abstract

The scalar Cayley ratio has unit modulus exactly on the critical line.

**Theorem 1.1 (Unit circle corresponds to the critical line).**

$$\forall s\in\mathbb{C},\ \lvert\frac{s - 1}{s}\rvert = 1 \Leftrightarrow \Re(s) = \frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/CayleyCriticalLine.cayley_ratio_norm_one_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof treats the totalized division value at zero separately. For a nonzero parameter, the squared norm defect is (1 - 2 Re(s)) divided by the norm square of s.

Thus unit modulus is equivalent to vanishing horizontal displacement from real part one half.

## References

- Truth anchor: `D5/S3/Midline/CayleyCriticalLine.cayley_ratio_norm_one_iff_critical_line`
