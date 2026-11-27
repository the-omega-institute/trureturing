# Möbius shell sums at adjacent reciprocal scales

## Abstract

Möbius shell sums at adjacent reciprocal scales

**Theorem 1.1 (Uniform estimate between integer samples).**

Lean statement: `D5/S3/Weil/Analytic/NymanShellScale.scale_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanShellScale.scale_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose W vanishes outside (1, 2) and has Lipschitz constant K. For 1/(N+1) ≤ t ≤ 1/N and N ≥ 1, the two scaled sums differ by at most 10K. Truncating both sums at 2(N+1) bounds the number of terms, and each term changes by at most 2K/N.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanShellScale.scale_difference`
- Dependency: [D5/S3/Weil/Analytic/NymanShellMellin](NymanShellMellin.md)
