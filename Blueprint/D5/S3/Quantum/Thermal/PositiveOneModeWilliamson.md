# Positive One-Mode Williamson Form

## Abstract

Every positive one-mode quadratic energy has a positive symplectic normal form.

**Theorem 1.1 (A positive quadratic form becomes an isotropic oscillator).**

$$\forall a, b, c, \operatorname{PosDef}\left(\operatorname{matrix2}\left(a, b, b, c\right)\right) \Rightarrow \exists omega, M, 0 < omega \land \operatorname{transpose}\left(M\right) \cdot \operatorname{matrix2}\left(0, 1, -1, 0\right) \cdot M = \operatorname{matrix2}\left(0, 1, -1, 0\right) \land \operatorname{transpose}\left(M\right) \cdot \operatorname{matrix2}\left(a, b, b, c\right) \cdot M = omega \cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.positive_one_mode_williamson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real symmetric positive-definite two-by-two matrix S, there is a positive frequency omega and a symplectic matrix M with M-transpose S M equal to omega times the identity.

The symplectic identity uses the physical q,p Poisson matrix with upper-right entry +1 and lower-left entry -1. This statement has one mode; the general finite-mode normal form requires a separate construction.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.positive_one_mode_williamson`
