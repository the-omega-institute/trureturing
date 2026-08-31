# Off-Line Strong Negative Certificate

## Abstract

Every off-line zero yields an admissible shift with a quantitative strong negative certificate.

**Theorem 1.1 (Off-line strong negative certificate).**

$$\forall rho\in\mathbb{C}, \forall delta\in\mathbb{R}, \forall gamma\in\mathbb{R}, (rho=\frac{1}{2}+delta+i\cdot gamma\land 0<delta\land xiReading(rho)=0) \Rightarrow \exists omega\in\mathbb{R}, 0<omega\land omega<delta\land xiReading(rho-2\cdot omega)\neq0\land diagonalValue(omega,-gamma+i\cdot (delta-omega))=-\frac{1}{omega\cdot (delta-omega)}\land diagonalValue(omega,-gamma+i\cdot (delta-omega))<0\land diagonalValue(omega,-gamma+i\cdot (delta-omega))\leq-\frac{4}{delta^2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/OffLineStrongNegativeCertificate.off_line_strong_negative_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire shifted xi reading cannot vanish throughout an interval: analytic isolation and the value xiReading zero equals one half produce a positive shift below the off-line displacement where the shifted reading is nonzero.

At that shift, the frozen one-point computation gives the exact negative reciprocal value, strict negativity, and the sharp minus-four-over-delta-squared bound.

## References

- Truth anchor: `D5/S3/Weil/ZetaCore/OffLineStrongNegativeCertificate.off_line_strong_negative_certificate`
- Dependency: [D5/S3/Weil/ZetaCore/OffLinePickWitness](OffLinePickWitness.md)
