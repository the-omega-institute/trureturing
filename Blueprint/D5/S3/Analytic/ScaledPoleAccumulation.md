# Scaled Candidate-Pole Accumulation

## Abstract

Scaled candidate poles converge to any targeted point on the imaginary axis.

**Theorem 1.1 (Scaled candidate poles approach the imaginary axis).**

$$\lim_{n\to\infty}\left(\frac{1}{2c_n}+i\frac{\Gamma_n}{c_n}\right)=it$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ScaledPoleAccumulation.scaled_candidate_poles_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c_n be real scales tending to positive infinity and let gamma_n be real heights with gamma_n/c_n tending to a target t. The complex points 1/(2c_n) + i gamma_n/c_n then converge to it: the real parts vanish by inversion at infinity, while the imaginary parts converge by the supplied normalized-height limit.

The declaration isolates the scaling step in the source atom. It does not prove that zeros of a particular analytic function provide the height approximation; that number-theoretic distribution input is an explicit hypothesis rather than an imported claim.

## References

- Truth anchor: `D5/S3/Analytic/ScaledPoleAccumulation.scaled_candidate_poles_tendsto`
