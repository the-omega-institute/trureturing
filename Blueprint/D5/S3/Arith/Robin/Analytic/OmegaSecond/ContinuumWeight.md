# Continuum correction at a moving cutoff

## Abstract

The continuum moving-weight integral preserves the exact power-kernel cancellation.

**Theorem 1.1 (Central continuum mass upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight.central_integral_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight.central_integral_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every P>0 and s>1, the integral over [P/2,2P] of log(1+exp(-s*abs(log(t/P)))) is at most P*(pi/sin(pi/s)-s)+(s/2+2)*P*2^(-s). The power-kernel integral is evaluated exactly before subtracting the linear ramp.

The remaining endpoint and removed-tail terms decay geometrically. The explicit upper majorant for the normalized kernel correction tends to pi^2/6. This supports the second-threshold counting upper bound; a matching lower bound is not established here.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight.central_integral_upper`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight](MovingWeight.md)
