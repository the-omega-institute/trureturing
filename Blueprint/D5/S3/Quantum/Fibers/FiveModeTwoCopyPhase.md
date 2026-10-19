# Five-Mode Two-Copy Phase Magnitude

## Abstract

A real joint rank-one effect on two copies detects the squared hidden phase magnitude.

Use the five-coordinate phase mixture from FiveModePhaseLift. On two copies, the ray supported at (2,2) and (4,4) with coefficients 1 and -1 defines bellEffect. For q in the real closed unit interval, twoCopyProbability(q) is the real part of the trace of this effect against the Kronecker square of mixture(q).

**Theorem 1.1 (Two-copy Bell readout).**

$$\forall q\in \operatorname{IccReal}(0,1),\operatorname{PSD}(bellEffect)\land \operatorname{Tr}(bellEffect)=1\land bellEffect \cdot bellEffect=bellEffect\land \operatorname{twoCopyProbability}(q)=\frac{1+{1-2q}^{2}}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.two_copy_bell_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized real Bell effect is positive, trace one, and idempotent. Its two-copy probability on the phase mixture is exactly (1 + (1 - 2q)^2) / 4. The readout distinguishes the balanced mixture from the endpoints but is invariant under q ↦ 1-q.

This is a finite-dimensional operational result. It supplies no Source, kappa, p4, rho44, or rho24 bridge, no physical preparation, and no QFT realization.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.two_copy_bell_readout`
- Dependency: [D5/S3/Quantum/Fibers/FiveModePhaseLift](FiveModePhaseLift.md)
