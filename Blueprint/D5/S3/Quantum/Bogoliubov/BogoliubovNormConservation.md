# Bogoliubov Norm Conservation

## Abstract

Real Bogoliubov coefficients preserve the unit hyperbolic norm.

**Theorem 1.1 (Real Bogoliubov coefficients preserve the unit norm).**

$$\forall r\in\mathbb{R},\ \left|\operatorname{cosh}(r)\right|^{2} - \left|\operatorname{sinh}(r)\right|^{2} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation.bogoliubov_norm_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the standard real squeeze parameter r, alpha = cosh(r) and beta = sinh(r) obey |alpha|^2 - |beta|^2 = 1. Pinned Mathlib provides Real.cosh_sq_sub_sinh_sq, so the Lean proof only rewrites the squared absolute values and applies that identity.

This closes only the real Bogoliubov norm-conservation identity in the source atom. It does not formalize its open-channel, Krein, or frustration criteria, nor its adiabatic asymptotic and sudden-quench limit claims.

## References

- Truth anchor: `D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation.bogoliubov_norm_conservation`
