# Simple-Zero Logarithmic Residue

## Abstract

A simple analytic zero has unit normalized logarithmic residue.

**Theorem 1.1 (A simple zero has unit logarithmic residue).**

$$\lim_{z \to z_0} (z - z_0) \operatorname{logDeriv}(f)(z) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/SimpleZeroLogResidue.simple_zero_has_unit_logarithmic_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be complex analytic at z_0, with f(z_0) = 0 and nonzero derivative there. Then (z - z_0) times the logarithmic derivative of f tends to one as z approaches z_0 away from the center. Thus a simple zero contributes unit local residue, the analytic invariant behind one full phase winding.

This declaration is a thin wrapper around mathlib's AnalyticAt.tendsto_mul_logDeriv_simple_zero. The source atom's finite numerical phase difference is not reproduced as an exact equality; the theorem records the stronger general local law that explains that reading.

## References

- Truth anchor: `D5/S3/Zeros/SimpleZeroLogResidue.simple_zero_has_unit_logarithmic_residue`
