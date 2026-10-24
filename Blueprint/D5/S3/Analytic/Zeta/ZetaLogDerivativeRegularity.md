# The normalized zeta logarithmic derivative

## Abstract

Removing the pole of zeta at one before taking its logarithmic derivative gives a principal term regular on the nonnegative real axis. The translated nontrivial zeros have negative half-integer residues.

**Theorem 1.1 (The normalized zeta factor has no positive real zero).**

Lean statement: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_ne_zero_real`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_ne_zero_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire completion Z(s) of (s-1)zeta(s) is nonzero at every positive real s. Away from one this follows from the sign of real zeta; at one its value is one.

**Theorem 1.2 (Cancellation of the density pole).**

Lean statement: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z(s) be the entire completion of (s-1)zeta(s). At a point s different from one half where zeta(s+1/2) is nonzero, the quantity -Z'(s+1/2)/(2Z(s+1/2)) equals -zeta'(s+1/2)/(2zeta(s+1/2))-1/(2(s-1/2)).

**Theorem 1.3 (Regularity along the nonnegative real axis).**

Lean statement: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_analyticAt_real`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_analyticAt_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative real sigma, the cancelled principal term is complex analytic near sigma. Zeta has no real zero between zero and one, has no zero to the right of one, and Z(1)=1. These facts include regularity at sigma=0 and sigma=1/2.

**Theorem 1.4 (Isolation of translated nontrivial zeros).**

Lean statement: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_eventually_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_eventually_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nontrivial zeta zero rho, the function Z(s+1/2) is nonzero in a punctured neighborhood of rho-1/2. The local factorization into a positive integer power times an analytic nonvanishing function gives the isolation.

**Theorem 1.5 (Multiplicity determines the translated residue).**

Lean statement: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_zero_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_zero_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nontrivial zeta zero rho there is a positive integer m such that (s-(rho-1/2)) times the cancelled principal term tends to -m/2 as s approaches rho-1/2 through distinct points. The analytic-unit factorization of zeta supplies m; the subtracted density term is regular at this translated zero.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_eventually_ne_zero`
- Truth anchor: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.normalized_zeta_ne_zero_real`
- Truth anchor: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_analyticAt_real`
- Truth anchor: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_eq`
- Truth anchor: `D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.regularizedPrincipal_zero_residue`
- Dependency: [D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization](../../Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.md)
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](../../Weil/ZetaBridge/AlternatingZetaContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite](../../Weil/ZetaBridge/ZeroDataNonemptyIffInfinite.md)
