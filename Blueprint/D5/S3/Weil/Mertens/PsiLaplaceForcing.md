# PsiLaplaceForcing

## Abstract

Exact signed psi-tail substitution

**Theorem 1.1 (Exact signed psi-tail substitution).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceForcing.fpsi_eq_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceForcing.fpsi_eq_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original fpsi(u)=-Jpsi(exp u) equals the negative integral of qpsi(v)*(v+1)/v^2 over v>u, by the exponential substitution with its Jacobian.

**Theorem 1.2 (Entire positive cutoff boundary).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceForcing.boundary_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceForcing.boundary_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

boundary(U,s)=U^2*fpsi(U)*exp(-sU) is entire in s. It is consumed in the forcing pole proof.

**Theorem 1.3 (Full meromorphic Euler coefficient).**

Lean statement: `D5/S3/Weil/Mertens/PsiLaplaceForcing.actual_forcing_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/PsiLaplaceForcing.actual_forcing_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi(U,s)=-Mpsi prime(U,s)+Mpsi(U,s)+boundary(U,s). Every actual nontrivial strip zero gives the full complex double pole of order -2 and normalized coefficient -m/rho. Adding the entire positive boundary preserves this coefficient. The source simple pole and both full punctured limits are included. No radial replacement or negative-half-plane integral convergence assumption is used.

## References

- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceForcing.actual_forcing_poles`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceForcing.boundary_analytic`
- Truth anchor: `D5/S3/Weil/Mertens/PsiLaplaceForcing.fpsi_eq_tail`
- Dependency: [D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope](../../Arith/Robin/Analytic/RHSharpArithmeticEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/PsiLaplaceContinuation](PsiLaplaceContinuation.md)
