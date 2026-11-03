# Original full-kernel certificate source

## Abstract

The complete actual-K moment certificate.

**Theorem 1.1 (actual cutoff resolvent payment).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_cutoff_resolvent_payment`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_cutoff_resolvent_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal V has abs(V)<=(8+4C+2B)exp(D/2)W. Integrating EACH finite Mangoldt atom gives the inclusive Abel identity sum w_n=exp(-D/2)psi(exp D)+(1/2)integral_[0,D]exp(-t/2)psi(exp t), including a zero tail at equality entries. Global actual psi<=(1+C)exp(t) yields sum w_n<=2(1+C)exp(D/2). Actual S/Z control pays both the continuous resolvent integral and the signed b(D)Z/2 boundary.

**Theorem 1.2 (actual continuum moment payment).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_continuum_moment_payment`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_continuum_moment_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual G(t)=integral_0^t prefix, mass and the first atomic moment give G(0)=G(D)=0. The retained finite causal Gram/FTC identities, generalized from positive to nonzero lambda, are applied at -1/2 and identified with the actual growing-exponential prefix curvature. Compact-square Fubini identifies the causal triangle with H(G), giving H(A)=-integral norm(G)^2-H(G)/4. The literal growing row is (M_D-1)g(u)+u exp(u/2)+(D-u)exp((D-u)/2), at most (M_D+D-1)g(u). The weighted complex pair integration and retained complex primitive gap therefore pay H(A)>=-((M_D+D+3)/4)delta_q E.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_continuum_moment_payment`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_cutoff_resolvent_payment`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent](ActualKernelMomentResolvent.md)
