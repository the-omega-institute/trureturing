# Weil Rayleigh Enclosure Mode Capture

## Abstract

Two-sided Rayleigh enclosure and codimension-one coercivity capture the ground eigendirection without requiring a small operator residual.

D is a real linear operator domain, iota:D->H is its embedding into a real Hilbert space and A:D->H is a symmetric operator action on that domain. The theorem is therefore compatible with an unbounded Friedrichs realization rather than replacing it by a bounded matrix. The arithmetic application must separately establish the real-invariant domain bridge for the canonical Weil form.

**Theorem 1.1 (A certified Rayleigh interval captures the ground line).**

$$\operatorname{SymmetricOnDomain}(A)\land \operatorname{Normalized}(k)\land \operatorname{Normalized}(u)\land \operatorname{GroundEigenpair}(A, u)\land ell\leq \operatorname{GroundEigenvalue}(A, u)\leq \operatorname{Rayleigh}(A, k)\leq M\land \operatorname{ComplementEnergyAtLeast}(A, k, T)\land M< T\Rightarrow 0< T-M\land {T-M} \operatorname{normSq}(u-\operatorname{inner}(k, u) k)\leq M-ell$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilRayleighEnclosureModeCapture.rayleigh_enclosure_mode_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write alpha=<k,u> and v=u-alpha*k. Symmetry and the eigenvalue equation give the exact identity q(v)=lambda*||v||^2 +alpha^2*(q(k)-lambda). Cauchy-Schwarz gives alpha^2<=1. The coercive lower bound on k-perp then yields (T-M)||v||^2<=M-ell. This replaces the usual residual/gap quantity by three values directly exposed by a Schur or LDL certificate: a ground lower bound ell, a candidate upper bound M and a complementary threshold T. No claim about an unbounded-scale Xi limit is made by this theorem itself.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilRayleighEnclosureModeCapture.rayleigh_enclosure_mode_capture`
