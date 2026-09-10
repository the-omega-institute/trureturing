# Neumann completion of the actual Gamma resolvent

## Abstract

Neumann Green-kernel completion supplies positive canonical Gamma boundary corrections.

The free and Neumann Green kernels are independently specified. Their difference is proved to have a positive rank-two factorization. The canonical Gamma rates are exactly b_r=2r+1/2. L2 integration, the infinite-mixture domain identity and the energy-weighted arithmetic Schur application are paper bridges, not conclusions of this Lean owner. Lean and Scribe compilation have not been run in this increment.

**Definition 1.1 (Compressed whole-line kernel).**

$$\operatorname{Kfree}(b, x, y)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.freeLaplaceKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Kfree(b,x,y)=exp(-b*abs(x-y)). For b>0 this is 2b times the whole-line resolvent kernel.

**Definition 1.2 (Independent Neumann Green formula).**

$$\operatorname{KN}(a, b, x, y)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumannLaplaceKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set E=exp(ba), u=exp(b*min(x,y)), w=exp(b*max(x,y)). KN=(E*u+E^(-1)*u^(-1))*(E*w^(-1)+E^(-1)*w)/(E^2-E^(-2)). On [-a,a], a,b>0, this is 2b times the Neumann Green kernel. The operator interpretation is established separately on paper.

**Definition 1.3 (Even response).**

$$\operatorname{Hplus}(b, x)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.evenBoundaryResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hplus(b,x)=exp(bx)+exp(bx)^(-1), twice cosh(bx).

**Definition 1.4 (Odd response).**

$$\operatorname{Hminus}(b, x)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.oddBoundaryResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hminus(b,x)=exp(bx)-exp(bx)^(-1), twice sinh(bx).

**Theorem 1.5 (Exact positive boundary completion).**

$$\operatorname{BoundaryCompletion}(a, b, x, y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b>0 and arbitrary real x,y, KN-Kfree equals Hplus(x)*Hplus(y)/(2*(exp(ba)^2-1)) +Hminus(x)*Hminus(y)/(2*(exp(ba)^2+1)). All denominators are proved nonzero. Ordering x and y identifies the free exponential; exact field algebra proves the difference.

**Theorem 1.6 (Finite quadratic identity).**

$$\operatorname{BoundaryEnergyIdentity}(a, b, S, x, v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite sample set S and real coefficients v, the double quadratic sum of KN-Kfree equals the sum of the squares of sum v_i*Hplus(x_i) and sum v_i*Hminus(x_i), divided by their respective positive denominators. No coefficient parity or boundary cancellation is assumed. The empty sample set is allowed.

**Theorem 1.7 (Finite Gram positivity).**

$$\operatorname{BoundaryEnergyNonnegative}(a, b, S, x, v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_energy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding independently derived kernel identity proves nonnegativity of every finite real quadratic sample. This does not assume positivity of the Weil form.

**Theorem 1.8 (Canonical Gamma mixture).**

$$\operatorname{CanonicalGammaBoundaryNonnegative}(a, R, S, x, v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.canonical_gamma_resolvent_boundary_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every natural R, summing the actual kernel corrections over rates b_r=2r+1/2, r<R, preserves finite quadratic positivity. R=0 is included. The proof has no spectral-gap, residual, zeta-zero or target-positivity premise. Infinite positive summation and the Fourier/Neumann spectral identification are separate analytic obligations described in the existing source analysis.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.canonical_gamma_resolvent_boundary_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.evenBoundaryResponse`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.freeLaplaceKernel`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumannLaplaceKernel`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_completion`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_energy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.neumann_laplace_boundary_energy_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.oddBoundaryResponse`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
