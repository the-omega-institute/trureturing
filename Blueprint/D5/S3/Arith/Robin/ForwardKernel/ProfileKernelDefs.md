# Moving profile kernel definitions

## Abstract

The Robin price ratio and the response of a moving profile.

**Definition 1.1 (Price ratios).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.priceRatio`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.priceRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio rho_x(u) is w(x+u)/w(x), where w(t)=(log(t)+1)/(t^2*log(t)^2) is the Robin price derivative weight.

**Definition 1.2 (Moving profile response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.profileResponse`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.profileResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For H=x^theta, the response is sqrt(x)/H^2 times the oriented integral from 0 to H of g(u/H)*(E(x+u)-E(x))*rho_x(u).

**Theorem 1.3 (The complete Chebyshev response as a constant profile).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.forwardResponse_eq_profileResponse`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.forwardResponse_eq_profileResponse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original forward response equals the moving profile response with E(x)=psi(x)-x, theta=4/5, and g identically one, as functions on the real line.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.forwardResponse_eq_profileResponse`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.priceRatio`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.profileResponse`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Transport](Transport.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](../MellinWeightedVariation.md)
