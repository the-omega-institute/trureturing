# The compact adjoint of the forward price kernel

## Abstract

The literal Mellin adjoint retains the complete signed arithmetic response of the original forward kernel.

**Theorem 1.1 (Compact support at every evaluation point).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_eq_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_eq_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Mellin adjoint q_s(t) is the integral over x>=x0 of x^(-s-1)*k(x,t). For each t it equals the compact integral over x in [x0,max(x0,t)]. Centers x>=t have zero kernel value.

**Theorem 1.2 (Absolute integrability in the center variable).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_center_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_center_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=4, every complex s and real t give an absolutely integrable center integrand x^(-s-1)*k(x,t) on [x0,infinity). Its support is compact and its Mellin weight is continuous there.

**Theorem 1.3 (The complete signed response of the price kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.forwardResponse_eq_prefix_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Adjoint.forwardResponse_eq_prefix_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>1, T(x) equals the sum of Lambda(n)*k(x,n) for 1<=n<=floor(B(x)), minus the integral of k(x,t) over [x,B(x)]. The normalization sqrt(x)/(w(x)*H(x)^2) is exactly 1/(w(x)*x^(11/10)); the initial atom is excluded and the terminal atom has zero price weight.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_center_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.adjointKernel_eq_compact`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Adjoint.forwardResponse_eq_prefix_kernel`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Transport](Transport.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutAggregate](../OriginalMovingCutAggregate.md)
