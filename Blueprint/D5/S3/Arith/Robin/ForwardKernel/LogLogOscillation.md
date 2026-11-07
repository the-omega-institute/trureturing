# Logarithmic logarithmic oscillation of the forward response

## Abstract

The forward response has two-sided logarithmic logarithmic excursions.

**Theorem 1.1 (Two-sided log-log excursions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/LogLogOscillation.forward_kernel_omega_pm_loglog`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/LogLogOscillation.forward_kernel_omega_pm_loglog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Riemann hypothesis, the von Koch bound, and the paired xi expansion. Then some positive constant c gives arbitrarily large x with forwardResponse(x)<=-c*log(log x), and arbitrarily large x with c*log(log x)<=forwardResponse(x), while x>exp(1). The result follows by transferring the paired Laplace excursions in y and taking x=exp(y).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/LogLogOscillation.forward_kernel_omega_pm_loglog`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PairedLaplace](PairedLaplace.md)
