# Power excursions of the forward kernel

## Abstract

Power mean-square mass and absolute excursions of the forward response.

**Theorem 1.1 (A lower bound on power windows).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_power_window_mean_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_power_window_mean_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Riemann hypothesis, the von Koch bound, the paired xi expansion, and the averaged Montgomery lower bound for the positive zeta spectrum. There are positive c and M0 greater than one such that, whenever M is at least M0, the integral of the square of the forward response against dx/x from exp(-2) M^16 to exp(2) M^20 is at least c M (log M)^2. The general paired Laplace window bound applies to the logarithmic forward response. The wider Gaussian strip bound and the canonical local zero count provide its inputs. Exponential substitution transports the logarithmic window exactly.

**Theorem 1.2 (Arbitrarily large absolute power excursions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_omega_abs_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_omega_abs_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses there is c1 greater than zero such that for every real X some x at least X and greater than three satisfies abs(forwardResponse(x)) at least c1 x^(1/40) sqrt(log x). The logarithmic window has length 4 log M plus 4, so its lower mean-square mass forces a point whose squared response is at least c M log M divided by 16. On that window the square of the desired power weight is bounded by the same quantity when c1 equals sqrt(c/352) divided by exp(1). An upper bound on an integral of a bounded function supplies the point without any continuity or attainment assumption.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_omega_abs_power`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare.forward_kernel_power_window_mean_square`
- Dependency: [D5/S3/Analytic/Oscillation/PairedLaplaceWindow](../../../Analytic/Oscillation/PairedLaplaceWindow.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/GaussianLaplace](GaussianLaplace.md)
- Dependency: [D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount](../../../Weil/ZeroData/ZetaSpectrumLocalCount.md)
