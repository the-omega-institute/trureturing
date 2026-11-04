# Weighted coefficient curves and a charge kernel

## Abstract

Positive analytic coefficient curves generate the full continuous charge kernel in a fourth weighted sequence norm.

**Theorem 1.1 (A genuine Hilbert carrier and its constrained core).**

Lean statement: `D5/S3/Analytic/PowerSeries/WeightedChargeKernelCore.weighted_charge_kernel_core_of_scalar_curve`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/WeightedChargeKernelCore.weighted_charge_kernel_core_of_scalar_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s(n)=(n+1)^2, z(0)=1, |z(n)|<=1, c(n) nonzero and |c(n)|<=C(9/2)^n with C>=0. Suppose 0<r<=1/36. For every t in (0,r), suppose the scalar coefficients d(t,n) have the actual HasSum sum z(n)d(t,n)=0 and d(t,n)=c(n)t^n for every n>=1. There exists a curve f in ordinary real l2 with coordinates f(t,n)=s(n)d(t,n), whose closed real span equals the kernel of the continuous functional inner(a,w), a(n)=z(n)/s(n). Membership of the actual coefficients in the weighted space, their constant coordinate and density are conclusions.

The proof constructs a in l2 using the fourth-power p-series, projects the coordinate expansion continuously onto its charge kernel, and uses vector-valued multilinear power series to extract all constrained directions from positive parameter values. A finite correction constructs the scalar curve carrier; equality of charge and all positive-index coordinates removes that correction. This theorem concerns the weighted coefficient topology. It does not assert closure or density of its synthesized image in a different physical function space.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/WeightedChargeKernelCore.weighted_charge_kernel_core_of_scalar_curve`
