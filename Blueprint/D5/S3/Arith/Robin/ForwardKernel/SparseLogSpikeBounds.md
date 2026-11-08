# Variance bounds for sparse logarithmic spikes

## Abstract

Sparse logarithmic spikes have uniformly negligible variance on every sublinear exponent band.

Let X_n=10^n and A_n=sqrt(X_n log(X_n)/log(log(X_n))). The perturbation F is the sum, from an admissible starting index, of A_n times the logarithm clipped between radii X_n^a and X_n^b, translated to X_n. The existing pointwise theorem perturbation_pointwise_bound in SparseLogSpikes gives F(x)=O(sqrt(x) log(x)^(3/2)/sqrt(log(log(x)))). CommonBandSharpness uses that theorem directly.

**Theorem 1.1 (Uniform short-step variance bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<b, beta<1 and an admissible starting index, there is C>0 such that, for all sufficiently large Y and every 0<u<=Y^beta, the integral of (F(x+u)-F(x))^2 over [1,Y] is at most C Y u log(Y)/log(log(Y)). CommonBandSharpness consumes this estimate.

The step is at most Y. A contributing spike therefore has center at most 3Y. Choose m with X_m<=3Y<X_(m+1); then 0.3Y<X_m<=3Y. Truncate the increment to these finitely many spikes and apply the L2 triangle inequality. ClippedLogEnergy bounds each squared translation norm by an absolute constant times u A_n^2. SparseLogSpikes bounds the amplitude sum by a constant times A_m, and comparison of X_m with Y gives A_m^2<=12 Y log(Y)/log(log(Y)).

**Theorem 1.2 (Negligibility on the common exponent band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_band_negligible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_band_negligible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<a<b<beta<1, the ratio of the cumulative variance of F to Y u log(Y/u) tends uniformly to zero for Y^alpha<=u<=Y^beta. Indeed log(Y/u)>=(1-beta) log(Y), so the ratio is O(1/log(log(Y))). CommonBandSharpness combines this with variance stability.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_band_negligible`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikeBounds.perturbation_variance_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes](SparseLogSpikes.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
