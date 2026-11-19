# Continuous sampling on sublinear bands

## Abstract

Discrete fourth moments control continuous second and fourth moments throughout every sublinear polynomial band.

Let E(x)=psi(x)-x, D(v,x)=E(x+v)-E(x), N=floor(Y), H=floor(v), and L=log Y. Fix 0<alpha<beta<1. Assume A>=1 and, uniformly for Y^alpha<=v<=Y^beta and all sufficiently large real Y, the discrete fourth moment sum over 1<=n<=N is at most A Y v^2 L^2.

**Theorem 1.1 (Asymptotically exact second moment sampling).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.second_sampling_uniform_of_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.second_sampling_uniform_of_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every eta>0, the absolute difference between the continuous second moment integral from one to Y and the discrete second moment at N,H is at most eta Y v log(Y/v), uniformly on this band for sufficiently large Y. The pointwise logarithmic replacement error tends to zero after normalization. The exact terminal cell correction is bounded by D(H,N)^2; its square is at most the discrete fourth moment. Thus its relative size is O(sqrt(A/Y)/(1-beta)), which tends to zero for every beta<1.

**Theorem 1.2 (Continuous fourth moment band bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.fourth_band_bound_of_discrete`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.fourth_band_bound_of_discrete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists C4>=0 such that the integral of |D(v,x)|^4 from one to Y is at most C4 Y v^2 log^2(Y/v), uniformly on the exponent band for all sufficiently large Y. This is the predicate FourthMomentBandBoundFor for E=psi-id. The prefix replacement estimate and the discrete fourth bound control the continuous fourth moment. The inequality log(Y/v)>=(1-beta)log Y converts its logarithmic normalizer.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.fourth_band_bound_of_discrete`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.second_sampling_uniform_of_fourth`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs](../FourthMomentBandDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry](SingleLengthBandGeometry.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments](SingleLengthMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates](UniformRates.md)
