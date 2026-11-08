# Clipped cusps and sparse perturbations

## Abstract

Clipped logarithmic cusps and sparse perturbations for common-band variance sharpness.

**Definition 1.1 (Clipped logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithm of min(k,max(h,abs(y)))/k clips the radial argument between the inner and outer radii.

**Definition 1.2 (Unit logarithmic jump).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.logJump`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.logJump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit logarithmic jump at z is log(abs(z+1))-log(abs(z)).

**Definition 1.3 (Forward cusp average).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cusp average integrates the forward difference of the clipped logarithm at displacement s*q over the unit interval.

**Definition 1.4 (Cusp cross energy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspCrossEnergy`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspCrossEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cusp cross energy integrates over [0,k] the product of the forward cusp averages of lengths h and k.

**Definition 1.5 (Geometric spike centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth spike center is the real number 10^n.

**Definition 1.6 (Spike amplitude).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.amplitude`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth amplitude is the square root of X_n*log(X_n)/log(log(X_n)), where X_n=10^n.

**Definition 1.7 (One logarithmic spike).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth spike is its amplitude times the clipped logarithm with radii X_n^a and X_n^b, translated to center X_n.

**Definition 1.8 (Separated spike radii).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.AdmissibleStart`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.AdmissibleStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A starting index n0 is admissible when n0>=1 and X_n^b<=X_n/10 for every n>=n0.

**Definition 1.9 (Sparse logarithmic perturbation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The perturbation at x is the sum of the spikes with indices n0+j for natural j.

**Definition 1.10 (Pointwise spike scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spikePointScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spikePointScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pointwise comparison scale is sqrt(x)*log(x)^(3/2)/sqrt(log(log(x))).

**Definition 1.11 (Near-optimal cross-energy scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.nearOptScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.nearOptScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The near-optimal comparison scale is X^(1-b)*log(X)^3/log(log(X)).

**Definition 1.12 (Reduced logarithmic scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.reducedLogScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.reducedLogScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced comparison scale is X^(1-b)*log(X)^(3-eta).

**Definition 1.13 (Negligible variance on a band).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.CumulativeVarianceBandNegligibleFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.CumulativeVarianceBandNegligibleFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The absolute normalized variance V_F(Y,u)/(Y*u*log(Y/u)) tends uniformly to zero for Y^alpha<=u<=Y^beta.

Set clippedLog(h,k,y)=log(min(k,max(h,abs(y)))/k) and logJump(z)=log(abs(z+1))-log(abs(z)). The forward cusp average cuspAverage(h,k,q,y) integrates clippedLog(h,k,y+s*q)-clippedLog(h,k,y) over 0<=s<=1. The cusp cross energy integrates the product of the averages at lengths h and k over 0<=y<=k.

The centers are X_n=10^n, the amplitudes are A_n=sqrt(X_n*log(X_n)/log(log(X_n))), and the nth spike is A_n*clippedLog(X_n^a,X_n^b,x-X_n). An admissible start n0 is at least one and satisfies X_n^b<=X_n/10 for every n>=n0. The perturbation is the sum of the spikes indexed by n0+j for natural j.

The pointwise scale is sqrt(x)*log(x)^(3/2)/sqrt(log(log(x))). The near-optimal cross-energy scale is X^(1-b)*log(X)^3/log(log(X)), and the reduced-log comparison scale is X^(1-b)*log(X)^(3-eta). Negligible band variance means that the absolute value of V_F(Y,u)/(Y*u*log(Y/u)) tends uniformly to zero for Y^alpha<=u<=Y^beta. These definitions concern real functions and make no assumption about an arithmetic error.

**Theorem 1.14 (Positive centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every center X_n=10^n is strictly positive.

**Theorem 1.15 (Increasing centers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map n to X_n=10^n is strictly increasing on the natural numbers.

**Theorem 1.16 (Centers escape to infinity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sequence X_n tends to positive infinity as n tends to infinity.

**Theorem 1.17 (An admissible starting index exists).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.exists_admissibleStart`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.exists_admissibleStart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real b<1 there exists n0>=1 such that X_n^b<=X_n/10 for every n>=n0. Indeed, X_n^(b-1) tends to zero.

**Theorem 1.18 (Vanishing beyond the outer radius).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If k>0 and abs(y)>=k, then clippedLog(h,k,y)=0, for every real h.

**Theorem 1.19 (Outer support bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real a and b and every natural n, the support of the nth spike is contained in [X_n-X_n^b,X_n+X_n^b]. Outside this interval the clipped logarithm equals log(1)=0.

**Theorem 1.20 (Strict separation of outer intervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_intervals_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_intervals_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an admissible start, if i<j, then the right endpoint of the outer interval at index n0+i is strictly less than the left endpoint at index n0+j.

**Theorem 1.21 (Locally finite spike supports).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_locallyFinite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_locallyFinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an admissible start, the supports of the spikes indexed by n0+j form a locally finite family. Each support has left endpoint at least nine tenths of its center, and these lower bounds tend to infinity.

**Theorem 1.22 (Finite support in the summation index).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_finite_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an admissible start and at each fixed real x, only finitely many spikes in the perturbation are nonzero.

**Theorem 1.23 (A single possible spike on a neighbourhood).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_locally_single_spike`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_locally_single_spike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an admissible start, every real point has a neighbourhood U such that any two spikes nonzero anywhere in U have the same index. The closed outer support intervals are locally finite and pairwise disjoint: their radii are at most one tenth of their centers and successive centers differ by a factor of ten.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.AdmissibleStart`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.CumulativeVarianceBandNegligibleFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.amplitude`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_pos`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_strictMono`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.center_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.clippedLog_eq_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspAverage`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.cuspCrossEnergy`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.exists_admissibleStart`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.logJump`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.nearOptScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_finite_support`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.perturbation_locally_single_spike`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.reducedLogScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spikePointScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_intervals_disjoint`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_locallyFinite`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs.spike_support_subset`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
