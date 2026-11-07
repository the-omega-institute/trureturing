# Sparse logarithmic spikes

## Abstract

Geometrically separated logarithmic spikes give a continuous perturbation with controlled amplitudes.

The centers are X_n=10^n, the radii are X_n^a and X_n^b, and the amplitudes are sqrt(X_n*log(X_n)/log(log(X_n))). An admissible starting index makes every outer radius at most X_n/10. The existing support separation and locally finite support family allow the sum to be treated as a finite sum near every point.

**Theorem 1.1 (Support near the center).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.spike_support_tenth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.spike_support_tenth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible spike is supported in [0.9*X_n,1.1*X_n]. This locates the centers that can contribute to a variance integral.

**Theorem 1.2 (Continuity of the sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an admissible start the perturbation is continuous. The sum has finite support at each point, so its infinite sum equals its finite-support sum, and the locally finite family of continuous summands gives continuity.

**Theorem 1.3 (Local boundedness and measurability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_locallyBoundedMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_locallyBoundedMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The perturbation is Borel measurable and bounded on every closed finite interval. These are the regularity hypotheses used when perturbing variance.

**Theorem 1.4 (Isolation on three center lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_eq_spike_on`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_eq_spike_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at or above the starting index and x in [X_n,3*X_n], the perturbation equals its n-th spike. Every earlier and every later spike vanishes throughout this interval.

**Theorem 1.5 (Isolation of complete forward ranges).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_forward_eq_spike`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_forward_eq_spike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x in [X_n,2*X_n] and 0<=u<=2*X_n^b, the value at x+u is exactly the n-th spike. This covers all forward increments in the transport of the two moving lengths.

**Theorem 1.6 (The amplitude ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_ratio_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_ratio_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio of consecutive amplitudes tends to sqrt(10). The identity log(X_(n+1))=log(X_n)+log(10) reduces both logarithmic correction factors to ratios tending to one.

**Theorem 1.7 (Summing the amplitudes).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_partial_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_partial_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a fixed positive constant C such that, for all sufficiently large m, the sum of amplitudes from zero through m is at most C times the m-th amplitude. Consecutive amplitudes eventually at least double; a fixed initial sum is absorbed in C. This supplies the coefficient estimate for the sparse perturbation variance.

**Theorem 1.8 (Pointwise growth).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_pointwise_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_pointwise_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a<b, the perturbation is O(sqrt(x)*(log(x))^(3/2)/sqrt(log(log(x)))) as x tends to infinity. At a nonzero point only one spike contributes. Its depth is at most (b-a)*log(X_n), and x and X_n differ by at most a factor of two on its support. The logarithmic factors are compared explicitly there. This gives the pointwise estimate in the final near-optimality theorem.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_partial_sum_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.amplitude_ratio_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_continuous`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_eq_spike_on`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_forward_eq_spike`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_locallyBoundedMeasurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.perturbation_pointwise_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.spike_support_tenth`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy](ClippedLogEnergy.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs](CommonBandSharpnessDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/CuspAverages](CuspAverages.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds](DyadicSmoothingBounds.md)
