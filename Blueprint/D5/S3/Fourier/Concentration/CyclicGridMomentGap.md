# First-moment gap for separated phase supports

## Abstract

Separation from orthogonality improves the first-moment bound for a small second moment.

**Theorem 1.1 (A quantitative gap from pairwise phase separation).**

$$\varepsilon \leq \frac{\delta}{3} \implies \left|m\right|^{2} \leq \frac{1 + \varepsilon}{2}-\frac{\delta^{2}}{684}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicGridMomentGap.first_moment_gap_of_small_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let z be a finite indexed family of complex unit phases with real weights w that are nonnegative and sum to one. Write m for the weighted sum of the phases and b for the weighted sum of the squared phases. Set epsilon to the magnitude of b and take a positive real delta. For every pair of indices with positive weight, assume the absolute real part of the first phase times the conjugate of the second phase is at least delta.

A positive-weight diagonal pair gives delta at most one. Centering the second moment and applying the triangle inequality gives the upper bound (1+epsilon)/2 before imposing separation. The already proved stability estimates for the same weights `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability` force at least one positive-weight phase close to each of two comparison points if the deficit is too small. The real inner product of those points is controlled by the deficit and epsilon. Bounding the changes in that product gives a pair whose real inner product has absolute value strictly below delta.

**Theorem 1.2 (Explicit angular separation on a cyclic grid).**

$$\varepsilon \leq \frac{\delta}{3} \implies \left|a\right|^{2} \leq \frac{1 + \varepsilon}{2}-\frac{\delta^{2}}{684}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicGridMomentGap.cyclic_grid_fourier_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a positive integer modulus q that is not divisible by four. Let w be a nonnegative real weight of mass one on the residues modulo q. Compute its unnormalized discrete Fourier transform with the negative phase. Write epsilon for the magnitude of the coefficient at residue two and a for the coefficient at residue one. Take delta to be sin(pi/(2q)) for odd q and sin(pi/q) for even q.

For each integer difference d of residues, reduce 4d−q to a centered residue modulo 2q. It cannot vanish because q is not divisible by four. Its absolute value is at least one when q is odd and at least two when q is even. Apply sine monotonicity on the resulting interval between zero and pi/2 to bound the absolute cosine of the phase difference. The finite-phase theorem then applies to the standard additive character. At zero second coefficient the bound is 1/2 minus delta squared over 684. The separation hypothesis concerns a fixed finite support. A weighted positive-resolution bound at growing order for actual zeta ordinates remains open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicGridMomentGap.cyclic_grid_fourier_gap`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicGridMomentGap.first_moment_gap_of_small_second`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability`
- Dependency: [D5/S3/Fourier/Concentration/CyclicMomentStability](CyclicMomentStability.md)
