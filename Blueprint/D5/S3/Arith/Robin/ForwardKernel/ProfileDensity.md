# Lipschitz density in L1

## Abstract

Lipschitz functions on the unit interval approximate every real integrable profile in L1.

**Theorem 1.1 (Approximation by Lipschitz profiles).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileDensity.exists_lipschitz_profile_approx`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileDensity.exists_lipschitz_profile_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real Borel integrable profile g on (0,1) and every epsilon>0, there is a Borel integrable profile f that is Lipschitz on [0,1] and satisfies integral |g-f| < epsilon. First approximate g in L1 by a bounded continuous function. Approximate the latter uniformly on [0,1] by a polynomial, with both errors at most epsilon/3. The polynomial derivative is bounded on the compact interval; the mean value theorem gives a finite Lipschitz constant. The integral triangle inequality yields the strict error bound.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileDensity.exists_lipschitz_profile_approx`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
