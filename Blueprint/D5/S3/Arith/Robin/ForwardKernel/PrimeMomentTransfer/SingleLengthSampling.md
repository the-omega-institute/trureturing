# Single-length cumulative sampling

## Abstract

Cumulative scalar moments admit floor sampling with explicit terminal corrections.

**Theorem 1.1 (Endpoint discrepancy on the full prefix).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.sampling_cumulative_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.sampling_cumulative_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Y at least two, lengths between one and Y, and base points between one and Y, the continuous increment differs from the increment with both length and base point rounded down by at most 2 log(4Y)+2. Beyond the length scale this uses the dyadic sampling estimate; the remaining prefix is controlled by the endpoint lattice crossings.

**Theorem 1.2 (Fourth integrability of sampled increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real cutoff and length, the floor-sampled lattice increment belongs to L4 on the closed interval from one to the cutoff. Only finitely many lattice values occur there.

**Theorem 1.3 (Exact terminal-cell correction).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.floor_integral_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.floor_integral_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real sequence F and Y at least one, set N=floor(Y). The integral of F(floor(x)) from one to Y minus the sum of F(n) over 1 through N equals (Y-N-1)F(N). In particular, an integral cutoff contributes minus its final sample.

**Theorem 1.4 (Discrete control of the sampled fourth integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_fourth_le_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_fourth_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Y at least one, the fourth integral of the increment with floored length and base point is at most its discrete fourth-moment prefix through floor(Y). The exact terminal-cell correction is nonpositive.

**Theorem 1.5 (Stability of scalar moments under fourth-moment perturbations).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.scalar_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.scalar_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a probability space, suppose f and g have fourth moments at most C and their difference has fourth moment at most e^4, with C and e nonnegative. For k equal to two or four, their kth moments differ by at most k e C^((k-1)/4). This is the finite-product replacement bound applied to identical factors.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.floor_integral_identity`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.sampling_cumulative_pointwise`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.scalar_stability`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_fourth_le_sum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.step_memLp`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature](CellQuadrature.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs](SingleLengthMSDefs.md)
