# Logarithmically weighted frozen blocks

## Abstract

Fixed-scale mixed moments pass to finite frozen blocks, whose exact logarithmic weights approximate integration.

The cells have endpoints u_j=1+j/n. Each cell receives its exact logarithmic probability log(u_(j+1)/u_j)/log(2), rather than its Lebesgue length 1/n. Closed and left-open position indicators agree almost everywhere by the position law and null endpoints.

**Theorem 1.1 (Finite frozen block convergence).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.fixed_block_moments_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.fixed_block_moments_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume interval-weighted fixed-scale mixed moment convergence for a kernel W. Fix a positive number of cells and frozen lengths in a common bounded nonnegative interval. The finite sum of cell moments weighted by w at the left endpoints converges to the same weighted sum of W times the exact logarithmic cell masses. This uses the fixed-scale hypothesis separately on each cell, followed by convergence of a finite sum.

**Theorem 1.2 (Riemann sums with exact logarithmic masses).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.logarithmic_block_riemann`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.logarithmic_block_riemann` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous real function f on [1,2], the sum of f(u_j) times the logarithmic probability of [u_j,u_(j+1)] converges to its integral against du/(u log(2)). Translate f(u)/(u log(2)) to [0,1] and apply the continuous left Riemann sum theorem. On each cell, the difference between its rectangular density weight and its exact mass is at most 1/(n^2 log(2)). A compact bound for f makes the total difference tend to zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.fixed_block_moments_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBlockTransfer.logarithmic_block_riemann`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentTransferDefs](FourthMomentTransferDefs.md)
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling](../../../Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.md)
