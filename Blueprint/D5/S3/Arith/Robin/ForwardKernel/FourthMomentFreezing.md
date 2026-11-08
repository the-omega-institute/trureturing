# Fourth-order macroscopic freezing

## Abstract

Local fourth energy controls normalized moving and frozen increments.

**Theorem 1.1 (Comparison with a fixed length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.macro_fourth_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.macro_fourth_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded continuously differentiable macroscopic length, compare the moving increment with a fixed increment on any subinterval of [X,2X]. If their endpoint gap is at most R and the endpoint scale is admissible, the fourth energy is bounded by (1312/3)C R squared log(X) squared times the image interval length plus the local error. The common endpoint geometry supplies derivatives at least one half and the common image interval.

**Theorem 1.2 (Finite fourth-order freezing estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive equal cells and R=(1+L)X to the theta divided by n, the fourth moment of the normalized moving-minus-frozen increment is at most 1312 C (1+L) squared divided by (3 n squared log 2), multiplied by 1+n M X to the theta divided by X+n epsilon. Frozen functions use disjoint left-open right-closed cells. The local comparison keeps the cell length, so summing produces decay of order n to the minus two.

**Theorem 1.3 (Uniform moving fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.moving_fourth_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.moving_fourth_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under local fourth energy, for every M at least one and nonnegative derivative bound L, all sufficiently large X satisfy the same fourth-moment bound 1312 C M squared divided by log 2 for every admissible length function. The threshold precedes the function quantifier. Taking endpoint radius M X to the theta also covers lengths arbitrarily close to zero.

**Theorem 1.4 (Uniform frozen fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.frozen_fourth_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.frozen_fourth_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed positive number of cells, all sufficiently large X give fourth moment at most 1312 C M squared divided by log 2 for every frozen admissible length. On each cell the common endpoint estimate uses radius M X to the theta, and the summed finite bound contains 1+n M X to the theta divided by X+n epsilon. Both error terms eventually lie below one. This controls the whole frozen function for use in Holder estimates.

**Theorem 1.5 (Uniform eventual fourth-order freezing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive tolerance and fixed positive cell count, there is a common eventual threshold for all admissible length functions. Beyond it, the fourth moment of the normalized freezing error is at most 1312 C (1+L) squared divided by (3 n squared log 2) plus the tolerance. The proof uses the explicit finite bound and the vanishing relative endpoint scale and local energy error; it includes the case C equals zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_eventually`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.freezing_fourth_finite`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.frozen_fourth_uniform`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.macro_fourth_comparison`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentFreezing.moving_fourth_uniform`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthMomentEndpoint](FourthMomentEndpoint.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicFreezing](MacroscopicFreezing.md)
