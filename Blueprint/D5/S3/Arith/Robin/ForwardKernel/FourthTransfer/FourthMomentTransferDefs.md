# Fourth-moment transfer definitions

## Abstract

Local fourth energy and interval-weighted fixed-scale mixed moments

**Definition 1.1 (Local fourth energy on a window).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.localFourthEnergyWindow`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.localFourthEnergyWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every X/2<=A<=B<=4X and (4X)^alpha<=v<=(X/2)^beta, the integral of |E(y+v)-E(y)|^4 over [A,B] is at most C*v^2*log(X)^2*(B-A+epsilon*X).

**Definition 1.2 (The local fourth-energy hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.LocalFourthEnergyFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.LocalFourthEnergyFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant C is nonnegative. There is a nonnegative function epsilon(X) tending to zero such that, for all sufficiently large X, the local fourth-energy window bound holds simultaneously for every admissible A, B, and v.

**Definition 1.3 (A fixed-scale normalized increment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedScaleB`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedScaleB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At position x, divide E(x+c*X^theta)-E(x) by sqrt(X^theta*log(X)). The length coefficient c is fixed independently of x.

**Definition 1.4 (A mixed moment on a macroscopic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedBlockMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedBlockMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate the product of k fixed-scale normalized increments against dyadic logarithmic probability at scale X, multiplied by the indicator that U_X=x/X lies in the closed interval [u,v].

**Definition 1.5 (Interval-weighted fixed-scale convergence).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.FixedScaleMixedMoments`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.FixedScaleMixedMoments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every M>0, every k-tuple c with each coefficient in [0,M], and every 1<=u<v<=2, the fixed block moment tends as X tends to infinity to W(c) times the logarithmic probability of [u,v] at scale one. The interval indicator remains part of the moment being tested.

**Definition 1.6 (A moving normalized increment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.movingB`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.movingB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the fixed-scale normalization with the length coefficient a(U_X), where U_X=x/X. The increment length is X^theta*a(x/X).

**Definition 1.7 (A normalized increment frozen on cells).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.frozenB`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.frozenB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Partition (1,2] into the n disjoint cells (1+j/n,1+(j+1)/n]. On each cell evaluate the fixed-scale normalized increment with coefficient a(1+j/n). The sum is zero outside these cells; for n=0 it is the empty sum.

**Definition 1.8 (The uniform fourth-moment constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fourthK`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fourthK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For energy constant C and length bound M, define K_M=1312*C*M^2/log(2).

**Definition 1.9 (The fourth-order freezing constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.freezeCoefficient`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.freezeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For energy constant C, derivative bound L, and cell count n, define 1312*C*(1+L)^2/(3*n^2*log(2)). Its use in freezing estimates assumes n>0.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.FixedScaleMixedMoments`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.LocalFourthEnergyFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedBlockMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fixedScaleB`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.fourthK`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.freezeCoefficient`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.frozenB`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.localFourthEnergyWindow`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.movingB`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs](../MomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells](../MovingLengthCells.md)
