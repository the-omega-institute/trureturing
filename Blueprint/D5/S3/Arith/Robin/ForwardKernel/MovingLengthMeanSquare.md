# Equal-cell freezing gives the moving-length triangular mean square

## Abstract

Equal-cell freezing gives the moving-length triangular mean square.

**Theorem 1.1 (Moving-length mean square from fixed-length limits).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare.moving_length_mean_square_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare.moving_length_mean_square_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be measurable and bounded on compact intervals. Assume the short-interval mean-square bound and uniform cumulative variance band asymptotic. They give the fixed-length triangular mean-square limit with value (b-a)/3 for every 1<=a<b<=2 and c>0. Then the square integral of P_(x^(4/5))(x) over [X,2X], divided by X^(1/5) log X, tends to (2^(1/5)-1)/3. Freeze the length at each left endpoint of n equal cells. Write Q_n(X)=cellMeanSquare E n X, the sum over the n cells of the integrals of the square of the triangular average at the frozen cell length. The total square error is at most 18 Q_n(X)/n^2 + 64 X^(1/5) log X/n, with constants independent of n. The interval L squared reverse triangle inequality and Young’s inequality compare the two square integrals. First choose n so that both the rectangle constant and the normalized error are small, then choose X for this fixed n. The short-interval upper bound controls the small lengths in the fixed-length limit, and the variance band controls the strip estimate with one logarithm.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare.moving_length_mean_square_tendsto`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells](MovingLengthCells.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity](MovingLengthRegularity.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance](MovingLengthVariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
