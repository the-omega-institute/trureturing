# Equal-cell limits determine the moving-length constant

## Abstract

Equal-cell limits determine the moving-length constant.

**Theorem 1.1 (The fixed-length normalization ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.fixed_normalizer_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.fixed_normalizer_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>0 and any real theta, the ratio of (X/(c*X^theta))*log(X/(c*X^theta)) to X^(1-theta)*log(X) tends to (1-theta)/c as X tends to infinity.

**Theorem 1.2 (Cell endpoints lie in the dyadic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive and j between zero and n, the point 1+j/n lies in [1,2].

**Theorem 1.3 (Equal cell widths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two consecutive endpoints 1+j/n and 1+(j+1)/n differ by 1/n.

**Theorem 1.4 (Ordered cell endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n each endpoint is strictly smaller than the next.

**Theorem 1.5 (The frozen-cell mean square).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a Borel real function bounded on compact intervals, assume 0<alpha<theta<beta<1 and the uniform cumulative variance band asymptotic, and let g be integrable on [0,1]. For fixed positive n, sum the profile square integrals on [a_j X,a_(j+1) X] with length frozen at (a_j X)^theta, where a_j=1+j/n. Dividing by X^(1-theta) log X gives the limit ((1-theta)Q(g)/n) times the sum of a_j^(-theta). The fixed-length normalizer divided by this scale tends to (1-theta)/c.

**Theorem 1.6 (The limiting rectangle constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<theta<1 and any real profile g, the constants ((1-theta)Q(g)/n) times the sum of (1+j/n)^(-theta) for 0<=j<n tend to Q(g)*(2^(1-theta)-1). Since v^(-theta) decreases on [1,2], its left and right rectangle sums bound its integral and differ by (1-2^(-theta))/n. Multiplying the resulting rectangle-sum limit by (1-theta)Q(g) proves the conclusion without a sign assumption on Q(g).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.fixed_normalizer_ratio`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare](TriangularMeanSquare.md)
