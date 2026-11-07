# Equal-cell limits determine the moving-length constant

## Abstract

Equal-cell limits determine the moving-length constant.

**Theorem 1.1 (Cell endpoints lie in the dyadic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n positive and j between zero and n, the point 1+j/n lies in [1,2].

**Theorem 1.2 (Equal cell widths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two consecutive endpoints 1+j/n and 1+(j+1)/n differ by 1/n.

**Theorem 1.3 (Ordered cell endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n each endpoint is strictly smaller than the next.

**Theorem 1.4 (The frozen-cell mean square).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be measurable and bounded on compact intervals, with the short-interval mean-square bound and uniform cumulative variance band asymptotic. These imply the fixed-length triangular mean-square limit on every interval [aX,bX] with 1<=a<b<=2 and every positive length factor c. For fixed positive n, summing the square integrals with length frozen at (a_j X)^(4/5) and dividing by X^(1/5) log X tends to the sum of a_j^(-4/5)/(15n), where a_j=1+j/n. The fixed-length normalizer divided by X^(1/5) log X tends to 1/(5c).

**Theorem 1.5 (The limiting rectangle constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constants (15n)^(-1) times the sum of (1+j/n)^(-4/5) for 0<=j<n tend to (2^(1/5)-1)/3. Since v^(-4/5) decreases on [1,2], its left and right rectangle sums bound its integral. Their difference is (1-2^(-4/5))/n, so the normalized upper sum differs from the limiting constant by at most 1/(15n).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_lt`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_mem`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cellPoint_step`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_constant_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells.cell_mean_square_tendsto`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare](TriangularMeanSquare.md)
