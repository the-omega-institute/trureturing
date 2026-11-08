# Macroscopic increments and weighted moments

## Abstract

Macroscopic increments and weighted moments

**Definition 1.1 (Variance error on a comparable window).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.VarianceWindowBound`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.VarianceWindowBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every Y in [X/2,4X] and Y^alpha<=v<=Y^beta, the relative error of V(Y,v) from Y*v*log(Y/v) is at most epsilon.

**Definition 1.2 (The macroscopic variance scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.varianceScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.varianceScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale is X*X^theta*log(X).

**Definition 1.3 (A macroscopic variable length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.macroIncrement`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.macroIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At x the increment is E(x+X^theta*a(x/X))-E(x).

**Definition 1.4 (The normalized square integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.normalizedSquare`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.normalizedSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate f(x)^2 over [X,2X] and divide by X*X^theta*log(X).

**Definition 1.5 (Bounded differentiable lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.MacroscopicLengthBounds`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.MacroscopicLengthBounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On [1,2], the length function a is continuously differentiable, takes values in [0,M], and its derivative within the interval has absolute value at most L.

**Definition 1.6 (The error from freezing lengths on blocks).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.freezingError`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.freezingError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Partition [X,2X] into n equal blocks with endpoints X*(1+j/n). Sum the integrals of the squared difference between the variable increment and the increment with length frozen at the left endpoint, and divide by X*X^theta*log(X).

**Definition 1.7 (Weighted covariance of macroscopic increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedMacroCovariance`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedMacroCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate w(x/X) times the two increments with lengths X^theta*a(x/X) and X^theta*b(x/X) over [X,2X], and divide by X*X^theta*log(X).

**Definition 1.8 (Weighted dyadic covariance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicCovariance`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under logarithmic dyadic probability, integrate phi(U_X) times the two normalized increments B_X(s) and B_X(t), allowing separate exponents for the two increments.

**Definition 1.9 (Weighted dyadic first moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicFirstMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicFirstMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under logarithmic dyadic probability, integrate phi(U_X)*B_X(s).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.MacroscopicLengthBounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.VarianceWindowBound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.freezingError`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.macroIncrement`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.normalizedSquare`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.varianceScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicCovariance`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedDyadicFirstMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.weightedMacroCovariance`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs](MomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthCells](MovingLengthCells.md)
