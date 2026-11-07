# Variance transfer definitions

## Abstract

Increments, triangular averages, and the uniform short-interval variance hypotheses.

**Definition 1.1 (Increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increment D_h(x) is E(x+h)-E(x), for a real error function E and real h and x.

**Definition 1.2 (Cumulative variance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(Y,h) is the oriented integral of D_h(x)^2 from 1 to Y.

**Definition 1.3 (Triangular primitives).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularPrimitive`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularPrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B_h(x) is the oriented integral of D_u(x) with respect to u from 0 to h.

**Definition 1.4 (Triangular averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P_h(x) is B_h(x)/h^2.

**Definition 1.5 (The fixed comparison length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison length is c*X^(4/5).

**Definition 1.6 (The length logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length logarithm is log(X/(c*X^(4/5))).

**Definition 1.7 (The dyadic scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalization of the moving-length mean square is X^(1/5)*log(X).

**Definition 1.8 (Regularity of an error function).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An error function is measurable and, on each closed finite real interval, its absolute value has a finite nonnegative upper bound.

**Definition 1.9 (The uniform variance hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each positive epsilon and all sufficiently large Y, uniformly for Y^(3/4)<=h<=Y^(7/8), the absolute difference between V(Y,h)/(Y*h*log(Y/h)) and 1 is at most epsilon. The threshold for Y precedes the choice of h.

**Definition 1.10 (The short-interval mean-square hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are C>0 and X0>=2 such that, for X>=X0 and 0<theta<=1, the integral over [X,2X] of (E((1+theta)*x)-E(x))^2 is at most C*theta*X^2*log(2/theta)^2.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularAverage`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.triangularPrimitive`
