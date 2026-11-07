# Cross-exponent averages and variance scales

## Abstract

Square norms, moving increments, and forward averages for comparisons between power scales.

**Definition 1.1 (Interval square norm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.intervalL2`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.intervalL2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interval square norm of u on [A,B] is the square root of the oriented integral of u(x)^2. Its norm interpretation is used when A is at most B.

**Definition 1.2 (Moving increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingIncrement`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moving increment at x is E(x+s*x^theta)-E(x), using the shared increment function.

**Definition 1.3 (Moving endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingShift`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moving endpoint is x+s*x^theta.

**Definition 1.4 (Forward window averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.windowAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.windowAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward window average of u at x is the integral of u(x+r) for r from zero to R, divided by R.

**Definition 1.5 (Double forward averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.doubleAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.doubleAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The double average at scale R applies the forward window average of length R twice.

**Definition 1.6 (Dyadic smoothing blocks).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.smoothingBlock`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.smoothingBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The smoothing block at scale R is the double average at scale R minus the double average at scale 2R.

**Definition 1.7 (Comparable-length variance bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.ComparableLengthVarianceUpperFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.ComparableLengthVarianceUpperFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale R(X) is eventually positive. For each fixed 0<A<=B and d>0, a positive constant bounds V(d*X,u) by C*X*R(X)*log(X), eventually uniformly for A*R(X)<=u<=B*R(X). The threshold precedes the choice of u.

The quantifier covers every spatial factor d>0; for C>=1 this is the form supplied by (491.1), since cumulative variance is monotone in its first argument.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.ComparableLengthVarianceUpperFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.doubleAverage`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.intervalL2`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingIncrement`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.movingShift`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.smoothingBlock`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.windowAverage`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
