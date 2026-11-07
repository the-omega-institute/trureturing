# Variance transfer definitions

## Abstract

Increments, profile averages, and parameterized short-interval variance hypotheses.

**Definition 1.1 (Unit interval measure).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.unitMeasure`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.unitMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lebesgue measure restricted to the interval (0,1].

**Definition 1.2 (Integrable profiles).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ProfileIntegrable`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ProfileIntegrable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A profile is a measurable real function whose absolute value is integrable for unit interval measure. Choose a global Borel representative; its values outside [0,1] do not affect the conclusions.

**Definition 1.3 (Admissible exponents).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ValidBand`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ValidBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponents satisfy 0<alpha<theta<beta<1.

**Definition 1.4 (Profile primitives).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profilePrimitive`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profilePrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primitive at length h and center x is the oriented integral from 0 to h of g(u/h)*D_u(x).

**Definition 1.5 (Profile averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile average is the profile primitive divided by h^2.

**Definition 1.6 (Moving profile averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.movingAverage`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.movingAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The moving average uses length x^theta in the profile average.

**Definition 1.7 (Profile absolute integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileL1`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileL1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile L1 size is the integral of abs(g) for unit interval measure.

**Definition 1.8 (Tail profiles).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.tailProfile`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.tailProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail profile at r is the oriented integral of g from r to 1.

**Definition 1.9 (Profile quadratic energy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.Q`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q(g) is the iterated integral on the unit square of g(s)*g(t)*min(s,t).

**Definition 1.10 (Increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increment D_h(x) is E(x+h)-E(x), for a real error function E and real h and x.

**Definition 1.11 (Cumulative variance).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(Y,h) is the oriented integral of D_h(x)^2 from 1 to Y.

**Definition 1.12 (The fixed comparison length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison length is c*X^theta.

**Definition 1.13 (The length logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length logarithm is log(X/(c*X^theta)).

**Definition 1.14 (The dyadic scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalization of the moving-length mean square is X^(1-theta)*log(X).

**Definition 1.15 (Regularity of an error function).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An error function is measurable and, on each closed finite real interval, its absolute value has a finite nonnegative upper bound.

**Definition 1.16 (The uniform variance hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each positive epsilon and all sufficiently large Y, uniformly for Y^alpha<=h<=Y^beta, the absolute difference between V(Y,h)/(Y*h*log(Y/h)) and 1 is at most epsilon. The threshold for Y precedes the choice of h.

**Definition 1.17 (The short-interval mean-square hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are C>0 and X0>=2 such that, for X>=X0 and 0<theta<=1, the integral over [X,2X] of (E((1+theta)*x)-E(x))^2 is at most C*theta*X^2*log(2/theta)^2.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.CumulativeVarianceBandAsymptoticFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.LocallyBoundedMeasurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ProfileIntegrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.Q`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ShortIntervalMeanSquareBoundFor`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.ValidBand`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.cumulativeVariance`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.fixedLength`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.increment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.lengthLog`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.meanSquareScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.movingAverage`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileAverage`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profileL1`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.profilePrimitive`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.tailProfile`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.unitMeasure`
