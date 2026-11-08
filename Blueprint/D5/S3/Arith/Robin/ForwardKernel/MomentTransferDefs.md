# Moment transfer definitions

## Abstract

Normalized moving increments, mixed moments, and the fourth Brownian moment kernel.

**Definition 1.1 (Unit cube measure).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.cubeMeasure`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.cubeMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure on real tuples indexed by Fin k is the product of k copies of Lebesgue measure restricted to (0,1].

**Definition 1.2 (Complementary exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.kappa`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real length exponent theta, kappa(theta)=1-theta.

**Definition 1.3 (Response scale exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicR`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The macroscopic scale exponent r is kappa(theta)/2.

**Definition 1.4 (Macroscopic position).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicU`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scaled position U_X(x) is x/X; for X>0 and x in [X,2X], it belongs to [1,2].

**Definition 1.5 (Normalized moving increment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized increment B(s,x) is (E(x+s*x^theta)-E(x))/sqrt(x^theta*log(x)). It depends on s and x, with no separate dyadic endpoint parameter.

**Definition 1.6 (Normalized profile response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicZ`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized response Z_X(x) is the price-weighted moving profile response divided by sqrt(X^(1-theta)*log(X)).

**Definition 1.7 (Weighted mixed moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMixedMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMixedMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple s of length k, the mixed moment is the integral of U_X(x)^(k*r) times the product of B(s_i,x), against the dyadic logarithmic measure.

**Definition 1.8 (Moment transfer interface).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.MomentInterface`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.MomentInterface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is a nonnegative constant C such that, for all sufficiently large X and every s in [0,1], the integral of abs(B(s,x))^k is at most C. The specified limit function M is measurable, and each weighted mixed moment at a tuple in the unit cube converges to M at that tuple as X tends to infinity.

**Definition 1.9 (Fourth Brownian kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.brownianW4`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.brownianW4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four real coordinates, W4 is min(s0,s1)*min(s2,s3) + min(s0,s2)*min(s1,s3) + min(s0,s3)*min(s1,s2), the three covariance pairings for the fourth Brownian moment on nonnegative times.

**Definition 1.10 (Fourth dyadic moment constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMomentConstant`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMomentConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fourth-order macroscopic constant c4(theta) is (2^(2*kappa(theta))-1)/(2*kappa(theta)*log(2)). For nonzero kappa this is the integral of u^(2*kappa) against du/(u*log(2)) on [1,2].

**Theorem 1.11 (Joint measurability of normalized increments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a locally bounded measurable error function E and any real exponent theta, the map (s,x) to B(s,x) is Borel measurable. Joint measurability of the moving increment and measurability of real powers, logarithm, square root, and division give the result on the whole real plane.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.MomentInterface`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.brownianW4`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.cubeMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicB_measurable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMixedMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicMomentConstant`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicR`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicU`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.dyadicZ`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs.kappa`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicProbability](DyadicProbability.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightRemoval](WeightRemoval.md)
