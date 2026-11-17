# Dyadic smoothing decomposition

## Abstract

A common variance band controls every scale in a dyadic smoothing decomposition.

Let E be locally bounded and Borel measurable, and suppose its cumulative variance has uniform asymptotics on an exponent band containing a<b. Write h=X^a, k=X^b, Z_R for the double forward average of E, and B_R=Z_R-Z_(2R). The estimates below use [X/2,4X] as the working interval and [X/4,8X] for the increment estimates, leaving room for all forward translations.

**Theorem 1.1 (Choice of terminal scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.exists_dyadic_terminal_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.exists_dyadic_terminal_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>=1 and a<b there is a natural number N with k<=2^N*h<2*k and N<=1+(b-a)*log(X)/log(2). The Archimedean power comparison supplies N, with exact powers treated at their own index so that the upper endpoint remains strict.

**Theorem 1.2 (Telescoping double averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.doubleAverage_dyadic_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.doubleAverage_dyadic_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every function E, real h and x, and natural number N, Z_h(x)=Z_(2^N*h)(x)+sum_(j<N) B_(2^j*h)(x). This is the finite telescoping identity for consecutive scales.

**Theorem 1.3 (Uniform bounds for every dyadic block).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.common_band_dyadic_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.common_band_dyadic_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are C>0 and an index function N(X) such that one eventual threshold gives the terminal-scale inequalities, the pointwise telescoping decomposition, and the following estimates simultaneously. Set A=sqrt(X*log(X)). The residual E-Z_h has L2 norm at most C*A*sqrt(h). For every j<=N(X), put R=2^j*h. The L2 norms of B_R, B_R', and Z_R' are at most C*A*sqrt(R), C*A/sqrt(R), and C*A/sqrt(R), respectively. On the working interval, |B_R|<=C*A and |Z_R'|<=C*A/R.

The increment-square bound is applied at X/2 and 2X with exponents strictly inside the common band. Their intervals cover the outer interval and give a single bound proportional to X*max(u,h)*log(X) for every 0<=u<=8*k. Taking square roots supplies the hypotheses of the smoothing and residual estimates. All scales and all spatial points are quantified after the common threshold.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.common_band_dyadic_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.doubleAverage_dyadic_decomposition`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition.exists_dyadic_terminal_scale`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds](DyadicSmoothingBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance](MovingLengthVariance.md)
