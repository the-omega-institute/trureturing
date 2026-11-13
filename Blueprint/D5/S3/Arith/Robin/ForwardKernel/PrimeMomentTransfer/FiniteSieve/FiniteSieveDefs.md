# Finite sieve variables and interval moments

## Abstract

Finite sieve variables and interval moments

**Definition 1.1 (sieve density).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveDensity`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive integer modulus Q, the sieve density ratio is Q divided by its Euler totient.

**Definition 1.2 (sieve variable).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveVariable`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveVariable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus Q and a natural shift d, the centered sieve variable is Q/phi(Q) times the indicator that the representative of x+d in ZMod Q is coprime to Q, minus one.

**Definition 1.3 (sieve expectation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveExpectation`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveExpectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus Q, the expectation of a real function on ZMod Q is the sum over all residue classes divided by Q.

**Definition 1.4 (sieve functional).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveFunctional`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus Q, normalized summation over ZMod Q defines a real linear functional.

**Definition 1.5 (sieve interval sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus Q, the interval sieve sum is the sum of the centered coprimality variables over the natural shifts in (aH,bH].

**Definition 1.6 (sieve interval moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite number of intervals, the sieve interval moment is the expectation of the product of their centered sieve sums over the positive integer shifts in (a_i H,b_i H].

**Definition 1.7 (sieve interval pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalPairing`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four intervals, the sieve interval pairing is the sum of the three products of second moments corresponding to the three pair partitions.

**Definition 1.8 (sieve interval wick defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalWickDefect`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalWickDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four intervals, the sieve interval Wick defect is the fourth joint moment minus the sum of the three products of second moments.

**Definition 1.9 (sieve cutoff).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveCutoff`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a window size M and a real scale H, the sieve cutoff is the natural floor of ((M+5)H) to the tenth power.

**Definition 1.10 (primorial sieve modulus).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.primorialSieveModulus`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.primorialSieveModulus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a window size M and real scale H, the positive sieve modulus is the primorial at the sieve cutoff.

**Definition 1.11 (finite singular series).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteSingularSeries`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteSingularSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural cutoff y and a finite set of natural offsets, the finite singular series is the product over primes at most y of (1 minus the fraction of occupied residue classes) divided by (1 minus the reciprocal prime) to the number of offsets.

**Definition 1.12 (centered pair kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.centeredPairKernel`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.centeredPairKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered pair kernel is zero on the diagonal and otherwise is the centered full singular series of the two offsets.

**Definition 1.13 (mssecond).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.MSSecond`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.MSSecond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Montgomery–Soundararajan square-sum hypothesis asserts that the sum of the centered pair kernel over 1 <= d,e <= m differs from minus m log m by at most C m, for one nonnegative C and every natural m at least one. This is a consequence of their Theorem 2 and equation (16).

**Definition 1.14 (moment scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.momentScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.momentScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural order k and real H, the moment scale is (H log H) raised to the real exponent k/2.

**Definition 1.15 (finite sieve intervals).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.FiniteSieveIntervals`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.FiniteSieveIntervals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite-sieve interval hypothesis is the conclusion of Lemma 498.3(c): the third interval moment is uniformly negligible relative to (H log H)^(3/2), and the fourth interval Wick defect is uniformly negligible relative to (H log H)^2. For every M at least one and every positive epsilon, these estimates hold for all sufficiently large real H and all ordered interval endpoints in [0,M], for the primorial moduli Q = primorial(floor(((M+5)H)^10)). This conclusion is assumed here; its derivation from Montgomery–Soundararajan Theorem 1 and Kuperberg Theorem 1.3 is not proved here.

**Definition 1.16 (finite distinct correlation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteDistinctCorrelation`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteDistinctCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite number of intervals, the finite distinct correlation is the distinct centered correlation formed with the finite singular series at the sieve cutoff.

**Definition 1.17 (finite pair correlation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finitePairCorrelation`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finitePairCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four intervals, the finite pair correlation is the sum of the three products of second distinct correlations for the finite singular series at the sieve cutoff.

**Definition 1.18 (uniform interval small).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.UniformIntervalSmall`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.UniformIntervalSmall` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed order and window size M, uniform interval smallness means that for every positive epsilon and all sufficiently large real scales H, the absolute error is at most epsilon times (H log H)^(k/2), simultaneously for all ordered endpoints in [0,M].

**Definition 1.19 (locally bounded interval error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.LocallyBoundedIntervalError`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.LocallyBoundedIntervalError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed order and window size M, local boundedness means that for every T at least two a nonnegative constant bounds the absolute error by that constant times (H log H)^(k/2), for every H in [2,T] and all ordered endpoints in [0,M].

**Theorem 1.20 (sieve quadratic).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each centered coprimality indicator satisfies Y squared = (P-2)Y+(P-1), where P is Q divided by its totient.

**Theorem 1.21 (sieve mean zero).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_mean_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_mean_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural translate of the centered coprimality indicator has expectation zero under the uniform average modulo a positive integer.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.FiniteSieveIntervals`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.LocallyBoundedIntervalError`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.MSSecond`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.UniformIntervalSmall`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.centeredPairKernel`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteDistinctCorrelation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finitePairCorrelation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.finiteSingularSeries`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.momentScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.primorialSieveModulus`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveCutoff`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveDensity`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveExpectation`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveFunctional`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalPairing`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveIntervalWickDefect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieveVariable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_mean_zero`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs.sieve_quadratic`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance](../IntervalCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel](../SignedCubeMomentModel.md)
