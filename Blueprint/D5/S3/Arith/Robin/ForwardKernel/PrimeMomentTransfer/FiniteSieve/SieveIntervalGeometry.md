# Integer interval geometry for finite sieve sums.

## Abstract

Integer interval geometry for finite sieve sums.

**Theorem 1.1 (Cardinality with endpoint error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H>0 and 0<=a<=b, the number of selected integer points is at most H(b-a)+1. The difference of the two floors gives the count, with an endpoint error bounded by one.

**Theorem 1.2 (Reduction to the prefix of the same cardinality).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_moment_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_moment_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real scale and endpoints, every natural moment of the interval sieve sum equals the corresponding moment for the prefix whose length is the number of selected integer points. Reversed floor endpoints select the empty interval; otherwise translation gives the prefix law.

**Definition 1.3 (sieve endpoint grid).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveEndpointGrid`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveEndpointGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real window M and mesh delta, the finite endpoint grid consists of delta times the natural numbers from zero through the natural floor of M/delta.

**Definition 1.4 (sieve round down).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveRoundDown`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveRoundDown` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An endpoint x rounded down to mesh delta is delta times the natural floor of x/delta.

**Theorem 1.5 (A finite mesh for ordered endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_grid_rounding`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_grid_rounding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M>=0, delta>0 and 0<=a<=b<=M, round each endpoint x down to delta*floor(x/delta). Both rounded endpoints belong to the finite grid delta*n for 0<=n<=floor(M/delta), remain ordered in [0,M], and differ from the original endpoints by at most delta.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveEndpointGrid`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieveRoundDown`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_grid_rounding`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_card_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.sieve_interval_moment_prefix`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs](FiniteSieveDefs.md)
