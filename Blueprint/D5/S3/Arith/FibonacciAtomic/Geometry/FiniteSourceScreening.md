# Finite Source Screening

## Abstract

The finite counting resolvent bridge is specified on the actual all-occurrence source.

**Definition 1.1 (unitInverse).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complete real inner-product space, unitInverse attaches the inverse continuous linear map to an explicit IsUnit proof.

**Definition 1.2 (ActualBridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.ActualBridge`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.ActualBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each source index n, ActualBridge records the actual closed counting Laplacian on the all-occurrence node space, its normalized root source and root evaluation, the supported path decomposition, the counting energy identity, symmetry and positivity, the root and source pairings, full-H screening invertibility, node resolvent invertibility, and the centered Gram covariance identity.

**Definition 1.3 (root_response).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ActualBridge and positive screening parameter, root_response evaluates the actual root source response using the inverse of its counting Laplacian plus lambda.

**Definition 1.4 (screened_inverse).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ActualBridge and positive screening parameter, screened_inverse is the inverse on the full common edge Hilbert space of I plus N(n) times lambda times the centered finite covariance.

The structure keeps the source node spaces dependent on n and keeps the common edge space fixed. Its fields state the supported-edge reconstruction, the unit-conductance counting energy, the uniform-to-counting N(n) factor, and the full-H inverse conditions. The final scalar identity is intentionally left at the source bridge until those fields are constructed from the actual address edges.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.ActualBridge`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.root_response`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.screened_inverse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.unitInverse`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance](FiniteSourceCovariance.md)
