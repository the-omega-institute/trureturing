# Golden Trace Logarithm

## Abstract

The actual golden adjacency trace series converges absolutely on its open disk and gives a justified principal logarithm.

The source is Part1739 of OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY. The positive exponential of the infinite trace series is a reciprocal determinant, also commonly called a dynamical zeta. The logarithm identity for a two-by-two matrix uses two spectral values satisfying its trace and determinant equations.

**Definition 1.1 (Actual adjacency).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.adjacency`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency is the entrywise complex image of the real Fibonacci substitution matrix. Both off-diagonal entries and the first diagonal entry are one; the second diagonal entry is zero. False and true letters correspond to the first and second states.

**Definition 1.2 (Positive-index trace term).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceTerm`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural index is shifted by one, so the defining series has exactly the positive indices. The trace belongs to the actual matrix power, and the denominator and power of the complex variable have the same positive index.

**Definition 1.3 (Local convergence domain).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.localDomain`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.localDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The open complex disk has radius the reciprocal of the positive golden ratio. Neither boundary point nor exterior point belongs to the domain of this series-defined function.

**Definition 1.4 (Infinite trace sum).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceSum`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is defined on the subtype of the local disk. The trace series is absolutely summable and has the sum given by the local logarithm identity at every input. A totalized sum at a point of divergence does not define this analytic function.

**Definition 1.5 (Positive exponential).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.dynamicalZeta`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.dynamicalZeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function is the exponential of the infinite trace sum with a positive sign in the exponent. Its domain is the local disk.

**Definition 1.6 (Separate rational continuation).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.continuation`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This rational expression agrees with the local exponential on the disk. Totalized complex division assigns finite values at denominator zeros, but the pole statements concern punctured meromorphic germs. They do not concern an exponential evaluated at a divergent series.

**Definition 1.7 (Local analytic contract).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.localContract`

*Formalization.* `D5/S3/Analytic/Characterizations/GoldenTraceLog.localContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The determinant and golden factorization hold for every complex variable, and the trace formula holds at every natural power. On the local disk, the determinant has positive real part and is nonzero; the trace series is absolutely summable and has sum equal to the negative principal logarithm of the determinant, and the positive exponential equals the rational continuation. The logarithm representative is analytic and normalized at zero.

**Lemma 1.8 (Absolute logarithm summability).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.summable_norm_log_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenTraceLog.summable_norm_log_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex input of norm less than one, the positive-index logarithm terms are absolutely summable by geometric domination. The same bound controls the correction at the golden convergence boundary.

**Theorem 1.9 (Two-root logarithm identity).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.matrix_trace_log`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenTraceLog.matrix_trace_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex two-by-two matrix with the supplied Vieta trace and determinant, both scaled roots must have norm less than one. Scalar logarithm series then give the actual infinite HasSum. The two factors have positive real parts, so their principal arguments have sum strictly between minus pi and pi. This discharges the product-log branch before exponentiation.

**Theorem 1.10 (Golden local identity).**

Lean statement: `D5/S3/Analytic/Characterizations/GoldenTraceLog.golden_local`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenTraceLog.golden_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace and determinant of the golden adjacency satisfy the two-root hypotheses. A norm estimate keeps the determinant in the open right half-plane throughout the entire stated disk. Thus the principal logarithm identity holds on this local branch. Nonvanishing alone does not imply a global unwrapped logarithm identity.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.adjacency`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.continuation`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.dynamicalZeta`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.golden_local`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.localContract`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.localDomain`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.matrix_trace_log`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.summable_norm_log_terms`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceSum`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTraceLog.traceTerm`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S1/Eigenstructure/FibonacciMatrixDiscriminant](../../../S1/Eigenstructure/FibonacciMatrixDiscriminant.md)
