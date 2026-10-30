# Intrinsic Positive Trace on Real Hilbert Spaces

## Abstract

The positive trace is an extended nonnegative quantity defined from the operator by all finite orthonormal test families. The definition chooses no basis or scalar spectrum and permits an infinite value.

**Definition 1.1 (Positive Trace).**

Lean statement: `D5/S3/HilbertOperators/RealPositiveTrace.positiveTrace`

*Formalization.* `D5/S3/HilbertOperators/RealPositiveTrace.positiveTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a bounded real linear operator A, positiveTrace(A) is the supremum, over every natural n and every orthonormal family v indexed by Fin n, of the sum of ofReal(inner(v(j),A(v(j)))). Its intended use is for positive operators. Neither compactness nor summability is required to define this extended value.

**Theorem 1.2 (Complete Positive Diagonal).**

Lean statement: `D5/S3/HilbertOperators/RealPositiveTrace.positive_trace_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/RealPositiveTrace.positive_trace_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be a complete real Hilbert basis of E and let A be a continuous real linear operator on that same carrier. Suppose d(i) is nonnegative and, for every vector x and every index i, the i-th coefficient of A(x) is d(i) times the i-th coefficient of x. Then A is positive and its intrinsic positive trace is the extended sum of ofReal(d(i)). The index type can be empty, finite or infinite, and the trace can be infinite.

Parseval gives the convergent quadratic-form series for each test vector. Interchanging nonnegative extended sums and applying finite-family Bessel bounds each finite orthonormal trace sum by the diagonal sum. Conversely, every finite selection of the supplied eigenvectors is an admissible test family. Taking the supremum of those finite selections gives the reverse inequality. Thus two complete positive diagonal presentations yield the same value because each equals the same operator-defined supremum.

This is the standard finite-family construction of positive trace. It supplies the original real boundary heat with an intrinsic operator trace without a complexification, a finite-dimensional algebraic trace, or a scalar sequence used as the definition of trace. The separate identification with singular-value trace class is an additional mathematical statement.

## References

- Truth anchor: `D5/S3/HilbertOperators/RealPositiveTrace.positiveTrace`
- Truth anchor: `D5/S3/HilbertOperators/RealPositiveTrace.positive_trace_diagonal`
