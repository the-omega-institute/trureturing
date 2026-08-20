# Axis Trace Definitions

## Abstract

The partial sum ranges over words of bounded depth; the weight is the exponential.

The clause introduces two objects: the axis weight at a depth, read as an exponential at the two Galois embeddings, and the axis partial sum, the total weight of the legal words whose digit depth is at most that depth.

The implementation sums over an initial segment of the naturals rather than over a set described by depth. Those are the same family only because depth at most K is exactly membership below the next Fibonacci number. That equivalence is the third conjunct here: without it the bound in the definition would be an unexplained constant, and a reader could not check the implementation against the source line.

**Theorem 1.1 (The two objects and the depth bridge).**

$$\operatorname{t}\left(K\right) = \operatorname{exp}\left(y \cdot \mathit{psi}^{K + 1} - x \cdot \mathit{phi}^{K + 1}\right) \land \left(\operatorname{W}\left(K\right) = \operatorname{sum}\left(\operatorname{range}\left(\operatorname{fib}\left(K + 1\right)\right), \operatorname{wordWeight}\left(n\right)\right) \land \left(\operatorname{greatestFib}\left(n\right) \le K \Leftrightarrow n < \operatorname{fib}\left(K + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisTraceDefinitions.axis_trace_definitions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two conjuncts hold by definition and pin it: changing the exponent or the summation bound makes the module fail to build. The third is a proved equivalence rather than a restatement, and it is what makes the summation bound mean bounded depth.

## References

- Truth anchor: `D5/S3/Axis/AxisTraceDefinitions.axis_trace_definitions`
