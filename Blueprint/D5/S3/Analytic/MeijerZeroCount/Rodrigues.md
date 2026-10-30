# The compactly supported polynomial family

## Abstract

Rodrigues kernels with exact interior zero counts.

**Definition 1.1 (The polynomial primitive).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.W`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Rodrigues.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and N, W is X to the power n times (1-X) to the power N, as a real polynomial.

**Definition 1.2 (The coefficients).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.coeffA`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Rodrigues.coeffA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at k is (-1) to the power n+k times (n+k) factorial divided by k factorial squared and by (n+d-1-k) factorial. The coefficient sum runs from zero through N=n+d-1.

**Definition 1.3 (The Rodrigues polynomial).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.rodriguesPoly`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Rodrigues.rodriguesPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the nth polynomial derivative of W with N=n+d-1, then multiply by (-1) to the power n divided by N factorial.

**Definition 1.4 (The Mellin kernel).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inside the unit interval with endpoints excluded, f is x to the real power n+c times the Rodrigues polynomial evaluated at x, viewed as a complex number. The function is zero elsewhere.

**Theorem 1.5 (The finite power expansion).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n and d, real c, and zero less than x less than one, f(x) is the sum over k from zero through n+d-1 of the coefficient at k times x to the real power n+c+k. Expand the primitive by the binomial theorem, apply the polynomial derivative term by term, and simplify the factorial coefficients.

**Theorem 1.6 (Exactly n interior zeros).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.zeros_f`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MeijerZeroCount/Rodrigues.zeros_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, every natural d at least one, and every real c, the zero set of f in the unit interval with endpoints excluded has extended cardinality n. The real power factor and the scalar normalization do not vanish there. Before the nth derivative, both endpoints remain roots. Rolle's theorem supplies an additional distinct interior root at every derivative step. The surviving factor (1-X) to the power N-n divides the nth derivative; after its removal the remaining polynomial has degree at most n. The polynomial degree bound gives the matching upper bound.

## References

- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.W`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.coeffA`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.f_eq_sum`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.rodriguesPoly`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Rodrigues.zeros_f`
- Dependency: [D5/S3/Analytic/MeijerZeroCount/Defs](Defs.md)
