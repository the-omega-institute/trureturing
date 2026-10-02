# Represented Spanning Polynomial Root Concavity

## Abstract

Every positive-degree represented spanning polynomial has a concave degree-th real root on the entire nonnegative orthant, including all zero-polynomial regimes.

**Theorem 1.1 (Actual Analytic Line Derivative).**

Lean statement: `D5/S3/Resource/SimplexCoverageRoot.evaluateAt_line_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoverageRoot.evaluateAt_line_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any rational multivariate polynomial on a finite index set, evaluating at x+t y has derivative equal to the finite sum of y_i times the evaluated formal partial derivative. Structural polynomial induction uses the constant, sum and product-with-one-variable cases. No nonempty-index or positivity assumption is needed.

**Theorem 1.2 (Root Concavity on the Closed Nonnegative Orthant).**

Lean statement: `D5/S3/Resource/SimplexCoverageRoot.spanningPolynomial_root_concaveOn`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoverageRoot.spanningPolynomial_root_concaveOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The field and ambient vector space are arbitrary, the quotient by U is finite-dimensional, the finite physical index set is unchanged, and the natural degree is at least one. The degree-th real root of the actual reciprocal-factorial spanning polynomial is ConcaveOn the whole nonnegative orthant. No spanning, nonempty-index, analytic derivative, Hessian or induction premise is imposed.

The quotient map preserves the spanning condition of each represented support, so the exact coefficient formula identifies the original polynomial with its quotient representation over the same variables. All physical indices are retained; no finite-dimensional ambient restriction is used.

The exact line derivative applied to each partial derivative identifies the second line derivative with the evaluated formal-Hessian quadratic form. Finite sums are interchanged without assuming mixed-partial commutation. At positive line points the actual all-degree reverse-Hessian induction makes the explicit second root derivative nonpositive. Continuous endpoints assemble concavity on the closed unit interval.

Zero polynomials give the constant branch. Positive degree and an empty index set force every coefficient to vanish. Rank obstruction and unspanned families use the existing exact zero-polynomial theorem. The nonzero branch is positive on the positive orthant. Jensen inequalities for positively translated endpoints pass to all boundary coordinates by global polynomial and real-root continuity. Degree one is included, and a fractional root is never differentiated at zero.

This is an analytic dependency, not a settlement of the named simplex optimizer. Actual all-horizon iid physical sampling probabilities and expected-time comparisons remain separate obligations.

## References

- Truth anchor: `D5/S3/Resource/SimplexCoverageRoot.evaluateAt_line_hasDerivAt`
- Truth anchor: `D5/S3/Resource/SimplexCoverageRoot.spanningPolynomial_root_concaveOn`
- Dependency: [D5/S3/Resource/SimplexCoverageInduction](SimplexCoverageInduction.md)
