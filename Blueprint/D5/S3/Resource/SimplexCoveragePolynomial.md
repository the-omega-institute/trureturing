# Represented Spanning Polynomial Dependencies

## Abstract

Actual reciprocal-factorial represented spanning polynomials have exact contractions, a degree-two reverse bound, positive-evaluation support and zero obstructions.

Variables are indexed by physical columns over an arbitrary field. Zero, repeated and scalar-parallel columns remain separate indices. Coefficients lie in Q and evaluation lies in R; no characteristic-zero assumption on the column field is made.

**Definition 1.1 (Represented support span).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.representedSpan`

*Formalization.* `D5/S3/Resource/SimplexCoveragePolynomial.representedSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjoin to U the span of columns whose natural exponent is positive.

**Definition 1.2 (Actual reciprocal-factorial polynomial).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial`

*Formalization.* `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the monomials of total degree m whose represented support spans the ambient space together with U, weighting each by the product of reciprocal coordinate factorials. The finite exponent encoding retains all physical indices.

**Definition 1.3 (Real evaluation).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.evaluateAt`

*Formalization.* `D5/S3/Resource/SimplexCoveragePolynomial.evaluateAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the rational polynomial at the represented real coordinate vector.

**Definition 1.4 (Actual algebraic Hessian).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian`

*Formalization.* `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the two polynomial partial derivatives, not a separate support-indicator matrix.

**Theorem 1.5 (Exact represented coefficients).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every natural exponent vector the coefficient is the reciprocal-factorial weight exactly when its total equals the degree and its represented support spans with U; otherwise the coefficient is zero. No finite-dimensional or nonempty assumption is needed.

**Theorem 1.6 (Exact one-column contraction).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_pderiv`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_pderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation at physical index i lowers successor degree by one and replaces U by U plus the span of that column. Loops, repeats and scalar-parallel columns are included.

**Theorem 1.7 (Degree-two quotient-rank classification).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_degree_two_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_degree_two_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite-dimensional ambient space and arbitrary evaluation point, quotient rank zero gives entries one; rank one excludes precisely loop-loop pairs; rank two joins nonloops with distinct one-column extension subspaces; larger rank gives zero. Empty indices and unspanned represented families are allowed.

**Theorem 1.8 (Division-free degree-two reverse inequality).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_degree_two_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_degree_two_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension, for nonnegative x and unrestricted real y, the actual polynomial F, Hessian H and evaluated polynomial gradient g satisfy 2 F(x) y^T H y <= (g^T y)^2. The zero-evaluation boundary and empty index set are included. Finite-fiber grouping is a proof identity, not column deduplication or sampling renormalization.

**Theorem 1.9 (Positive evaluation and quotient rank).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_positive_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_positive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty physical indices, finite-dimensional ambient space, strictly positive x and U plus the full represented column span equal to the ambient space, F(x) is nonnegative and strictly positive exactly when quotient rank is at most the degree. Nonemptiness is needed for padding when U is already the whole space.

**Theorem 1.10 (Actual derivative-positive support connectivity).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_active_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_active_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same nonempty, finite-dimensional, positive-evaluation and full-spanning conditions, at degree m+2 define active indices by the strictly positive evaluated actual polynomial derivative. Every nonempty proper cut on this subtype has a positive Hessian crossing. Empty and singleton active sets satisfy the cut condition vacuously; this does not supply nonemptiness for the matrix normalization theorem.

**Theorem 1.11 (Exact zero-polynomial obstructions).**

Lean statement: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_eq_zero_of_rank_or_span`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_eq_zero_of_rank_or_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension the polynomial vanishes identically if its degree is less than quotient rank or U plus the entire represented column span is not the whole space. No nonempty, full-spanning or evaluation-point assumption is imposed.

These are reusable dependencies of the source-faithful development for Bertuzzo–Ravagnani–Yaakobi, arXiv:2603.06489v1, Conjecture 3.2, preregistered in #11799. No higher-degree reverse inequality, analytic derivative bridge, root concavity, projective averaging, physical iid probability normalization, zero-column coupling or actual expected-time optimizer is claimed. The full conjecture remains OPEN.

## References

- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.evaluateAt`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.representedSpan`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_active_connected`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningHessian_degree_two_classification`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_coeff`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_degree_two_reverse`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_eq_zero_of_rank_or_span`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_pderiv`
- Truth anchor: `D5/S3/Resource/SimplexCoveragePolynomial.spanningPolynomial_positive_iff`
- Dependency: [D5/S3/Resource/SimplexCoverageHessian](SimplexCoverageHessian.md)
