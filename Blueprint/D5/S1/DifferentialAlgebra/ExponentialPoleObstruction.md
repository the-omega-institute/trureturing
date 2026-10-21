# A Simple Pole Obstructs a Rational Primitive

## Abstract

The rational function u/(2-u) has no primitive when the derivative of u is u.

Generality G: the coefficient field is arbitrary of characteristic zero, and its derivation may be nonzero. This is the classical local pole obstruction to rational integration.

Let K be a field of characteristic zero and let d be an integer-linear derivation of K[u] satisfying d(u)=u. The restriction of d to K may be nonzero. The conclusions therefore apply to the differential field K=Q(t), with d(t)=1, as well as to constant coefficient fields.

**Theorem 1.1 (The Cleared Polynomial Identity Is Impossible).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.polynomial_obstruction`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.polynomial_obstruction` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

For coprime polynomials p,q with q nonzero, the identity (2-u)(d(p)q-pd(q))=u q² is impossible. Evaluating at u=2 first shows q(2)=0. Coprimality gives p(2) nonzero. Write q=(u-2)^(n+1)s with s(2) nonzero. Since d(u-2)=u, cancelling (u-2)^(n+1) in the proposed identity and evaluating again gives 2(n+1)p(2)s(2)=0. Every factor is nonzero. The factorization uses polynomial root multiplicity; no analytic convergence or complex residues are required.

**Theorem 1.2 (Injective Differential Evaluation).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.rational_expression_obstruction`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.rational_expression_obstruction` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

Let j inject K[u] into a field L with derivation D, and suppose D(j(p))=j(d(p)) for every polynomial p. For every reduced fraction p/q, its image j(p)/j(q) cannot have derivative j(u)/(2-j(u)). The quotient rule and clearing the two nonzero denominators would give the impossible polynomial identity above; injectivity of j returns that identity from L to K[u].

**Theorem 1.3 (No Primitive in K(u)).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.no_rational_primitive`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.no_rational_primitive` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

If D is a derivation on K(u) that agrees with d on K[u], then D(h) differs from u/(2-u) for every rational function h. The reduced numerator and denominator of h supply coprime polynomials, so the differential evaluation obstruction applies to the standard embedding K[u] into K(u).

## References

- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.no_rational_primitive`
- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.polynomial_obstruction`
- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialPoleObstruction.rational_expression_obstruction`
