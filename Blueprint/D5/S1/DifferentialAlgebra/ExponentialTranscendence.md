# Polynomial Independence of the Formal Exponential

## Abstract

The formal variable and its exponential satisfy no nonzero rational polynomial relation.

Generality I: these statements concern the fixed exponential in Q[[X]]. Exponential transcendence is classical and is also the one-pair case of Ax's theorem.

Work in the ring Q[[X]] of formal power series. Write E=sum over n>=0 of X^n/n!. The expression p(X,E) is defined for every bivariate polynomial p with rational coefficients; no analytic convergence or substitution of an infinite series with nonzero constant coefficient is required.

**Definition 1.1 (Bivariate evaluation).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval`

*Formalization.* `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval` (`✓ std3`).

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

View Q[t,u] as polynomials in u with coefficients in Q[t]. The homomorphism exponentialEval first includes each coefficient polynomial in Q[[X]] by t=X, then evaluates u at E.

**Theorem 1.2 (Injectivity of exponential evaluation).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval_injective`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval_injective` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

The homomorphism p(t,u) -> p(X,E) is injective. Equivalently, if sum_j p_j(X)E^j=0 for finitely many rational polynomials p_j, then every p_j is zero. Let D be formal differentiation, considered as a rational linear operator. The identity (D-j)(p_j(X)E^j)=p_j'(X)E^j shows that p_j(X)E^j belongs to the generalized eigenspace of D for eigenvalue j: the power (D-j)^(degree(p_j)+1) annihilates it. Generalized eigenspaces for distinct eigenvalues form an independent family. Thus each summand of a zero sum vanishes. The series E is a unit, so each p_j(X) vanishes, and injectivity of the polynomial inclusion gives p_j=0. The proof uses Mathlib's general independence theorem for generalized eigenspaces and its differentiation and unit identities for the formal exponential.

**Theorem 1.3 (Transcendence over the polynomial coefficient ring).**

Lean statement: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exp_transcendental`

*Proof.* Machine-checked in Lean as `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exp_transcendental` (`✓ std3`). ∎

*Citation.* James Ax (1971). *On Schanuel's conjectures*. DOI: [10.2307/1970774](https://doi.org/10.2307/1970774). URL: <https://annals.math.princeton.edu/1971/93-2/p03>.

*Commentary.*

With the canonical inclusion Q[t] -> Q[[X]], t=X, the series E is transcendental over Q[t]. This is the same injectivity statement expressed through the algebra evaluation homomorphism Q[t][u] -> Q[[X]].

## References

- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exp_transcendental`
- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval`
- Truth anchor: `D5/S1/DifferentialAlgebra/ExponentialTranscendence.exponentialEval_injective`
