# Newton--Hankel Real-Root Criterion

## Abstract

Negative real roots of a positive-coefficient polynomial are equivalent to positivity of its Newton--Hankel matrix.

**Theorem 1.1 (Negative roots are equivalent to Newton--Hankel positivity).**

$$\forall d, P, lambda,\\(\operatorname{PositiveCoefficientsOfDegree}\left(P, d\right) \land \operatorname{EnumeratesReversedRoots}\left(P, lambda\right) \land \operatorname{ConjugationStable}\left(lambda\right)) \Rightarrow\\\operatorname{HasOnlyNegativeRealRoots}\left(P\right) \iff \operatorname{PosSemidef}\left(G_{d}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/NewtonHankelRealRootCriterion.negative_real_roots_iff_newtonHankel_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a real polynomial of degree d whose coefficients from degree zero through d are strictly positive. Let lambda enumerate with multiplicity the nonzero roots of q(x)=x^d P(-1/x), and assume its finite support is closed under complex conjugation. Then every root of P is a negative real number if and only if the normalized Newton--Hankel matrix G_d built from the lambda power sums is positive semidefinite.

The forward direction expands every quadratic form as the normalized sum of squares at real roots. For the reverse direction, a nonreal root and its conjugate are assigned interpolation values i and -i, with zero at every other distinct root. Lagrange interpolation descends to real coefficients and makes the quadratic form strictly negative. Positive coefficients then exclude nonpositive real roots of q, and the reversed-root correspondence gives the negative roots of P.

This declaration carries only properties one and two of the source theorem. It does not assert a positive-definite determinant realization or a nonnegative-weight Fibonacci-chain realization.

## References

- Truth anchor: `D5/S3/Constants/NewtonHankelRealRootCriterion.negative_real_roots_iff_newtonHankel_posSemidef`
