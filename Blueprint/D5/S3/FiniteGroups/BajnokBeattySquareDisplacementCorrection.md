# All-q square-displacement correction coefficient

## Abstract

For every natural q at least three, the square-displacement Perron coefficient has a positive slope factor, a strictly negative threshold correction, and an exact cubic cancellation.

Let Q be q as a real number, nu=q^2, beta be the existing d-bonacci Perron root at order nu, and sigma=log(beta). Define c=(Q^2-1)/(4Q), alpha=c/sigma, g=exp(sigma)-Q^2 exp(-Q^2 sigma), C=2(Q^2+1)/(3(Q^2-1)^2), H=C sigma^3 (exp(sigma)-Q^4 exp(-Q^2 sigma)), and define d=((Q^2+1)sigma/(6Q(Q^2-1)))*(((Q^4+1)beta-2Q^4)/((Q^2+1)beta-2Q^2)) and b=d-1/(2Q).

**Theorem 1.1 (The all-q coefficient signs and cancellation).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection.square_displacement_correction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection.square_displacement_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural q with q >= 3, 0 < g, 0 < d, d < 5 log(2)/(24Q), -1/(2Q) < b, and b < 0. The exact identity is g*(sigma*d/alpha)=H.

The positivity mechanism is finite and quantitative. The existing order-nine logarithm bound and strict monotonicity of the Perron family give 2/3 < sigma < log(2). A degree-four finite exponential sum gives exp(2nu/3) > (10/9)nu^2 for every real cast of a natural nu >= 9. Combining this with exp(-nu sigma)=2-beta proves nu^2 exp(-nu sigma) < 9/10 < beta, hence beta-Q^4 exp(-Q^2 sigma)>0. The numerator is smaller than the denominator by the positive term (Q^4-Q^2)exp(-Q^2 sigma), so the ratio defining d lies strictly between zero and one.

The bound on d uses (Q^2+1)/(Q^2-1) <= 5/4 for Q >= 3 and sigma < log(2). The cancellation is algebraic: the Perron reciprocal identity rewrites the numerator and denominator as beta-Q^4 exp(-Q^2 sigma) and beta-Q^2 exp(-Q^2 sigma), while alpha=(Q^2-1)/(4Q sigma) supplies the remaining factor C sigma^3.

The finite centered binomial motivation belongs only to this explanation. Existing sum_linear and sum_cubic declarations provide the exact first and third moments for offsets p, qp, and q^2p. With n=p(2qt-1), the rational coordinate v=t-1/(2q)+1/(2qp) gives s=c*p/v; the coefficient predicts alpha*p+1/(2q)+b/p. This source makes no claim about a full lattice quotient classification, a general-q count-error envelope, real-variable binomial counts, rounding, an infinite counterexample family, or literature novelty.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCorrection.square_displacement_correction`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../../S0/Tower/DBonacci/PerronRoot.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot](BajnokBeattyOddWrapGaussianRoot.md)
