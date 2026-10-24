# Coefficient calculus

## Abstract

Scores and curvature of reciprocal Pochhammer coefficients.

**Definition 1.1 (Reciprocal coefficients).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.c`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Coeff.c` (`✓ std3`).

*Citation.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, c(n,t) is the evaluation of ascPochhammer at 2t divided by the product of its evaluation at t and n factorial. For t positive this is the coefficient (2t)n/((t)n n!) in the reciprocal series of Conjecture 5.2, page 12.

**Definition 1.2 (Adjacent degree ratio).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.lambda`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Coeff.lambda` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural j and real t, lambda(j,t) equals (2t+j)/(t+j).

**Definition 1.3 (Score increment).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.eta`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Coeff.eta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural j and real t, eta(j,t) equals j/((2t+j)(t+j)). In particular the increment at j=0 is zero.

**Definition 1.4 (Finite score sum).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.psi`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Coeff.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, psi(n,t) is the sum of eta(j,t) over 0 <= j < n. The zero index contributes zero, so this equals the sum over 1 <= j < n.

**Definition 1.5 (Finite curvature sum).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.chi`

*Formalization.* `D5/S3/Analytic/KarpZhangReciprocal/Coeff.chi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and real t, chi(n,t) is the sum over 0 <= j < n of j(4t+3j)/((2t+j)^2(t+j)^2).

**Theorem 1.6 (Uniform score and curvature estimates).**

Lean statement: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.coefficient_calculus`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangReciprocal/Coeff.coefficient_calculus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii Karp and Yi Zhang (2023). *Log-concavity and log-convexity of series containing multiple Pochhammer symbols*. DOI: [10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0). URL: <https://arxiv.org/abs/2305.09029>.

*Commentary.*

For every natural n and positive real t, c(n,t) and lambda(n,t) are positive; c(n+1,t)/c(n,t) equals lambda(n,t)/(n+1); the derivative of c(n,t) is c(n,t)psi(n,t), the derivative of log(c(n,t)) is psi(n,t), and the derivative of psi(n,t) is -chi(n,t). Curvature is nonnegative and at least n times eta(n-1,t) squared. The function j -> lambda(j,t) is antitone. Natural subtraction makes the n=0 curvature estimate meaningful, with both sides zero.

At each j <= N, compare the positive denominator (2t+j)^2(t+j)^2 with the terminal denominator (2t+N)^2(t+N)^2. Retaining 3j squared from the numerator and summing gives chi(N+1,t) at least (N+1)N squared divided by the terminal denominator. This is the estimate controlling adjacent score differences in the convolution Hessian.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.c`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.chi`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.coefficient_calculus`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.eta`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.lambda`
- Truth anchor: `D5/S3/Analytic/KarpZhangReciprocal/Coeff.psi`
