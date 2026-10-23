# The exact bound for every truncation

## Abstract

The supremum of the elliptic remainder exponent

**Theorem 1.1 (Positive remainder denominator).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Result.denominator_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Result.denominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Q. Bao, M.-K. Wang and S.-L. Qiu (2022). *Monotonicity properties of the generalized elliptic integrals with respect to the parameter*. DOI: [10.7153/mia-2022-25-64](https://doi.org/10.7153/mia-2022-25-64). URL: <https://arxiv.org/abs/2112.13993>.

*Commentary.*

For every natural n and 0<a<=1/2, sin(pi a)-pi(1-a)S(n,a) is strictly positive. The coefficient-tail identity factors the remainder as a^2 U(n,a), whose factors are positive.

**Theorem 1.2 (Logarithmic derivative identity).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Q. Bao, M.-K. Wang and S.-L. Qiu (2022). *Monotonicity properties of the generalized elliptic integrals with respect to the parameter*. DOI: [10.7153/mia-2022-25-64](https://doi.org/10.7153/mia-2022-25-64). URL: <https://arxiv.org/abs/2112.13993>.

*Commentary.*

For every natural n and 0<a<=1/2, the parameter exponent equals 2+a U'(n,a)/U(n,a). The finite Euler product identifies each summand as a^2 b(k,a). The sine remainder is therefore a^2 U(n,a). Both functions are differentiable near each positive parameter. Equality of their derivatives within (0,1/2] includes the endpoint a=1/2, and the quotient rule gives the stated exponent.

**Theorem 1.3 (Strict upper bound).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_lt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_lt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Q. Bao, M.-K. Wang and S.-L. Qiu (2022). *Monotonicity properties of the generalized elliptic integrals with respect to the parameter*. DOI: [10.7153/mia-2022-25-64](https://doi.org/10.7153/mia-2022-25-64). URL: <https://arxiv.org/abs/2112.13993>.

*Commentary.*

For every natural n and 0<a<=1/2, the parameter exponent is strictly below two. The correction a U'(n,a)/U(n,a) is strictly negative because U is positive and its derivative is negative.

**Theorem 1.4 (The limiting exponent at zero).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Result.tendsto_lambda10`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Result.tendsto_lambda10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Q. Bao, M.-K. Wang and S.-L. Qiu (2022). *Monotonicity properties of the generalized elliptic integrals with respect to the parameter*. DOI: [10.7153/mia-2022-25-64](https://doi.org/10.7153/mia-2022-25-64). URL: <https://arxiv.org/abs/2112.13993>.

*Commentary.*

For every natural n, the parameter exponent tends to two as a decreases to zero through positive values. The uniform derivative bound gives a U'(n,a) tending to zero, while continuity and U(n,0)=1/(n+1) give a positive denominator limit.

**Theorem 1.5 (The exact supremum).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/bao-wang-qiu-2022-elliptic-tail-exponent` (proved) by `D5/S3/Analytic/EllipticTailExponent/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bao-wang-qiu-2022-elliptic-tail-exponent","declaration_gid":"D5/S3/Analytic/EllipticTailExponent/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Q. Bao, M.-K. Wang and S.-L. Qiu (2022). *Monotonicity properties of the generalized elliptic integrals with respect to the parameter*. DOI: [10.7153/mia-2022-25-64](https://doi.org/10.7153/mia-2022-25-64). URL: <https://arxiv.org/abs/2112.13993>.

*Commentary.*

For every natural n, two is the least upper bound of the values of the parameter exponent on (0,1/2]. Each value is strictly smaller than two, and the right-hand limit at zero places two in the closure of this set of values.

## References

- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Result.denominator_pos`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_eq`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Result.lambda10_lt_two`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Result.result`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Result.tendsto_lambda10`
- Dependency: [D5/S3/Analytic/EllipticTailExponent/Bounds](Bounds.md)
- Dependency: [D5/S3/Analytic/EllipticTailExponent/Tail](Tail.md)
