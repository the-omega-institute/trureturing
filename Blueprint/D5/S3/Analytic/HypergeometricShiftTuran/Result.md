# Half shifts with repeated denominator parameters

## Abstract

A family of negative first Turanian coefficients.

**Theorem 1.1 (Every multiplicity at least six).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Result.half_parameter_family_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Result.half_parameter_family_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Take no numerator parameters, q denominator parameters all equal to one half, base parameter mu=1, and shifts alpha=beta=1/2. For every natural q at least six, the coefficient of x in the shifted Turanian is strictly negative.

Here c(t)=Gamma(t+1/2) raised to the power -q. The two terms in the first Cauchy coefficient give delta(1)=2(1/2)^q-(16/(9 pi))^q-(16/(15 pi))^q. The half-integer Gamma formula gives Gamma(3/2)Gamma(7/2)=15 pi/16 and Gamma(5/2) squared equal to 9 pi/16; Gamma(2)=1 and Gamma(3)=2.

The bound pi<3.15 implies 32/(9 pi)>640/567>1. The sixth power of 640/567 is greater than two. Monotonicity in the exponent therefore gives (32/(9 pi))^q>2 for q at least six. Multiplication by (1/2)^q makes the middle term larger than the positive leading term, and the final term is strictly positive before subtraction.

**Theorem 1.2 (Refutation of the coefficient assertion).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-pfq-conjecture-one-coefficients` (refuted) by `D5/S3/Analytic/HypergeometricShiftTuran/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-pfq-conjecture-one-coefficients","declaration_gid":"D5/S3/Analytic/HypergeometricShiftTuran/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Set q=6 in the negative coefficient family. The empty numerator vector has positive entries vacuously, every denominator entry is positive, and p=0 makes the symmetric ratio chain vacuous. The parameters mu=1 and alpha=beta=1/2 satisfy all shift restrictions, including alpha at most beta+1. Universal coefficient nonnegativity would require this strictly negative first coefficient to be nonnegative.

The coefficient conclusion in the p at most q branch is therefore false, and so is the conjecture asserting all conclusions in this parameter range. The argument concerns a power-series coefficient and makes no claim about the sign of the Turanian as a function on the nonnegative real axis.

## References

- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Result.half_parameter_family_neg`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Result.result`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/Defs](Defs.md)
