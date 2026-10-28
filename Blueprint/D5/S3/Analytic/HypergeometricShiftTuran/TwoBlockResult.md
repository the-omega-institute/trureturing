# A counterexample family for Conjecture 2

## Abstract

Negative first Turanian coefficients with a nonempty shifted numerator.

**Definition 1.1 (The unshifted parameter block).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.pochRatio`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.pochRatio` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For parameter vectors a1 and b1 and natural n, pochRatio is the product of (ascPochhammer R n).eval a1(i) divided by the corresponding product for b1. These are the rising factorials in the unshifted block of equation (3). Empty products equal one.

**Definition 1.2 (The Taylor coefficient in equation (3)).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.seriesCoeff`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.seriesCoeff` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Equation (3) on page 2 defines f(mu;x)=Gamma(a2+mu)/Gamma(b2+mu) times pFq(a1,a2+mu;b1,b2+mu;x). Its degree n Taylor coefficient is pochRatio(a1,b1,n) times Defs.coeff(a2,b2,mu+n), divided by n!. Thus the shifted Gamma product includes the numerator block a2, while the rising factorial ratio contains only the unshifted block.

**Definition 1.3 (The Cauchy coefficient).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.twoBlockTuranCoeff`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.twoBlockTuranCoeff` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For natural m, sum F(k,mu+alpha)F(m-k,mu+beta)-F(k,mu)F(m-k,mu+alpha+beta) over k from zero through m, where F(n,t) is seriesCoeff at t and n. The factorials are already included in F. This is the coefficient of x to the power m in equation (2), the generalized Turanian of equation (3). The subtraction m-k is natural subtraction, and k is at most m in this sum.

**Definition 1.4 (Universal coefficient nonnegativity).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim` (`✓ std3`).

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Conjecture 2 on page 6 states: ‘Conjecture 2. Suppose p1 ≤ q1 , p2 ≤ q2 and conditions (13) hold for a1 , b1 and a2 , b2 . Then the function µ → f (µ; x) defined in (3) is log-concave on [1, ∞) and the corresponding generalized Turánian ∆f (α, β; x) has nonnegative coefficients at all powers of x.’ The standing assumption on page 2 is: ‘We will always assume that a2 is not empty (i.e. p2 ≥ 1), while all other subvectors are allowed to be empty.’ The definition encodes the coefficient clause: p1 is at most q1, p2 is at least one and at most q2, all four parameter vectors are positive, and Defs.cond13 holds separately for both blocks. For every mu at least one, every nonnegative alpha and beta, and every natural m, require twoBlockTuranCoeff to be nonnegative. There is no additional relation between alpha and beta. Refuting this clause requires no assertion about log-concavity of the function for a fixed x.

**Theorem 1.5 (The first coefficient in closed form).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.first_coefficient_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.first_coefficient_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural q, take empty unshifted blocks, shifted numerator (1), q shifted denominator entries equal to one half, mu=1, and alpha=beta=1/2. The first coefficient equals (45 pi/16)(1/2)^q-4(16/(9 pi))^q-6(16/(15 pi))^q. The identity follows by expanding the two degree-one Cauchy summands and applying the shared Gamma special values and reciprocal power products.

**Theorem 1.6 (Every multiplicity at least seven).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.half_parameter_family_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.half_parameter_family_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Take empty unshifted blocks a1 and b1, the shifted numerator a2=(1), and q shifted denominator entries all equal to one half. At mu=1 and alpha=beta=1/2, the coefficient of x is strictly negative for every natural q at least seven.

Empty rising factorial products are one, so this Cauchy sum equals Defs.turanCoeff for the shifted blocks. With c(t)=Gamma(1+t)/Gamma(1/2+t)^q, its first coefficient is 2c(3/2)c(5/2)-c(2)^2-c(1)c(3). The integer and half-integer Gamma formulas give delta(1)=(45 pi/16)(1/2)^q-4(16/(9 pi))^q-6(16/(15 pi))^q.

The bound pi<3.15 gives 32/(9 pi)>640/567>1. Exact rational arithmetic gives (640/567)^7>45 times 3.15 divided by 64. Monotonicity in the exponent therefore yields (32/(9 pi))^q>45 pi/64 for every q at least seven. Multiplication by 4(1/2)^q makes the middle term exceed the positive leading term, and the final term is strictly positive before subtraction.

**Theorem 1.7 (Refutation of the coefficient clause).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result` (`✓ std3`). ∎

*Resolves.* `Problems/kalmykov-karp-pfq-conjecture-two-coefficients` (refuted) by `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kalmykov-karp-pfq-conjecture-two-coefficients","declaration_gid":"D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Set q=7 in the negative coefficient family. Both unshifted blocks are empty, so their positivity requirements and condition (13) are vacuous. The shifted numerator contains the positive entry one, and the shifted denominator contains seven positive halves. The finite elementary symmetric sum for n repeated entries x in degree k is choose(n,k) times x to the power k. Hence the shifted ratio chain is (1/2)^7 at most 7(1/2)^6, with numerator symmetric values e1=1 and e0=1. All dimension, positivity and shift requirements hold.

Universal coefficient nonnegativity would make the negative coefficient of x nonnegative. Thus the coefficient clause of Conjecture 2 is false. The shifted numerator is nonempty as required in equation (3); this differs from a counterexample with an empty shifted numerator. The result makes no assertion about the sign of the full Turanian or log-concavity at a fixed nonnegative x.

## References

- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.claim`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.first_coefficient_eq`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.half_parameter_family_neg`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.pochRatio`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.seriesCoeff`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.twoBlockTuranCoeff`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/Defs](Defs.md)
