# The coefficient nonnegativity assertion

## Abstract

Gamma product ratios and shifted Turanian coefficients.

**Definition 1.1 (Gamma product ratios).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For vectors a of length p and b of length q, c(t) is the product of Gamma(a(i)+t) divided by the product of Gamma(b(j)+t). Empty products equal one, so a numerator vector of length zero is allowed.

**Definition 1.2 (The Cauchy coefficient).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.turanCoeff`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/Defs.turanCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For natural m, delta(m) is the sum over k from zero through m of [c(mu+alpha+k)c(mu+beta+m-k)-c(mu+k)c(mu+alpha+beta+m-k)] divided by k! times (m-k)!. Subtraction in the index m-k is natural subtraction; throughout this sum k is at most m. This is the coefficient in f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x), where f(mu;x) has coefficient c(mu+n)/n! at degree n.

**Definition 1.3 (Elementary symmetric functions).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

The degree k elementary symmetric function is the sum of the products over all k-element selections of parameter positions. Repeated parameter values retain their multiplicities, and the degree zero value is one.

**Theorem 1.4 (Elementary symmetric functions of a constant vector).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall x \in \mathbb{R},\; \operatorname{esymm}\left((fun (i: \operatorname{Fin}\left(n\right)) \mapsto x), k\right) = (\operatorname{Nat.choose}\left(n, k\right): \mathbb{R}) \cdot x^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For all natural n and k and every real x, the degree k elementary symmetric function of n copies of x is the real cast of n choose k times x to the power k. Every k-element subset contributes x to the power k, and there are n choose k such subsets. The identity includes k greater than n, when both sides vanish, and k zero, when both sides equal one. It supplies condition (13) for the repeated half parameters in both the coefficient and function counterexamples.

**Definition 1.5 (The ratio chain).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.cond13`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/Defs.cond13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural j less than p, require e(q-j,b)/e(p-j,a) to be at most e(q-j-1,b)/e(p-j-1,a). With p at most q these are exactly the consecutive inequalities in the descending symmetric ratio chain. If p is zero there are no inequalities.

**Definition 1.6 (Universal coefficient nonnegativity).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim`

*Formalization.* `D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For all p at most q and all positive parameter vectors satisfying the ratio chain, require delta(m) to be nonnegative for every natural m whenever mu is at least one, alpha and beta are nonnegative, and alpha is at most beta+1. This is the coefficient conclusion of the conjecture in the branch p at most q. Refuting this conclusion refutes the conjecture; no assertion about the value of the Turanian for nonnegative x is needed.

**Theorem 1.7 (Gamma at three halves).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_halves`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_halves` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Real.Gamma at 3/2 equals Real.sqrt Real.pi divided by 2. This is the natural-plus-half formula at one.

**Theorem 1.8 (Gamma at five halves).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Real.Gamma at 5/2 equals 3 times Real.sqrt Real.pi divided by 4. This is the natural-plus-half formula at two.

**Theorem 1.9 (Gamma at seven halves).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_seven_halves`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_seven_halves` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Real.Gamma at 7/2 equals 15 times Real.sqrt Real.pi divided by 8. This is the natural-plus-half formula at three.

**Theorem 1.10 (The balanced reciprocal power product).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves_inv_pow_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves_inv_pow_mul` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural q, the product of two copies of the qth power of the reciprocal of Real.Gamma at 5/2 is (16/(9 pi))^q. Apply the Gamma value and the identity Real.sqrt Real.pi times itself equals Real.pi.

**Theorem 1.11 (The outer reciprocal power product).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_seven_halves_inv_pow_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_seven_halves_inv_pow_mul` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural q, the product of the qth powers of the reciprocals of Real.Gamma at 3/2 and 7/2 is (16/(15 pi))^q. Apply the two Gamma values and the square-root identity.

**Theorem 1.12 (Gamma at three).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

Real.Gamma at 3 equals 2, the factorial formula at two.

**Theorem 1.13 (The integer reciprocal power product).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_two_three_inv_pow_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_two_three_inv_pow_mul` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural q, the product of the qth powers of the reciprocals of Real.Gamma at 2 and at 3 is (1/2)^q, since Real.Gamma at 2 is 1 and Real.Gamma at 3 is 2.

**Theorem 1.14 (The base times one half).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.base_pow_mul_half_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.base_pow_mul_half_pow` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

For every natural q, (32/(9 pi))^q times (1/2)^q equals (16/(9 pi))^q.

**Theorem 1.15 (A rational lower bound for the base).**

Lean statement: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.pi_base_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HypergeometricShiftTuran/Defs.pi_base_bound` (`✓ std3`). ∎

*Citation.* S. I. Kalmykov and D. B. Karp (2017). *Log-concavity and Turán-type inequalities for the generalized hypergeometric function*. DOI: [10.1007/s10476-017-0503-z](https://doi.org/10.1007/s10476-017-0503-z). URL: <https://arxiv.org/abs/1611.06724>.

*Commentary.*

The inequality 640/567 < 32/(9 pi) follows from pi < 3.15 and positivity of pi. It supplies the common base estimate for the two negative coefficient families.

## References

- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.base_pow_mul_half_pow`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.claim`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.cond13`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm_const`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_five_halves_inv_pow_mul`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_seven_halves`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_halves`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three_seven_halves_inv_pow_mul`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_two_three_inv_pow_mul`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.pi_base_bound`
- Truth anchor: `D5/S3/Analytic/HypergeometricShiftTuran/Defs.turanCoeff`
