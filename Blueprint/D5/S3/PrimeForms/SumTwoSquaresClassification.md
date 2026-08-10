# Classification of Sums of Two Squares

## Abstract

A natural number is a sum of two squares exactly when every prime congruent to three modulo four occurs to an even exponent in its factorization.

**Theorem 1.1 (A natural number is a sum of two squares exactly when its prime factors congruent to three modulo four carry even exponents).**

$$(\exists a,b\in\mathbb{N},\ n=a^2+b^2)\quad\Leftrightarrow\quad \forall q\ \text{prime},\ q\equiv 3\ (\operatorname{mod}\ 4) \Rightarrow 2\ \mid\ v_q(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/SumTwoSquaresClassification.eq_sq_add_sq_iff_even_factorization` (`✓ std3`). ∎

*Citation.* Emil Grosswald (1985). *Representations of Integers as Sums of Squares*. DOI: [10.1007/978-1-4613-8566-0](https://doi.org/10.1007/978-1-4613-8566-0).

*Commentary.*

A natural number n is a sum of two natural squares if and only if every prime q congruent to three modulo four occurs to an even exponent in the factorization of n. The formal statement quantifies over all primes rather than only the prime factors of n: primes not dividing n, and every prime when n is zero, carry exponent zero, which is even, so the two readings agree and nothing is weakened. The proof is a thin honest wrapper over pinned Mathlib: the classification stated over the prime-factor support with the p-adic valuation is glued to the all-primes factorization form by discharging the out-of-support primes with the zero exponent. The source's proof route through descent at primes congruent to three modulo four, the representation of primes congruent to one modulo four, and the multiplicative composition identity is not attributed and is not reproved. Original numerical-certificate disposition: the source theorem is a purely universal biconditional and contains no numerical certificate.

## References

- Truth anchor: `D5/S3/PrimeForms/SumTwoSquaresClassification.eq_sq_add_sq_iff_even_factorization`
