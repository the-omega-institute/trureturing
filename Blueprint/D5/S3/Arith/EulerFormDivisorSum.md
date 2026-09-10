# Euler-form divisor sums

## Abstract

Every Euler-form number in A228058 satisfies the strict divisor-sum inequality of A388986.

Let p be a prime congruent to one modulo four, let a be a natural number, and let r be odd, greater than one, and coprime to p. Put N=p^(4a+1)r^2. The two functions below sum actual divisors of N, including one.

**Definition 1.1 (The unitary divisor sum).**

$$\forall N \in \mathbb{N}, \operatorname{unitarySum}\left(N\right) = \sum_{d \in \operatorname{divisors}\left(N\right), \operatorname{gcd}\left(d, \frac{N}{d}\right) = 1} d$$

*Formalization.* `D5/S3/Arith/EulerFormDivisorSum.unitarySum` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2026). *OEIS A388986*. URL: <https://oeis.org/A388986>.

*Commentary.*

A divisor d is unitary when d and N/d are coprime. The quotient is exact on the divisor set. This definition also includes N itself.

**Definition 1.2 (The squarefree divisor sum).**

$$\forall N \in \mathbb{N}, \operatorname{squarefreeSum}\left(N\right) = \sum_{d \in \operatorname{divisors}\left(N\right), \operatorname{Squarefree}\left(d\right)} d$$

*Formalization.* `D5/S3/Arith/EulerFormDivisorSum.squarefreeSum` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2026). *OEIS A388986*. URL: <https://oeis.org/A388986>.

*Commentary.*

The sum ranges over divisors containing no square factor greater than one. Its prime-support product is obtained from Mathlib's powerset identity.

**Theorem 1.3 (The Euler-form inclusion).**

$$\forall p \in \mathbb{N}, \forall a \in \mathbb{N}, \forall r \in \mathbb{N}, \operatorname{prime}\left(p\right) \land p \bmod 4 = 1 \land \operatorname{Odd}\left(r\right) \land 1 < r \land \operatorname{gcd}\left(p, r\right) = 1 \Rightarrow \operatorname{unitarySum}\left({p}^{4 \cdot a + 1} \cdot {r}^{2}\right) + \operatorname{squarefreeSum}\left({p}^{4 \cdot a + 1} \cdot {r}^{2}\right) < 2 \cdot {p}^{4 \cdot a + 1} \cdot {r}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/EulerFormDivisorSum.euler_form_lt` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a388986-euler-form-divisor-sum` (proved) by `D5/S3/Arith/EulerFormDivisorSum.euler_form_lt`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a388986-euler-form-divisor-sum","declaration_gid":"D5/S3/Arith/EulerFormDivisorSum.euler_form_lt","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2026). *OEIS A388986*. URL: <https://oeis.org/A388986>.

*Commentary.*

After dividing by positive N, the distinguished prime contributes at most six fifths to each product. Every prime from r has exponent at least two. A finite reciprocal-square product bound, with separate cases for whether the support contains three and another prime, bounds the remaining sum strictly below five thirds. Their product is strictly below two. The hypothesis r>1 supplies a nonempty support; for r=1 and p=5 the claimed inequality would fail.

## References

- Truth anchor: `D5/S3/Arith/EulerFormDivisorSum.euler_form_lt`
- Truth anchor: `D5/S3/Arith/EulerFormDivisorSum.squarefreeSum`
- Truth anchor: `D5/S3/Arith/EulerFormDivisorSum.unitarySum`
