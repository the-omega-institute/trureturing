# The prime-successor conjecture of A375007

## Abstract

For every isolated quotient-remainder value t greater than 24, t+1 is prime.

**Definition 1.1 (Isolation in the natural interval).**

$$\forall t: \mathbb{N}, \operatorname{P}\left(t\right) \iff (\forall k: \mathbb{N}, 1 \le k \implies k \le t \implies (t \bmod k = \operatorname{natDiv}\left(\operatorname{natSub}\left(t, k\right), k\right) \bmod k \implies (k = 1 \lor k = t)))$$

*Formalization.* `D5/S3/Arith/IsolatedQuotientRemainder.P` (`✓ std3`).

*Citation.* Lechoslaw Ratajczak (2024). *A375007 — isolated quotient-remainder values*. URL: <https://oeis.org/A375007>.

*Commentary.*

All variables are natural numbers. The symbols mod, natDiv and natSub denote natural remainder, floor division and truncated subtraction. The bounds 1<=k<=t ensure that subtraction agrees with ordinary subtraction. P asserts only that the displayed equality can occur at the two endpoints.

**Theorem 1.2 (Every isolated value above 24 has prime successor).**

$$\forall t: \mathbb{N}, 24 < t \implies \operatorname{P}\left(t\right) \implies \operatorname{Prime}\left(t + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IsolatedQuotientRemainder.a375007_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lechoslaw Ratajczak (2024). *A375007 — isolated quotient-remainder values*. URL: <https://oeis.org/A375007>.

*Commentary.*

If t+1 is composite, its least prime factor a and complementary factor b satisfy 2<=a<=b. When a<b, set k=b-1. Then t=a*k+(a-1), with a-1<k, so both remainders equal a-1. When a=b=u, the threshold implies u>=6. Set k=u-2; then t=(u+2)*k+3 and 3<k. Subtracting k lowers the quotient by one, and (u+1) mod (u-2)=3. Each case gives 1<k<t, contradicting P. This proves the value formulation of the first OEIS conjecture; the first six listed values end at 24. The sequence enumeration and the separate conjecture about products of successive differences are outside this statement.

## References

- Truth anchor: `D5/S3/Arith/IsolatedQuotientRemainder.P`
- Truth anchor: `D5/S3/Arith/IsolatedQuotientRemainder.a375007_prime`
