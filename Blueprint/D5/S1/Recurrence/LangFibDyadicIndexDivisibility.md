# Dyadic Divisibility at Lang's Fibonacci Indices

## Abstract

Fibonacci numbers at Lang's dyadic indices have the conjectured power-of-two divisor.

The parameters n and m are natural numbers. Nat.fib is the Fibonacci sequence with Nat.fib(0)=0 and Nat.fib(1)=1. The symbol ∣ denotes divisibility in the natural numbers; multiplication and powers are natural-number operations. The subtraction n-2 is truncated natural subtraction, which agrees with ordinary subtraction under 3<=n. Only the first sentence of the A319197 comment is settled here. The product A(n)=Product_{j=3..n} a(j), the I(n; m) factorization conjecture, and the specific factors from A049660 and A253368 are not claimed.

**Theorem 1.1 (The dyadic divisibility conjecture).**

$$\forall n \in \mathbb{N}, m \in \mathbb{N},\; (3 \le n) \Rightarrow (2^{n} \mid \operatorname{Nat.fib}\left(2^{(n - 2)} \cdot 3 \cdot m\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LangFibDyadicIndexDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a319197-lang-fib-dyadic-index-divisibility` (proved) by `D5/S1/Recurrence/LangFibDyadicIndexDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a319197-lang-fib-dyadic-index-divisibility","declaration_gid":"D5/S1/Recurrence/LangFibDyadicIndexDivisibility.result","resolution_kind":"proved"} -->

*Citation.* Wolfdieter Lang (2018). *OEIS A319197, factors of Fibonacci(2^(n-2)*3*m), with the dyadic divisibility conjecture*. URL: <https://oeis.org/A319197>.

*Commentary.*

At n=3, Nat.fib(6)=8 and Fibonacci divisibility carries the factor 8 to Nat.fib(6m). Each increment of n doubles the index. The Fibonacci doubling identity expresses the new value as the old value times an even cofactor, so induction supplies one further factor of 2 at every step. Since 2^n is positive, divisibility gives the nonnegative-integral quotient in the quoted comment.

## References

- Truth anchor: `D5/S1/Recurrence/LangFibDyadicIndexDivisibility.result`
