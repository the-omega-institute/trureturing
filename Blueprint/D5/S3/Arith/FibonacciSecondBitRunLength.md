# Runs in the Second Binary Digit of the Fibonacci Numbers

## Abstract

No three consecutive Fibonacci numbers carry the same second most significant binary digit.

**Definition 1.1 (The second binary digit).**

$$\forall m \in \mathrm{Nat},\; \operatorname{secondBit}\left(m\right) = \operatorname{mod}\left(\operatorname{div}\left(m, 2^{(\operatorname{size}\left(m\right) - 2)}\right), 2\right)$$

*Formalization.* `D5/S3/Arith/FibonacciSecondBitRunLength.secondBit` (`✓ std3`).

*Citation.* Andres Cicuttin (2016). *OEIS A272170, Second most significant bit of Fibonacci numbers > 1 written in base 2*. URL: <https://oeis.org/A272170>.

*Commentary.*

The source takes each Fibonacci number greater than one, writes it in base two, and records the digit just below the leading one. Dividing by two raised to the number of digits less two brings that place to the bottom, and the remainder on division by two reads it off.

**Definition 1.2 (The conjectured bound on runs).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (3 \le n) \Rightarrow (\neg ((\operatorname{secondBit}\left(\operatorname{fib}\left(n\right)\right) = \operatorname{secondBit}\left(\operatorname{fib}\left(n + 1\right)\right)) \land (\operatorname{secondBit}\left(\operatorname{fib}\left(n + 1\right)\right) = \operatorname{secondBit}\left(\operatorname{fib}\left(n + 2\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciSecondBitRunLength.claim` (`✓ std3`).

*Citation.* Andres Cicuttin (2016). *OEIS A272170, Second most significant bit of Fibonacci numbers > 1 written in base 2*. URL: <https://oeis.org/A272170>.

*Commentary.*

The comment on the sequence reads verbatim: "It is conjectured that there are no more than two consecutive zeros or ones (tested up to n equals ten to the fifth). The sequence looks quasiperiodic and its Fourier spectrum seems to have a fractal structure." Stated over the indices, no three consecutive entries agree. The sequence starts at the third Fibonacci number, the first one with a second binary digit.

**Theorem 1.3 (The bound holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciSecondBitRunLength.result` (`✓ std3`). ∎

*Resolves.* `Problems/fibonacci-second-bit-run-length` (proved) by `D5/S3/Arith/FibonacciSecondBitRunLength.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fibonacci-second-bit-run-length","declaration_gid":"D5/S3/Arith/FibonacciSecondBitRunLength.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andres Cicuttin (2016). *OEIS A272170, Second most significant bit of Fibonacci numbers > 1 written in base 2*. URL: <https://oeis.org/A272170>.

*Commentary.*

Bracketing a number between two consecutive powers of two turns the digit into an arithmetic condition: if twice a power of two is at most the number and four times that power exceeds it, then the digit is one exactly when three times the power is at most the number, because the quotient by the power is then two or three. Any such bracket reads the same digit, which lets the argument move one and two brackets up without tracking the number of digits. The other ingredient is a two-sided bound on consecutive terms, eight times a term at most five times the next and eight times the next at most thirteen times the term, holding from the fifth index on. Its content is that the interval from eight fifths to thirteen eighths is carried into itself by adding one to the reciprocal, so each half of the bound proves the other half one step later and the pair is a single induction, with both ends attained at the fifth index. Three ones would put twice the third term below twenty-one times the bracket while its own bracket demands twenty-four; three zeros would put the third term at or above six times the bracket inside a bracket where that already means a one. The first two indices are checked directly. No logarithms, no irrationality and no equidistribution enter, although the wording of the source points that way.

## References

- Truth anchor: `D5/S3/Arith/FibonacciSecondBitRunLength.claim`
- Truth anchor: `D5/S3/Arith/FibonacciSecondBitRunLength.result`
- Truth anchor: `D5/S3/Arith/FibonacciSecondBitRunLength.secondBit`
