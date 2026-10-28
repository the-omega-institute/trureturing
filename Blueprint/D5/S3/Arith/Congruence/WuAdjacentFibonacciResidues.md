# Wu's Adjacent-Index Fibonacci Divisibility Conjecture

## Abstract

An index whose Fibonacci number is divisible by itself and both neighbours ends in zero, two or eight.

**Definition 1.1 (The A221018 assertion).**

$$claim = (\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow ((k - 1 \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k + 1 \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k \bmod 10 = 0) \lor ((k \bmod 10 = 2) \lor (k \bmod 10 = 8)))))))$$

*Formalization.* `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.claim` (`✓ std3`).

*Citation.* Chai Wah Wu; Alex Ratushnyak (2026). *OEIS A221018, first FORMULA conjecture on adjacent-index Fibonacci divisibility*. URL: <https://oeis.org/A221018/internal>.

*Commentary.*

OEIS A221018, revision 35, NAME: “Number k such that Fibonacci(k) is divisible by k, k + 1 and k - 1.” The first FORMULA line reads: “a(n) % 10 == 0, 2, or 8 (conjectured). - _Chai Wah Wu_, Aug 06 2026”. The web entry has no page number. The generator starts at two, so k ranges over natural numbers at least two. Nat.fib has F(0)=0, F(1)=1 and F(n+2)=F(n)+F(n+1). The three divisibilities are separate implication hypotheses. Subtraction is natural subtraction, which agrees with integer subtraction here; % denotes natural-number remainder. No converse is asserted.

**Theorem 1.2 (The final-digit theorem).**

$$\forall k \in \mathbb{N},\; (2 \le k) \Rightarrow ((k - 1 \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k + 1 \mid \operatorname{Nat}.\operatorname{fib}\left(k\right)) \Rightarrow ((k \bmod 10 = 0) \lor ((k \bmod 10 = 2) \lor (k \bmod 10 = 8))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu221018-fibdiv` (proved) by `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu221018-fibdiv","declaration_gid":"D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; Alex Ratushnyak (2026). *OEIS A221018, first FORMULA conjecture on adjacent-index Fibonacci divisibility*. URL: <https://oeis.org/A221018/internal>.

*Commentary.*

One of k and k+1 is even, so their divisibility into Nat.fib(k) makes that Fibonacci number even. The equivalence between Fibonacci divisibility and index divisibility, applied at indices three and four, forces 3 and 4 to divide k, hence 12 divides k. If k has remainder one or four modulo five, one neighbour is divisible by five. The same equivalence at index five then forces five to divide k, a contradiction. Evenness and these two exclusions leave final digits zero, two and eight.

## References

- Truth anchor: `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.claim`
- Truth anchor: `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.result`
- Dependency: [D5/S1/Recurrence/GoldenFibDivisibility](../../../S1/Recurrence/GoldenFibDivisibility.md)
