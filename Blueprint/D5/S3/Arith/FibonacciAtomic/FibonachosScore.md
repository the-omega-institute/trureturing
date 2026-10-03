# Fibonachos score

## Abstract

Fibonachos ties and large-heap majority follow Fibonacci blocks.

Let fib be the Fibonacci sequence with fib(0)=0 and fib(1)=1. Starting from n objects and index one, two players alternate taking fib(i) objects and increasing i by one. When fib(i) exceeds the remaining heap, i resets to one before the move. The game ends at the empty heap. The recursive pair play(n,i) gives the scores of the player to move and the other player: a move of size q returns (q+second,first) from the smaller heap. This is the same update as the OEIS program, with the player flag expressed by swapping the pair. Let a(n)=play(n,1).first and D(n)=2a(n)-n. The first ten a-values are 1,1,2,3,3,4,3,4,4,5.

**Theorem 1.1 (Ties and first-player majority).**

$$\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(2a\left(n\right) = n \Leftrightarrow n \in \left\{2, 8, 10, 32\right\}\right)\right) \land \left(\forall n \in \mathbb{N},\; 32 < n \Rightarrow \left(n < 2a\left(n\right) \Leftrightarrow \left(\exists m \in \mathbb{N},\; Odd\left(m\right) \land \left(fib\left(m\right) \le n+1 \land n+2 \le fib\left(m+1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FibonachosScore.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a382814-fibonachos-score` (proved) by `D5/S3/Arith/FibonacciAtomic/FibonachosScore.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a382814-fibonachos-score","declaration_gid":"D5/S3/Arith/FibonacciAtomic/FibonachosScore.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2025). *OEIS A382814: first-player score in the Fibonachos game*. URL: <https://oeis.org/A382814>.

*Commentary.*

The first uninterrupted segment in the block fib(m)-1 <= n <= fib(m+1)-2 consumes fib(m)-1 objects. With r=n-(fib(m)-1), its alternating score gives D(n)=1+(-1)^m(D(r)-fib(m-3)). The uniform estimate |D(u)-1| <= fib(t-3), for t>=4 and 0<=u<fib(t), follows by induction over these blocks. For n>32 it makes D(n) positive exactly in odd blocks and excludes ties. The smaller positive heaps have ties precisely at 2,8,10,32. The displayed inequalities fib(m)<=n+1 and n+2<=fib(m+1) express the original interval without natural-number subtraction; for n>32 the upper endpoint forces fib(m+1)>=2, so the two forms are equivalent. The comparison uses 2a(n) to avoid rounding n/2.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FibonachosScore.result`
