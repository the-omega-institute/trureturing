# A Shifted Fibonacci Combination That Is Never Fibonacci

## Abstract

No Fibonacci number equals the n-th Fibonacci number plus 2n plus one times the next one.

**Definition 1.1 (The conjectured non-representation).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\forall m \in \mathrm{Nat},\; \operatorname{fib}\left(m\right) \ne \operatorname{fib}\left(n + 2\right) + 2 \cdot n \cdot \operatorname{fib}\left(n + 1\right)))$$

*Formalization.* `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.claim` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The closing paragraph of Section 6 of the source reads verbatim: "Nevertheless, we were not able to show that the two sets, the set of n times F of n over two plus three minus n minus one times F of n over two plus two for n at least one even, and the set of F of n plus one over two plus two for n at least one odd, are disjoint, or, equivalently, that for every n in N, the number F of n plus two plus two n times F of n plus one is not a Fibonacci number. We conjecture that this is so." The source indexes the Fibonacci numbers so that the first and second are both one, which is the indexing displayed here. Both of its two sets are indexed from one, so the natural numbers of the equivalent form start at one; at zero the number would be the second Fibonacci number itself, while the two sets are unchanged. Writing the even index as twice j turns the first set into the numbers displayed here, since twice j times the difference of two consecutive Fibonacci numbers is twice j times the earlier one.

**Theorem 1.2 (The conjectured non-representation holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result` (`✓ std3`). ∎

*Resolves.* `Problems/fried-fibonacci-shift-non-fibonacci` (proved) by `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fried-fibonacci-shift-non-fibonacci","declaration_gid":"D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Write X for the number in question. The recurrence rewrites it as the n-th Fibonacci number plus two n plus one times the next one. Suppose some Fibonacci number with index m equals X. For n at most seven the values of X are four, eleven, twenty-three, forty-eight, ninety-three, one hundred seventy-seven and three hundred twenty-eight, all below the fourteenth Fibonacci number, which is three hundred seventy-seven; monotonicity bounds m below fourteen and the finitely many remaining pairs are excluded by evaluation. For n at least eight, X is at least three times the Fibonacci number of index n plus one, so m is at least n plus two; write m as j plus n plus one with j at least one. The addition formula expresses the Fibonacci number of index j plus n plus one as F of j times F of n plus F of j plus one times F of n plus one, so the supposed equality becomes an equation between two such combinations. Since F of j is at least one, the coefficient F of j plus one is at most two n plus one, and the equation rearranges, with subtraction staying inside the natural numbers, to F of j minus one times F of n equals two n plus one minus F of j plus one times F of n plus one. If F of j equals one then j is at most two and F of j plus one is at most two, whereas cancelling the positive factor F of n from the original equation forces F of j plus one to equal two n plus one, which is at least seventeen. Otherwise F of j is at least two, so F of j minus one is positive. The rearranged identity shows that F of n plus one divides F of j minus one times F of n, and consecutive Fibonacci numbers are coprime, so F of n plus one divides F of j minus one and is therefore at most it. The left side of the identity is then at least F of n plus one times F of n, while its right side is at most two n times F of n plus one because F of j plus one is positive. Cancelling the positive factor F of n plus one gives F of n at most two n. That contradicts two n below F of n for n at least eight, which holds at eight because the eighth Fibonacci number is twenty-one, and propagates because each step adds a Fibonacci number of index at least seven, hence at least thirteen.

## References

- Truth anchor: `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.claim`
- Truth anchor: `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result`
