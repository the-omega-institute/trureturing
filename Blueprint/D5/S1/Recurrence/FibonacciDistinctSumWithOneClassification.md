# Distinct Fibonacci Sums Containing One

## Abstract

Fibonacci sets containing one have Fibonacci sum exactly in alternating form.

Write F(n) for the Fibonacci sequence with F(0)=0, F(1)=1, and F(n+2)=F(n)+F(n+1). All indices and values are natural numbers.

**Definition 1.1 (Positive Fibonacci values).**

$$\forall x \in \mathrm{Nat},\; PositiveFibonacci\left(x\right) \Leftrightarrow \left(\exists n \in \mathrm{Nat},\; (2 \le n) \land (F\left(n\right) = x)\right)$$

*Formalization.* `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.PositiveFibonacci` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive values are 1, 2, 3, 5, 8, and so on. Starting the indices at two counts the value one only once.

**Definition 1.2 (Alternating initial sets).**

$$\forall r \in \mathrm{Nat},\; A\left(r\right) = \{1\} \cup \{F\left(2 \cdot j + 1\right) \mid 1 \le j < r\}$$

*Formalization.* `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.alternatingSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(r) consists of one and the Fibonacci values F(2j+1) for 1 <= j < r. In particular, A(1) is the singleton containing one.

**Theorem 1.3 (Classification and unique parameter).**

$$\forall S \in Finset\left(\mathrm{Nat}\right),\; ((\forall x \in \mathrm{Nat},\; (x \in S) \Rightarrow PositiveFibonacci\left(x\right)) \land (1 \in S)) \Rightarrow \left((PositiveFibonacci\left(\sum_{x \in S} x\right) \Leftrightarrow \left(\exists r \in \mathrm{Nat},\; (1 \le r) \land (S = A\left(r\right))\right)) \land (\forall r \in \mathrm{Nat},\; ((1 \le r) \land (S = A\left(r\right))) \Rightarrow \left((\sum_{x \in S} x = F\left(2 \cdot r\right)) \land (\forall t \in \mathrm{Nat},\; ((1 \le t) \land (S = A\left(t\right))) \Rightarrow t = r)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be any finite set of positive Fibonacci values containing one. Its sum is a positive Fibonacci value if and only if S=A(r) for some r at least one. For every such r, the sum is F(2r), and any t at least one with S=A(t) equals r. No assumption excludes adjacent Fibonacci indices.

If the sum is F(n) and n exceeds two, every member is strictly smaller than F(n). The sum of the Fibonacci values from index two through n-2 is F(n)-2, so F(n-1) must occur. Index three is impossible. At index at least four, deleting F(n-1) preserves one and leaves sum F(n-2). Strong induction therefore forces exactly the alternating initial set. Conversely the recurrence sums A(r) to F(2r); strict increase from index two gives uniqueness.

## References

- Truth anchor: `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.PositiveFibonacci`
- Truth anchor: `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.alternatingSet`
- Truth anchor: `D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.classification`
