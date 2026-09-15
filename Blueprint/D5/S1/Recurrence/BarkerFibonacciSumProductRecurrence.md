# Barker's Fibonacci Sum-Product Recurrence

## Abstract

The Fibonacci sum-product sequence satisfies Barker's three-and-six-step recurrence.

All indices and values are natural numbers. The predicate mem selects numbers that are both a sum of two Fibonacci values and a product of two Fibonacci values. The sequence a uses Nat.nth, whose index is zero-based; the OEIS sequence is one-based, so its definition uses natural subtraction at n = 0.

**Definition 1.1 (The Fibonacci sum-product membership predicate).**

$$\forall x \in \mathbb{N},\; \operatorname{mem}\left(x\right) \Leftrightarrow (\left(\exists i \in \mathbb{N}, j \in \mathbb{N},\; x = \operatorname{fib}\left(i\right) + \operatorname{fib}\left(j\right)\right) \land \left(\exists r \in \mathbb{N}, s \in \mathbb{N},\; x = \operatorname{fib}\left(r\right) \times \operatorname{fib}\left(s\right)\right))$$

*Formalization.* `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.mem` (`✓ std3`).

*Citation.* Colin Barker; Alonso del Arte (2014). *OEIS A226857, Numbers that are both the sum of two Fibonacci numbers and the product of two Fibonacci numbers*. URL: <https://oeis.org/A226857>.

*Commentary.*

A natural number belongs to mem exactly when it has both a representation as a sum of two Fibonacci numbers and a representation as a product of two Fibonacci numbers. Equal summands or factors are allowed; Fibonacci indexing uses F_0 = 0.

**Definition 1.2 (The one-based sequence from the membership predicate).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{nth}\left(mem, n - 1\right)$$

*Formalization.* `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.a` (`✓ std3`).

*Citation.* Colin Barker; Alonso del Arte (2014). *OEIS A226857, Numbers that are both the sum of two Fibonacci numbers and the product of two Fibonacci numbers*. URL: <https://oeis.org/A226857>.

*Commentary.*

The Lean sequence is Nat.nth mem (n - 1). Nat.nth enumerates members from zero, while the OEIS offset is one; natural subtraction therefore also specifies the value at n = 0.

**Theorem 1.3 (Barker's recurrence).**

$$\forall n \in \mathbb{N},\; 12 < n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{a}\left(n - 3\right) + \operatorname{a}\left(n - 6\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.barker_a226857` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a226857-fibonacci-sum-product-recurrence` (proved) by `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.barker_a226857`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a226857-fibonacci-sum-product-recurrence","declaration_gid":"D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.barker_a226857","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The classification of the membership set as {F_k, 2F_k, 3F_k}, proved using the product gap invariant and the interleaving of these three families, identifies the explicit enumeration with Nat.nth and yields the recurrence for every n greater than 12. The generating-function line and the accompanying %C corollaries are not claimed.

## References

- Truth anchor: `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.barker_a226857`
- Truth anchor: `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.mem`
