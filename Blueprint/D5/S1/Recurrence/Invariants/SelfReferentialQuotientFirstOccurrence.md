# First Occurrences in a Self-Referential Quotient Recurrence

## Abstract

The first occurrences in Alkan's self-referential quotient recurrence are A000522 thresholds.

**Definition 1.1 (Alkan's recurrence).**

$$(\operatorname{a}\left(1\right) = 1) \land (\forall n \in \mathbb{N}, 2 \le n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{a}\left(\lfloor\frac{n - 1}{\operatorname{a}\left(n - 1\right)}\rfloor\right) + 1)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.a` (`✓ std3`).

*Citation.* Altug Alkan (2020). *OEIS A335925, a(n) = a(floor((n-1)/a(n-1))) + 1 with a(1) = 1*. URL: <https://oeis.org/A335925>.

*Commentary.*

The source sequence begins at index one. The formal definition assigns a(0)=1 only as a sentinel that totalizes the recursion; this value is not part of the source assertion. For every n>=2, the recursive argument is strictly below n.

**Definition 1.2 (The A000522 thresholds).**

$$(\operatorname{T}\left(0\right) = 1) \land (\forall r \in \mathbb{N}, \operatorname{T}\left(r + 1\right) = \left(r + 1\right) \cdot \operatorname{T}\left(r\right) + 1)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.T` (`✓ std3`).

*Citation.* Altug Alkan (2020). *OEIS A335925, a(n) = a(floor((n-1)/a(n-1))) + 1 with a(1) = 1*. URL: <https://oeis.org/A335925>.

*Commentary.*

This recurrence is A000522, beginning with 1, 2, 5, 16, 65, 326, and 1957.

**Theorem 1.3 (Alkan's first-occurrence conjecture).**

$$\forall m \in \mathbb{N}, 1 \le m \Rightarrow (\operatorname{a}\left(\operatorname{T}\left(m - 1\right)\right) = m \land \forall k \in \mathbb{N}, 1 \le k \Rightarrow \operatorname{a}\left(k\right) = m \Rightarrow \operatorname{T}\left(m - 1\right) \le k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.alkan_a335925` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a335925-self-referential-quotient-first-occurrence` (proved) by `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.alkan_a335925`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a335925-self-referential-quotient-first-occurrence","declaration_gid":"D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.alkan_a335925","resolution_kind":"proved"} -->

*Citation.* Altug Alkan (2020). *OEIS A335925, a(n) = a(floor((n-1)/a(n-1))) + 1 with a(1) = 1*. URL: <https://oeis.org/A335925>.

*Commentary.*

For every positive m, the threshold T(m-1) carries m. Any positive index k carrying m is at least that threshold. A two-step induction on threshold blocks shows that a(T(r))=r+1, that values on [T(r),T(r+1)) belong to {r,r+1}, and that an occurrence of r in this block lies below r*T(r). These bounds give both the hit and its minimality.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.alkan_a335925`
