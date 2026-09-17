# First Occurrences in the Self-Referential Doubling Recurrence

## Abstract

Alkan's self-referential doubling recurrence has first-occurrence positions A117261.

The sequence a is totalized at index zero by a sentinel value one, while the source recurrence starts at index one. For every natural n at least two, the next value is twice the value at the floor of (n-1) divided by the preceding value.

The auxiliary sequence T is A117261 in recurrence form. The theorem states both the value at every block start and the least positive index carrying the corresponding power of two.

**Definition 1.1 (The A335901 recurrence).**

$$\operatorname{a}\left(1\right) = 1 \land \left(\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \operatorname{a}\left(n\right) = 2 \cdot \operatorname{a}\left(\left\lfloor\frac{n - 1}{\operatorname{a}\left(n - 1\right)}\right\rfloor\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.a` (`✓ std3`).

*Citation.* Altug Alkan (2020). *OEIS A335901, a(n) = 2*a(floor((n-1)/a(n-1))) with a(1) = 1*. URL: <https://oeis.org/A335901>.

*Commentary.*

The displayed clauses give a(1)=1 and the source recurrence for every natural n with n at least two. The sentinel at a(0) only totalizes the recursive definition and is not part of the source sequence.

**Definition 1.2 (The A117261 threshold sequence).**

$$\operatorname{T}\left(0\right) = 1 \land \left(\forall r \in \mathbb{N},\; \operatorname{T}\left(r + 1\right) = 2^{r} \cdot \operatorname{T}\left(r\right) + 1\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.T` (`✓ std3`).

*Citation.* Altug Alkan (2020). *OEIS A335901, a(n) = 2*a(floor((n-1)/a(n-1))) with a(1) = 1*. URL: <https://oeis.org/A335901>.

*Commentary.*

This is A117261 with T(0)=1 and T(r+1)=2^r times T(r) plus one for every natural r.

**Theorem 1.3 (Least indices for powers of two).**

$$\forall r \in \mathbb{N},\; \operatorname{a}\left(\operatorname{T}\left(r\right)\right) = 2^{r} \land \left(\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(\operatorname{a}\left(k\right) = 2^{r} \Rightarrow \operatorname{T}\left(r\right) \le k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.alkan_a335901` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a335901-self-referential-doubling-first-occurrence` (proved) by `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.alkan_a335901`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a335901-self-referential-doubling-first-occurrence","declaration_gid":"D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.alkan_a335901","resolution_kind":"proved"} -->

*Citation.* Altug Alkan (2020). *OEIS A335901, a(n) = 2*a(floor((n-1)/a(n-1))) with a(1) = 1*. URL: <https://oeis.org/A335901>.

*Commentary.*

For every natural r, the value at T(r) is 2^r. Every natural k with 1 <= k and a(k)=2^r is at least T(r), so T(r) is the least positive index carrying that value.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.alkan_a335901`
