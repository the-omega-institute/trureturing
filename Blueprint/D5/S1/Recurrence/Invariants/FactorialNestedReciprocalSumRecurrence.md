# The Factorial Nested Reciprocal Sum of OEIS A093345

## Abstract

The factorial nested reciprocal sum satisfies Mathar's third-order recurrence.

All indices are natural numbers, and a takes values in the rationals. Factorials and indices appearing as coefficients are cast to the rationals. Division and coefficient subtraction are rational operations; subtraction in the indices is natural subtraction. The hypothesis n >= 3 prevents truncation in the three preceding indices.

**Definition 1.1 (The factorial nested reciprocal sum).**

$$\forall n \in \mathbb{N}, a\left(n\right) = n! \cdot (1 + \sum_{i = 1}^{n} (\frac{1}{i} \cdot \sum_{j = 0}^{i - 1} (\frac{1}{j!})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.a` (`✓ std3`).

*Citation.* Richard J. Mathar (2014). *OEIS A093345, a(n) = n! * {1 + Sum[i=1..n, 1/i*Sum(j=0..i-1, 1/j!)]}*. URL: <https://oeis.org/A093345>.

*Commentary.*

The factor n! multiplies one plus the outer sum over i from 1 to n. Its ith summand is 1/i times the inner sum over j from 0 to i-1 of 1/j!. This is a rational-valued definition; integrality is not assumed.

**Theorem 1.2 (Mathar's third-order recurrence).**

$$\forall n \in \mathbb{N}, 3 \le n \implies a\left(n\right) - 2 \cdot n \cdot a\left(n - 1\right) + (n^{2} - 2) \cdot a\left(n - 2\right) - (n - 2)^{2} \cdot a\left(n - 3\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.mathar_a093345` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a093345-factorial-nested-reciprocal-sum-recurrence` (proved) by `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.mathar_a093345`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a093345-factorial-nested-reciprocal-sum-recurrence","declaration_gid":"D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.mathar_a093345","resolution_kind":"proved"} -->

*Citation.* Richard J. Mathar (2014). *OEIS A093345, a(n) = n! * {1 + Sum[i=1..n, 1/i*Sum(j=0..i-1, 1/j!)]}*. URL: <https://oeis.org/A093345>.

*Commentary.*

For the auxiliary prefix b(m)=m! times the sum of 1/j! over 0 <= j <= m, the factorial successor identity gives b(m+1)=(m+1)b(m)+1. The final outer summand gives a(m+1)=(m+1)a(m)+b(m). Three consecutive updates for a and two for b eliminate the prefix, and rational algebra yields the recurrence for every n at least three.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.mathar_a093345`
