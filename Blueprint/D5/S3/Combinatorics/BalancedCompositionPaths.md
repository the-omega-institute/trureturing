# Balanced Compositions Are Counted by Nonnegative Walks from Height Two

## Abstract

Nonnegative unit-step height sequences from two are as many as the compositions whose even parts are split evenly between odd and even positions, because both are windows of the same Pascal kernel.

**Definition 1.1 (Walks from height two).**

$$Walks(n) = \{s \mid (s(0) = 2) \land (\forall i \in Fin n,\; \left|s(i+1) - s(i)\right| = 1)\}$$

*Formalization.* `D5/S3/Combinatorics/BalancedCompositionPaths.walkCount` (`✓ std3`).

*Citation.* Gus Wiseman (2018). *OEIS A026010, a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 2*. URL: <https://oeis.org/A026010>.

*Commentary.*

A height sequence of length one more than the step count starts at two and moves by one at every step. The heights are natural numbers, so staying nonnegative costs nothing extra, and no height can exceed two plus the step count, so the sequences form a finite set and can be counted.

**Definition 1.2 (Compositions balanced across position parity).**

$$Balanced(m) = \{c \mid odd(c) = even(c)\}$$

*Formalization.* `D5/S3/Combinatorics/BalancedCompositionPaths.balancedCompositionCount` (`✓ std3`).

*Citation.* Gus Wiseman (2018). *OEIS A026010, a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 2*. URL: <https://oeis.org/A026010>.

*Commentary.*

A composition is balanced when its even parts occupy as many odd positions as even ones. Positions are counted from one, so the first part sits at an odd position; in terms of the zero-based index into the list of parts, an odd position is an even index. A composition with no even part is balanced. The worked list on the source entry fixes both readings: for total five the balanced compositions are five; three one one; one three one; one one three; two two one; one two two; and one one one one one. The tuple two one two is excluded, its two even parts sitting at the first and third positions.

**Definition 1.3 (The conjectured identity).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \lvert Walks(n) \rvert = \lvert Balanced(n + 2) \rvert)$$

*Formalization.* `D5/S3/Combinatorics/BalancedCompositionPaths.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2018). *OEIS A026010, a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 2*. URL: <https://oeis.org/A026010>.

*Commentary.*

The source asserts that the two counts agree once the total of the composition exceeds the step count by two, and reports the assertion checked as far as nineteen steps.

**Theorem 1.4 (The identity holds).**

$$\forall n \in \mathrm{Nat},\; \lvert Walks(n) \rvert = \lvert Balanced(n + 2) \rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BalancedCompositionPaths.result` (`✓ std3`). ∎

*Resolves.* `Problems/balanced-composition-paths` (proved) by `D5/S3/Combinatorics/BalancedCompositionPaths.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"balanced-composition-paths","declaration_gid":"D5/S3/Combinatorics/BalancedCompositionPaths.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2018). *OEIS A026010, a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 2*. URL: <https://oeis.org/A026010>.

*Commentary.*

Both sides are windows of one kernel. Write the kernel on the integers whose value at length zero is the indicator of the origin and which sends each entry to the sum of its two neighbours at the previous length; it is even in the displacement and is Pascal's array in displacement coordinates. For the walks, reflect across the line one below zero: the sequences that touch it correspond to all sequences starting four below zero, and summing over the end height telescopes because the subtracted index exceeds the added one by exactly three, leaving three consecutive kernel entries. For the compositions, recursion on the first part splits three ways: a first part of at least three loses two and keeps every position, a first part of one is deleted and reverses position parity, and a first part of two contributes one before being deleted. Tracking the signed difference between even parts at odd and at even positions, the count at a given difference is the sum of six consecutive kernel entries centred at three times that difference. At difference zero evenness folds that window into the same three-entry expression the reflection produced, term by term. No generating function and no square root enter. Each side is then tied to its literal objects, the finite set of height sequences on one hand and a filter on the compositions on the other, so the statement counts what the source counts.

## References

- Truth anchor: `D5/S3/Combinatorics/BalancedCompositionPaths.balancedCompositionCount`
- Truth anchor: `D5/S3/Combinatorics/BalancedCompositionPaths.claim`
- Truth anchor: `D5/S3/Combinatorics/BalancedCompositionPaths.result`
- Truth anchor: `D5/S3/Combinatorics/BalancedCompositionPaths.walkCount`
