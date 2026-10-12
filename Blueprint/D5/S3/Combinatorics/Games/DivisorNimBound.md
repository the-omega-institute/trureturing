# The Sharper Sprague–Grundy Bound for Divisor Nim

## Abstract

For every nonempty board of positive heaps, the Grundy value is at most twice the smallest heap.

**Theorem 1.1 (Twice the smallest heap).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \operatorname{Positive}\left(P\right) \Rightarrow \left(P \ne 0 \Rightarrow \left(\forall m \in \mathrm{Nat},\; m \in P \Rightarrow \left(\left(\forall h \in \mathrm{Nat},\; h \in P \Rightarrow m \le h\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 2 \cdot m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/tyagi-2026-divisor-nim-sharper-sg-bound` (proved) by `D5/S3/Combinatorics/Games/DivisorNimBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tyagi-2026-divisor-nim-sharper-sg-bound","declaration_gid":"D5/S3/Combinatorics/Games/DivisorNimBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Write the distinguished heap as two to its valuation times a positive odd part. A sufficiently large odd part is covered by the coarse ceiling. For smaller odd parts the divisor-sensitive recurrence is bounded by the large-valuation integer estimates or the finite valuation range. The remaining distinguished heaps of sizes two, four, and eight satisfy direct bounds. Choose a smallest heap.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBound.result`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundEight](DivisorNimBoundEight.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundSmall](DivisorNimBoundSmall.md)
