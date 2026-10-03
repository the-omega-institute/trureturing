# Eventual periodicity of the self-banning rows

## Abstract

Every initialized infinite self-banning row of OEIS A398589 is eventually periodic.

The parameter k ranges over every natural number, including zero. Time t starts at zero. The row starts with k and at every later time emits the least integer x at least k for which every earlier occurrence at s satisfies s+x<t. Thus an occurrence bans its label for exactly the next x positions. The infinite row is used throughout; the finite display in OEIS stops at the end of the first periodic block.

**Definition 1.1 (The initialized least-legal row).**

$$\forall k \in \mathbb{N},\; a\left(k, 0\right) = k \land \left(\forall t \in \mathbb{N},\; (0 < t) \Rightarrow a\left(k, t\right) = \operatorname{min}\left(\{x \mid k \le x \land \left(\forall s \in \mathbb{N},\; (s < t \land a\left(k, s\right) = x) \Rightarrow s + x < t\right)\}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/OeisA398589EventualPeriodicity.row` (`✓ std3`).

*Citation.* Joshua B. Weinstein (2026). *OEIS A398589: eventual periodicity of self-banning rows*. URL: <https://oeis.org/A398589>.

*Commentary.*

The recursion is total. Among the t+1 candidates k through k+t, at least one is absent from the t previous positions and hence legal. The definition chooses the least legal value over all natural labels, without an imposed bound.

**Theorem 1.2 (All rows are eventually periodic).**

$$\forall k \in \mathbb{N},\; \exists N \in \mathbb{N},\; \exists p \in \mathbb{N},\; 0 < p \land \left(\forall t \in \mathbb{N},\; (N \le t) \Rightarrow a\left(k, t + p\right) = a\left(k, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OeisA398589EventualPeriodicity.eventual_periodicity` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a398589-all-row-eventual-periodicity` (proved) by `D5/S3/Combinatorics/OeisA398589EventualPeriodicity.eventual_periodicity`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a398589-all-row-eventual-periodicity","declaration_gid":"D5/S3/Combinatorics/OeisA398589EventualPeriodicity.eventual_periodicity","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua B. Weinstein (2026). *OEIS A398589: eventual periodicity of self-banning rows*. URL: <https://oeis.org/A398589>.

*Commentary.*

For k>0, the minimum label k occurs exactly at multiples of k+1. Put B=k(k+2). If every label from k through B were unavailable at a time t, their exclusion witnesses would lie in the same window of at most B positions. The k+1 recent clock occurrences, together with the witnesses for labels above k, give B+1 distinct positions in that window. Thus every term is at most B.

A state is the actual length-B window with values in {0,...,B}. At time t+B, a candidate x in [k,B] is legal exactly when every matching position i in the window satisfies i+x<B. Earlier occurrences cannot exclude x because x<=B. The transition shifts the window and appends the least eligible label. Its fallback is unreachable on the actual orbit by the bound and the legality equivalence. The initial window is the actual prefix at time zero.

The finite deterministic generator theorem, with both control and input equal to Unit, gives eventual periodicity of this orbit. The head projection is the original row value. For k=0 every term is zero. No minimal period or preperiod length is asserted, and the separate conjecture about nonempty preperiods for k>2 is outside this result.

## References

- Truth anchor: `D5/S3/Combinatorics/OeisA398589EventualPeriodicity.eventual_periodicity`
- Truth anchor: `D5/S3/Combinatorics/OeisA398589EventualPeriodicity.row`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity](../ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity.md)
