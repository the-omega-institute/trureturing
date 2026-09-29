# Deterministic Word-Minimum Window Tables

## Abstract

Offline word orderings and labels have an exact average defect on every context without repeated words.

**Definition 1.1 (Candidate word types).**

Lean statement: `D5/S3/Combinatorics/FairWindowMinimizer.word`

*Formalization.* `D5/S3/Combinatorics/FairWindowMinimizer.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m and k, a binary block v of length m+k has k+1 candidate words of length m. Candidate i reads v(i+j) for every j less than m.

**Definition 1.2 (Leftmost minimum).**

Lean statement: `D5/S3/Combinatorics/FairWindowMinimizer.select`

*Formalization.* `D5/S3/Combinatorics/FairWindowMinimizer.select` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and every natural-valued rank function on positions zero through n, select is the least position among those attaining the minimum rank.

**Definition 1.3 (Ordering all word types).**

Lean statement: `D5/S3/Combinatorics/FairWindowMinimizer.rank`

*Formalization.* `D5/S3/Combinatorics/FairWindowMinimizer.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural m, a permutation rho of all binary m-words followed by their fixed finite enumeration assigns distinct natural ranks to word types. Each permutation represents one complete strict ordering.

**Definition 1.4 (A fixed strict-window table).**

Lean statement: `D5/S3/Combinatorics/FairWindowMinimizer.table`

*Formalization.* `D5/S3/Combinatorics/FairWindowMinimizer.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m and k, fix one word permutation rho and one binary label function beta on all m-words. On a binary window v of length m+k, choose the leftmost candidate a of minimum rank. Multiply the sign of beta at the chosen word by the relation signs at positions a+m through m+k-1. The output is one if this product is one, and zero otherwise. A zero bit has sign minus one and a one bit has sign one. The chosen tables are fixed across all contexts and times; the rule reads only this window.

**Theorem 1.5 (Exact defect on a context with distinct words).**

Lean statement: `D5/S3/Combinatorics/FairWindowMinimizer.good_context_average`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FairWindowMinimizer.good_context_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m greater than zero, every natural k, and every binary context v of length m+k+1, suppose its k+2 consecutive m-words are pairwise distinct. Uniformly average over all complete word permutations rho and, independently, all complete binary label functions beta. The average of the actual defect of table(m,k,rho,beta) on v is exactly 1/(k+2). Swapping word identities makes every candidate equally likely to have the least rank in the union of the two windows. The chosen position changes exactly when that minimum is at one of the two outer endpoints, giving frequency 2/(k+2). A common chosen position gives exact transport. For two distinct chosen words, flipping the label at the new word pairs defect zero with defect one, giving label average one half. This also includes k equal to zero, when the two candidate sets are disjoint.

## References

- Truth anchor: `D5/S3/Combinatorics/FairWindowMinimizer.good_context_average`
- Truth anchor: `D5/S3/Combinatorics/FairWindowMinimizer.rank`
- Truth anchor: `D5/S3/Combinatorics/FairWindowMinimizer.select`
- Truth anchor: `D5/S3/Combinatorics/FairWindowMinimizer.table`
- Truth anchor: `D5/S3/Combinatorics/FairWindowMinimizer.word`
- Dependency: [D5/S3/Combinatorics/FairWindowDefect](FairWindowDefect.md)
