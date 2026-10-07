# Mu–Welker Dyck valleys and bargraph statement

## Abstract

State Mu–Welker's Conjecture 3.9: UUDD-avoiding Dyck paths with `i` valleys are counted by bargraphs of semiperimeter `n` and width `i`.

**Definition 1.1 (The source-side predicates).**

*Formalization.* `D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs.AvoidsUUDD`, `valleys`, `ascent`, `semiperimeter`, and `IsBargraph`.

*Citation.* Lili Mu and Volkmar Welker (2026). *Simplicial Complexes of Antichains in Root Posets and Related Combinatorics of Dyck Paths*, arXiv:2609.14054v1, §3, Conjecture 3.9. URL: <https://arxiv.org/abs/2609.14054>.

*Commentary.* `AvoidsUUDD` is the maximal-face condition from the source's Lemma 3.4. `valleys` counts adjacent `DU` factors. A positive height list is a bargraph; `semiperimeter` is `length + h₁ + Σ max(hⱼ₊₁ − hⱼ, 0)`.

**Definition 1.2 (The conjecture statement).**

*Formalization.* `D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs.claim`.

The statement quantifies `n ≥ 2` and `1 ≤ i ≤ n−1`, equating the finite cardinality of the source-side Dyck words with the finite cardinality of positive height lists of length `i` and semiperimeter `n`. This file records the exact open target; it does not claim that the target is already resolved.

## References

- Truth anchor: `D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs.claim`
