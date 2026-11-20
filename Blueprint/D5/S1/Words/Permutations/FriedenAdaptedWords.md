# Four-wire avoidance characterizes adaptedness

## Abstract

Four-wire avoidance and source-flip adaptedness in arbitrary rank.

An orientation assigns a direction to every edge between two consecutive generators. A generator is legal when all its incident edges point away from it. Using it reverses precisely those edges.

**Theorem 1.1 (The avoidance-to-adaptedness implication of Conjecture 4.10).**

$$\forall n \in \mathbb{N},\; \forall w \in Word\left(n\right),\; ReducedReversal\left(w\right) \implies (AvoidsX\left(w\right) \implies Adapted\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

For each natural n and each word on the n-1 adjacent generators, suppose its length is n(n-1)/2 and its chronological swaps send the identity to the reversal. Suppose also that restricting to any four labels gives a word outside X, whose elements are 123212, 321232, 212321 and 232123. Then there exists an initial path orientation in which the entire word is a legal sequence of source flips. Each two-generator projection must alternate because a repetition would force one of the four restrictions, with reflection exchanging the two ends of the edge. The first letter in each projection determines the edge direction needed for the sequence.

**Theorem 1.2 (Conjecture 4.10).**

$$\forall n \in \mathbb{N},\; \forall w \in Word\left(n\right),\; ReducedReversal\left(w\right) \implies (AvoidsX\left(w\right) \iff Adapted\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410` (`✓ std3`). ∎

*Resolves.* `Problems/frieden-2026-adapted-reversal-words` (proved) by `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"frieden-2026-adapted-reversal-words","declaration_gid":"D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

In the converse direction, the last move of a wire at an interior position leaves an incident arrow blocking a return. Thus a turn is possible only at an endpoint. Two turns would require crossing the entire network between moves into and out of its endpoints. This would exceed the n-1 moves available to a wire, since it crosses each other label once. Restriction retains a subsequence of the moves of each selected wire, with their directions preserved. Each word in X contains a wire whose retained directions alternate twice.

## References

- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410`
- Dependency: [D5/S1/Words/Permutations/FriedenSortingNetwork](FriedenSortingNetwork.md)
