# Four-wire avoidance characterizes adaptedness

## Abstract

Four-wire avoidance and source-flip adaptedness in arbitrary rank.

An orientation assigns a direction to every edge between two consecutive generators. A generator is legal when all its incident edges point away from it. Using it reverses precisely those edges.

**Definition 1.1 (Generator incidence).**

$$\forall n \in \mathbb{N},\; \forall e \in \operatorname{Fin}\left(n-2\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{edgeVisit}\left(e, i\right):\operatorname{Option}\left(\operatorname{Bool}\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.edgeVisit` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

On edge e, the letter e returns true and the letter e+1 returns false. Every other letter returns none.

**Definition 1.2 (Source at a generator).**

$$\forall n \in \mathbb{N},\; \forall o \in \operatorname{Orientation}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{SourceAt}\left(o, i\right) \iff \forall e \in \operatorname{Fin}\left(n-2\right),\; \forall b \in \operatorname{Bool},\; \operatorname{edgeVisit}\left(e, i\right) = \operatorname{some}\left(b\right) \implies o\left(e\right) = b$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.SourceAt` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

For every edge and every Boolean returned by edgeVisit for this generator, the orientation of that edge equals the returned Boolean.

**Definition 1.3 (Source flip).**

$$\forall n \in \mathbb{N},\; \forall o \in \operatorname{Orientation}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n-1\right),\; \operatorname{flip}\left(o, i\right):\operatorname{Orientation}\left(n\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.flip` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

Negate the orientation of precisely the incident edges.

**Definition 1.4 (Legal sequence of source flips).**

$$\forall n \in \mathbb{N},\; \forall o \in \operatorname{Orientation}\left(n\right),\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{Legal}\left(o, w\right):\operatorname{Prop}$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.Legal` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

The empty word is legal. A nonempty word requires its first generator to be a source and its remaining letters to be legal after the first flip.

**Definition 1.5 (Adapted word).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{Adapted}\left(w\right) \iff \exists o \in \operatorname{Orientation}\left(n\right),\; \operatorname{Legal}\left(o, w\right)$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.Adapted` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

There exists an initial orientation for which the whole word is legal.

**Definition 1.6 (Avoidance and adaptedness in Conjecture 4.10).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{ReducedReversal}\left(w\right) \implies (\operatorname{AvoidsX}\left(w\right) \iff \operatorname{Adapted}\left(w\right))$$

*Formalization.* `D5/S1/Words/Permutations/FriedenAdaptedWords.claim` (`✓ std3`).

*Citation.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

Conjecture 4.10, p. 15. “A reduced word for w₀ ∈ 𝔖ₙ is X-avoiding if and only if it is adapted to an orientation of Aₙ₋₁.” The quantifier ranges over all natural n. Word uses zero-based adjacent generators. AvoidsX uses one-based letters for the retained crossings on each four-element set of labels. Adapted tests for a source before every flip.

**Theorem 1.7 (The avoidance-to-adaptedness implication of Conjecture 4.10).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{ReducedReversal}\left(w\right) \implies (\operatorname{AvoidsX}\left(w\right) \implies \operatorname{Adapted}\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

For each natural n and each word on the n-1 adjacent generators, suppose its length is n(n-1)/2 and its chronological swaps send the identity to the reversal. Suppose also that restricting to any four labels gives a word outside X, whose elements are 123212, 321232, 212321 and 232123. Then there exists an initial path orientation in which the entire word is a legal sequence of source flips. The projection onto the two endpoints of each path edge must alternate because a repetition would force one of the four restrictions, with reflection exchanging the two ends of the edge. The first letter in each projection determines the edge direction needed for the sequence.

**Theorem 1.8 (Conjecture 4.10).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(n\right),\; \operatorname{ReducedReversal}\left(w\right) \implies (\operatorname{AvoidsX}\left(w\right) \iff \operatorname{Adapted}\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410` (`✓ std3`). ∎

*Resolves.* `Problems/frieden-2026-adapted-reversal-words` (proved) by `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"frieden-2026-adapted-reversal-words","declaration_gid":"D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Frieden, Pavlo Pylyavskyy, Leonid Rybnikov (2026). *The big cactus group, invariant tensors, and rectangular tableaux*. DOI: [10.48550/arXiv.2610.24842](https://doi.org/10.48550/arXiv.2610.24842). URL: <https://arxiv.org/html/2610.24842v1>.

*Commentary.*

This proves the named proposition claim. In the converse direction, the last move of a wire at an interior position leaves an incident arrow blocking a return. Thus a turn is possible only at an endpoint. Two turns would require crossing the entire network between moves into and out of its endpoints. This would exceed the n-1 moves available to a wire, since it crosses each other label once. Restriction retains a subsequence of the moves of each selected wire, with their directions preserved. Each word in X contains a wire whose retained directions alternate twice.

## References

- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.Adapted`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.Legal`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.SourceAt`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.claim`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.edgeVisit`
- Truth anchor: `D5/S1/Words/Permutations/FriedenAdaptedWords.flip`
- Dependency: [D5/S1/Words/Permutations/FriedenSortingNetwork](FriedenSortingNetwork.md)
