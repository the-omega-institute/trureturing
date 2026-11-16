# Bounded reflection differences for every word of linear complexity

## Abstract

Linear factor complexity implies bounded integer reflection differences.

**Definition 1.1 (Conjecture 28: the bounded-difference assertion).**

$$\operatorname{claim} = (\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall x: \mathbb{N} \to A, (\exists C: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{Finset.card}\left(\operatorname{wordFactorSet}\left(x, k\right)\right) \le C \cdot \left(k + 1\right)) \Rightarrow (\exists B: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{Int.natAbs}\left((\operatorname{reflectionComplexity}\left(x, n + 1\right): \mathbb{Z}) - (\operatorname{reflectionComplexity}\left(x, n\right): \mathbb{Z})\right) \le B))$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.claim` (`✓ std3`).

*Citation.* Jean-Paul Allouche; John M. Campbell; Shuo Li; Jeffrey Shallit; Manon Stipulanti (2025). *The reflection complexity of sequences over finite alphabets*. DOI: [10.1007/s00224-025-10234-x](https://doi.org/10.1007/s00224-025-10234-x). URL: <https://arxiv.org/abs/2406.09302v4>.

*Commentary.*

Conjecture 28, p. 15: “Let x be a sequence of at most linear factor complexity. Then rₓ(n+1)−rₓ(n) is bounded for all n ≥ 0. Hence, in particular, if x is (generalized) automatic, so is (rₓ(n+1)−rₓ(n))ₙ≥₀.” Here the proposition is the full bounded-difference assertion. The alphabet is any finite type, x is any one-sided word, and every length n includes zero. The hypothesis p(n) ≤ C(n + 1) expresses at most linear factor complexity. Differences are taken in ℤ before Int.natAbs. The source's automaticity sentence is outside this proposition; generalized numeration requires its addable positional-numeration hypotheses.

**Theorem 1.2 (Every such word has bounded reflection differences).**

$$\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall x: \mathbb{N} \to A, (\exists C: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{Finset.card}\left(\operatorname{wordFactorSet}\left(x, k\right)\right) \le C \cdot \left(k + 1\right)) \Rightarrow (\exists B: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{Int.natAbs}\left((\operatorname{reflectionComplexity}\left(x, n + 1\right): \mathbb{Z}) - (\operatorname{reflectionComplexity}\left(x, n\right): \mathbb{Z})\right) \le B)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.result` (`✓ std3`). ∎

*Resolves.* `Problems/acls-reflection-complexity-c28` (proved) by `D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"acls-reflection-complexity-c28","declaration_gid":"D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Paul Allouche; John M. Campbell; Shuo Li; Jeffrey Shallit; Manon Stipulanti (2025). *The reflection complexity of sequences over finite alphabets*. DOI: [10.1007/s00224-025-10234-x](https://doi.org/10.1007/s00224-025-10234-x). URL: <https://arxiv.org/abs/2406.09302v4>.

*Commentary.*

Place a new marker between the two sides of a bi-infinite mirror of x. Its factor count is the reversal-symmetrized count plus n. For a bi-infinite language, every fixed-offset cropping map is surjective. Weighted factor graphs then control intermediate excess using two lengths with small increments: a cut estimate forces heavy edges to return, and word overlap prevents two heavy outgoing edges. Linear growth supplies those two lengths by interval averaging. The resulting mirror increment bound transfers through reflection-orbit and palindromic-loop counts to the displayed absolute-difference bound. The same proof includes periodic words and transient prefixes. It supplies a finite bound without asserting optimal dependence on the growth coefficient.

## References

- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.claim`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.result`
- Dependency: [D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport](AlloucheReflectionComplexitySupport.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
