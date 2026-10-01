# Consecutive four-cycle diameter refutation

## Abstract

Conjecture 11 of CayleyPy-4 fails at n = 6: reversal cannot be reached in four consecutive-four-cycle moves, while the proposed diameter is four.

**Definition 1.1 (Nonwrapped consecutive four-cycle).**

Lean statement: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.cycle`

*Formalization.* `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.cycle` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The permutation of Fin n sends i to i + 1, i + 1 to i + 2, i + 2 to i + 3, and i + 3 to i, fixing every other point. The starting index satisfies i + 4 <= n.

**Definition 1.2 (Inverse-closed generators).**

Lean statement: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.generators`

*Formalization.* `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.generators` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

The generating set contains all these cycles and their inverses. The indices run from zero through n - 4; no cycle wraps around.

**Definition 1.3 (Cayley graph on the full symmetric group).**

Lean statement: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.graph`

*Formalization.* `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.graph` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Vertices are permutations of Fin n. Two distinct vertices u and v are adjacent when u times a generator equals v, or v times a generator equals u. Inverse closure identifies both alternatives with a single generator move. The diameter ediam takes values in the extended naturals, with infinity reserved for unbounded distances.

**Definition 1.4 (The proposed rational diameter).**

Lean statement: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.formula`

*Formalization.* `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.formula` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

Write F(n) for n(n - 1)/6 + 2/3 when n has residue two modulo three, and n(n - 1)/6 - 1 when its residue is zero or one. All subtraction and division in this formula take place in the rationals.

**Definition 1.5 (The complete k = 4 clause of Conjecture 11).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 6 \le n \Rightarrow \left(\exists d \in \mathbb{N},\; \operatorname{ediam}\left(\operatorname{graph}\left(n\right)\right) = \operatorname{castENat}\left(d\right) \land \operatorname{castRat}\left(d\right) = \operatorname{formula}\left(n\right)\right)\right)$$

*Formalization.* `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.claim` (`✓ std3`).

*Citation.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

For every n >= 6 the diameter must be finite and equal to F(n). The notation castENat embeds a natural into the extended naturals, and castRat embeds it into the rationals.

**Theorem 1.6 (Refutation of the complete universal clause).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chervov-2026-cayleypy4-conjecture-eleven-refutation` (refuted) by `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chervov-2026-cayleypy4-conjecture-eleven-refutation","declaration_gid":"D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2026). *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI tasks*. DOI: [10.48550/arXiv.2603.22195](https://doi.org/10.48550/arXiv.2603.22195). URL: <https://arxiv.org/abs/2603.22195v1>.

*Commentary.*

At n = 6 the six generators are (0123), (1234), (2345) and their inverses. Starting with the identity, repeatedly retain the current products and append each product times each generator. After four iterations the reversal (05)(14)(23) is absent. Induction on graph walks shows that a walk of length at most four from the identity ends among these products, including when an edge is expressed in reverse. The formula gives F(6) = 4. A diameter of four would bound the distance to reversal by four, and a shortest walk would then contradict its exclusion. This establishes falsity of the entire k = 4 clause; it does not determine the exact diameter or a corrected formula. Theorem 5 of the same paper already supplies a sufficient lower bound, so the bound and method are not new.

## References

- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.claim`
- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.cycle`
- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.formula`
- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.generators`
- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.graph`
- Truth anchor: `D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result`
