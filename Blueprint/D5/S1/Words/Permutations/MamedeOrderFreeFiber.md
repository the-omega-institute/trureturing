# First-Orientation Singleton Fiber

## Abstract

The first-orientation endpoint data determine the entire singleton-word fiber when j<i.

**Theorem 1.1 (Whole-fiber uniqueness for j<i).**

$$1 \le m < j < i < M \le n \land \operatorname {Endpoints}\left(sigma, m, M, i, j\right) \land \operatorname {ExteriorFixed}\left(sigma, m, M\right) \land \operatorname {SingletonWord}\left(n, sigma, a\right) \land \operatorname {SingletonWord}\left(n, sigma, b\right) \implies a = b$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOrderFreeFiber.singleton_fiber_unique_of_j_lt_i` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

For arbitrary n,m,M,i,j with 1<=m<j<i<M<=n, let sigma be a permutation of the n+1 positions in the repository's one-based position convention. Assume sigma(M+1)=m, sigma(m)=j+1, sigma(i)=M+1, and sigma fixes every position outside [m,M+1]. Then any two singletonWord(n,sigma) lists are equal. For each source list, guarded walks force a descent j..m, an ascent m..M, and a descent M..i. Aligning their shared m and M markers yields the exact sourceShape, with every prefix letter in (m,j) and every suffix letter in (i,M). The existing factor-separation theorem then identifies two such lists. The proof includes adjacent endpoints i=j+1 and empty outer factors. The theorem is conditional on all three endpoint equations and exterior fixedness; the separate nonoscillating source-endpoint theorem derives these from an actual first-orientation source word with attained generator extrema. It formalizes this first-orientation part of Proposition 3.7 and does not settle global Conjecture 5.1. The repository's singletonWord interpretation of the paper's commutation classes remains a source-translation judgment.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeOrderFreeFiber.singleton_fiber_unique_of_j_lt_i`
