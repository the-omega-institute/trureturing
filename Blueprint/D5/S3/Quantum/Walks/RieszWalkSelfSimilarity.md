# RieszWalkSelfSimilarity

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

**Definition 1.1 (prob).**

$$\forall (t : \mathbb{N}) (S : Set \mathbb{Q}) , \operatorname{prob} t S = \sum ' (y : \mathbb{N}) , \operatorname{if} \operatorname{Nat.cast}\left(y\right) / \operatorname{Nat.cast}\left(t\right) \in S \operatorname{then} \operatorname{mu} t y \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.prob` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

The sum is over all natural-number sites. Finite propagation makes only finitely many terms nonzero. Rational division gives the normalized site position.

**Definition 1.2 (Tset).**

$$\forall (n k : \mathbb{N}) , \operatorname{Tset} n k = \operatorname{if} k = 0 \operatorname{then} \{0\} \operatorname{else} \operatorname{Set.Ioc} ((\operatorname{Nat.cast}\left(k\right) - 1) / \operatorname{Nat.cast}\left(n\right)) (\operatorname{Nat.cast}\left(k\right) / \operatorname{Nat.cast}\left(n\right))$$

*Formalization.* `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.Tset` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 4, Conjecture 4.2, arXiv PDF p. 12: “Let ℤ_> = {1, 2, 3, …}. For each n ∈ ℤ_>, we put T₀(n) = {0}, and Tₖ(n) = ((k − 1)/n, k/n] (1 ≤ k ≤ n). Then, for the measure of the Riesz walk with initial state of Ψ₀ = [1, 0]ᵀδ₀, P(X₂ₜ/(2t) ∈ Tₖ(t)) = P(X₈ₜ/(8t) ∈ Tₖ(t)), for any t ∈ ℤ_>.” The case k=0 is a singleton; every other case is left-open and right-closed.

**Definition 1.3 (claim).**

$$\operatorname{claim} \iff \forall (t : \mathbb{N}) , 1 \leq t \to \forall (k : \mathbb{N}) , k \leq t \to \operatorname{prob} (2 \cdot t) (\operatorname{Tset} t k) = \operatorname{prob} (8 \cdot t) (\operatorname{Tset} t k)$$

*Formalization.* `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.claim` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 4, Conjecture 4.2, arXiv PDF p. 12: “Let ℤ_> = {1, 2, 3, …}. For each n ∈ ℤ_>, we put T₀(n) = {0}, and Tₖ(n) = ((k − 1)/n, k/n] (1 ≤ k ≤ n). Then, for the measure of the Riesz walk with initial state of Ψ₀ = [1, 0]ᵀδ₀, P(X₂ₜ/(2t) ∈ Tₖ(t)) = P(X₈ₜ/(8t) ∈ Tₖ(t)), for any t ∈ ℤ_>.” Here t and k are natural numbers, 1 ≤ t and k ≤ t. The two coordinates at site x are 2x and 2x+1. The intervals have rational endpoints and probabilities are real.

**Theorem 1.4 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanaoka-konno-2021-riesz-walk-self-similarity` (proved) by `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanaoka-konno-2021-riesz-walk-self-similarity","declaration_gid":"D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Cumulative probabilities are squared norms of projections onto the Laurent windows. Fourth-power decimation and the parity-weighted projection identity make these norms equal at the two scales. Interval differences give the assertion, including the singleton interval at the origin.

## References

- Truth anchor: `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.Tset`
- Truth anchor: `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.claim`
- Truth anchor: `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.prob`
- Truth anchor: `D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result`
- Dependency: [D5/S3/Quantum/Walks/CMV/Representation](CMV/Representation.md)
- Dependency: [D5/S3/Quantum/Walks/Riesz/Decimation](Riesz/Decimation.md)
