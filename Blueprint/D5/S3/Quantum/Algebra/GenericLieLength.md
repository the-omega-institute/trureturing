# GenericLieLength

## Abstract

Generic Lie-length in the traceless skew-Hermitian matrix Lie algebra grows logarithmically for every fixed generator count at least two.

**Definition 1.1 (claim).**

$$\operatorname{claim} \iff (\forall (g : \mathbb{N}) , 2 \leq g \to \exists (c C : \mathbb{R}) , 0 < c \land 0 < C \land \forall (n : \mathbb{N}) , 2 \leq n \to \operatorname{Filter} . \operatorname{Eventually} (\operatorname{fun} (S : \operatorname{Fin} g \to \operatorname{Fin} n \to \operatorname{Fin} n \to \mathbb{C}) \mapsto (c * \operatorname{Real} . \operatorname{log} (n : \mathbb{R}) \leq (\operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) : \mathbb{R}) \land (\operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) : \mathbb{R}) \leq C * \operatorname{Real} . \operatorname{log} (n : \mathbb{R}))) (\operatorname{MeasureTheory} . \operatorname{ae} (\operatorname{suPairMeasure} g n)))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLength.claim` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

Conjecture 6 (arXiv:2301.08241v3, p. 19): “Let S be a random Lie-generating set of su(n), then Lieℓ(S) = Θ(log n) almost surely.” The number g of generators is fixed, with g ≥ 2, and the positive real constants depend on g but not on n ≥ 2. Lie-length counts generator letters in right-nested brackets and cumulative layers. Filter.Eventually under suPairMeasure gives the source almost-sure qualifier.

**Theorem 1.2 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLength.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Acknowledgement.* Seth Lloyd; Reevu Maity (2019). *Efficient implementation of unitary transformations*. DOI: [10.48550/arXiv.1901.03431](https://doi.org/10.48550/arXiv.1901.03431). URL: <https://arxiv.org/abs/1901.03431>.

*Commentary.*

For each fixed g ≥ 2 the constants c = 1/log(g + 1) and C = 32/log 2 work. The anchored heap produces a spanning pair in 16(1 + Nat.log 2 (n − 1)) letters; the determinant argument gives the same bound almost everywhere. The word-count dimension bound gives the lower estimate. The optimal upper constant and Lloyd–Maity Conjecture III remain open.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.result`
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLengthConstruction](GenericLieLengthConstruction.md)
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLengthGenericity](GenericLieLengthGenericity.md)
