# Bidirectional Prime-Box Horizon

## Abstract

Ordered mixed-register words have a shared-state semantics and an exact product profile.

A command specifies a register and either multiplication or exact division. The initial state is one capacity-bounded exponent tuple. Commands retain their order within each register, while different registers act independently.

**Theorem 1.1 (Exact cardinality at every capacity vector and every horizon).**

$$\forall I: Type, (\operatorname{DecidableEq}(I) \land \operatorname{Fintype}(I)) \Rightarrow \forall a: I \to \mathbb{N}, \forall H \in \mathbb{N}, \operatorname{Surjective}(\operatorname{boxCode}(a, H)) \land (\forall q, r: \operatorname{Option}(\prod_{i \in I} \operatorname{Fin}(\operatorname{a}(i) + 1)), (\forall w: \operatorname{List}(I \times Bool), \operatorname{length}(w) \leq H \Rightarrow (\operatorname{allowed}(a, q, w) \iff \operatorname{allowed}(a, r, w))) \iff \operatorname{boxCode}(a, H, q) = \operatorname{boxCode}(a, H, r)) \land \operatorname{card}(\operatorname{Option}(\operatorname{Profile}(a, H))) = 1 + \prod_{i \in I} (\operatorname{min}(\operatorname{a}(i), 2 \times H) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon.mixed_word_profile_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting a mixed word onto one register never increases its length. Conversely, every single-register word can be lifted to a mixed word using that register alone. These two constructions prove the exact product response kernel. Coordinate-wise surjectivity realizes every claimed profile, and finite product cardinality gives the displayed count including rejection.

For the original capacities (4,2,1,1), counts are 2,37,61 at horizons 0,1,2. The target remains guard legality. The number of full live states has not fallen from 60; the availability of division shortens distinguishing experiments. Invalid attempts are observed as failure, not silently removed from the domain. No sparse base-4 DFAO conjecture is claimed solved.

## References

- Truth anchor: `D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon.mixed_word_profile_classification`
- Dependency: [D5/S3/Factorization/Automata/BoundedPrimeHorizon](BoundedPrimeHorizon.md)
- Dependency: [D5/S3/Factorization/Automata/PrimeCapacityHorizon](PrimeCapacityHorizon.md)
