# Complete mappings of Brauer and partial Brauer monoids

## Abstract

Brauer and partial Brauer monoids admit complete mappings exactly in degree one and degrees at least four.

**Definition 1.1 (The whole-monoid existence question).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), (1 \leq n) \Rightarrow ((\exists (: \operatorname{BrauerSourceMonoid}\left(n\right)), \operatorname{True}) \land ((\exists (: \operatorname{PartialBrauerSourceMonoid}\left(n\right)), \operatorname{True}) \land ((\forall (B : \operatorname{BrauerSourceMonoid}\left(n\right)), (\exists \alpha : (\operatorname{Brauer}\left(n\right) \to \operatorname{Brauer}\left(n\right)), \operatorname{CompleteMapping}\left(\operatorname{Brauer}\left(n\right), B.\operatorname{algebra}.\operatorname{toSemigroup}, \alpha\right)) \Leftrightarrow (n = 1 \lor 4 \leq n)) \land (\forall (PB : \operatorname{PartialBrauerSourceMonoid}\left(n\right)), (\exists \alpha : (\operatorname{PartialBrauer}\left(n\right) \to \operatorname{PartialBrauer}\left(n\right)), \operatorname{CompleteMapping}\left(\operatorname{PartialBrauer}\left(n\right), PB.\operatorname{algebra}.\operatorname{toSemigroup}, \alpha\right)) \Leftrightarrow (n = 1 \lor 4 \leq n))))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.claim` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

Problem 15.11, printed page 61: "Classify complete mappings for $\mathcal{B}_{n}$ and $\mathcal{PB}_{n}$. In view of the Hall--Paige theorem, the unresolved proper factors are those of ranks $2$ and $3$ which occur in the corresponding monoid. Determine also for which values of $n$ the whole monoid has a complete mapping." The question asks for the degrees; the numerical classification is the answer proved below. The two existence clauses construct monoid structures with the exterior-connectivity product. The remaining clauses quantify over every such structure. Labels in Fin n represent the paper's labels shifted by one; false and true identify its unprimed and primed rows. CompleteMapping is applied with its carrier and semigroup structure displayed explicitly.

**Theorem 1.2 (The existence classification).**

$$\forall (n : \mathbb{N}), (1 \leq n) \Rightarrow ((\exists (: \operatorname{BrauerSourceMonoid}\left(n\right)), \operatorname{True}) \land ((\exists (: \operatorname{PartialBrauerSourceMonoid}\left(n\right)), \operatorname{True}) \land ((\forall (B : \operatorname{BrauerSourceMonoid}\left(n\right)), (\exists \alpha : (\operatorname{Brauer}\left(n\right) \to \operatorname{Brauer}\left(n\right)), \operatorname{CompleteMapping}\left(\operatorname{Brauer}\left(n\right), B.\operatorname{algebra}.\operatorname{toSemigroup}, \alpha\right)) \Leftrightarrow (n = 1 \lor 4 \leq n)) \land (\forall (PB : \operatorname{PartialBrauerSourceMonoid}\left(n\right)), (\exists \alpha : (\operatorname{PartialBrauer}\left(n\right) \to \operatorname{PartialBrauer}\left(n\right)), \operatorname{CompleteMapping}\left(\operatorname{PartialBrauer}\left(n\right), PB.\operatorname{algebra}.\operatorname{toSemigroup}, \alpha\right)) \Leftrightarrow (n = 1 \lor 4 \leq n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result` (`✓ std3`). ∎

*Resolves.* `Problems/araujo-brauer-complete-mapping` (proved) by `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"araujo-brauer-complete-mapping","declaration_gid":"D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

Rank fibres are assembled from transversals. The exceptional rank-two and rank-three Brauer factors use supported cycles with one triangle of negative transport sign. Partial Brauer factors in these ranks have even index. Unit groups exclude degrees two and three, and identity maps supply degree one.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.claim`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result`
- Dependency: [D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation](../../../S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.md)
- Dependency: [D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings](../../../S0/Certificates/Groups/AraujoSymmetricCompleteMappings.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates](AraujoBrauerCoordinates.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles](AraujoBrauerHalfTriangles.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport](AraujoBrauerOverlayTransport.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting](AraujoSignedFactorLifting.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
