# The full bisimplicial Eilenberg–Zilber equivalence

## Abstract

The full bisimplicial Eilenberg–Zilber equivalence

For every pair of independent universe levels u,v, every C : Type u with Category.{v} C and Abelian C, and every X : SimplicialObject (SimplicialObject C), the total double alternating-face complex FOne(X) is chain homotopy equivalent to the diagonal alternating-face complex FTwo(X) in ChainComplex C ℕ. The total in degree n uses the finite coproduct over p+q=n and differential d₁+(-1)^p d₂.

On Moore-normalized complexes the shuffle map NOne(X) → NTwo(X), followed by the Alexander–Whitney map NTwo(X) → NOne(X), is strictly the identity. For the matching bidegree, only the staircase shuffle survives normalization; the other shuffle terms are degenerate. For a different split, one of the two simplex maps drops dimension and is killed by Moore retraction. The other composite is homotopic to the identity through the recursive Eilenberg–Mac Lane family described in NormalizedHomotopy.

Write A=normalizationComparison X : NOne(X) ≃ FOne(X) and B=diagonalNormalizationComparison X : NTwo(X) ≃ FTwo(X). The final forward map is A.inv followed by normalizedShuffleMap X followed by B.hom. Its inverse is B.inv followed by normalizedAlexanderWhitney X followed by A.hom. Both homotopies are transported by HomotopyEquiv.trans from these same comparisons and the normalized equivalence. The all-degree recursive homotopy remains the diagonal-side homotopy of the normalized equivalence.

Dold–Puppe, Theorems 2.9 and 2.15, supply the additive total/diagonal statement and identify the shuffle and Alexander–Whitney maps. The present software assumes Abelian C. Eilenberg–Mac Lane II, Theorem 2.1a, uses normalized product/tensor quotient chains; the present abstract software uses Moore kernels. These conventions are not identified here by an extra comparison theorem. No naturality theorem, monoidal coherence, side-condition identities, tensor-product hypothesis or unbounded-integer totalization is asserted.

**Theorem 1.1 (inclusionNOne_comp_retractionNOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_comp_retractionNOne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_comp_retractionNOne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**Glue (split mono, lifted to the total complex).** The bi-normalized inclusion is a section of the retraction. This lifts the Mathlib split-mono identity `(splitMonoInclusionOfMooreComplexMap _).id` through `totalFunctor` in both simplicial directions. (Reused by `normalizationComparison`.)

In this notation, @[reassoc] lemma inclusionNOne_comp_retractionNOne (X : BisimplicialObject C) : inclusionNOne X ≫ retractionNOne X = 𝟙 (NOne.obj X).

**Theorem 1.2 (inclusionNOne_shuffleMap_diag_normalize).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_shuffleMap_diag_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_shuffleMap_diag_normalize` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**(B) `∇` preserves normalization** (EM Lemma I.5.3). Precomposed with the bi-normalized inclusion, the shuffle map already lands in the normalized diagonal, so the diagonal renormalization round-trip `retractionNTwo ≫ inclusionNTwo` (which equals `PInfty`) is a no-op. `@[reassoc]` so it rewrites underneath the trailing `alexanderWhitney ≫ retractionNOne`.

In this notation, @[reassoc] lemma inclusionNOne_shuffleMap_diag_normalize (X : BisimplicialObject C) : inclusionNOne X ≫ shuffleMap X ≫ retractionNTwo X ≫ inclusionNTwo X = inclusionNOne X ≫ shuffleMap X.

**Theorem 1.3 (ezComponent_awComponent_comp_retraction).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.ezComponent_awComponent_comp_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.ezComponent_awComponent_comp_retraction` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**A-diag: the diagonal Eilenberg–MacLane identity.** On the diagonal `(p,q) = (r,m)` the shuffle/Alexander–Whitney pairing `ezComponent ≫ awComponent` is the identity *plus* degenerate cross-terms; the bi-normalized retraction component `R'` (the Dold–Kan `PInfty` projection in both simplicial directions, taken at bidegree `(r,m)`) annihilates the degenerate part, so `ez ≫ aw ≫ R' = R'`. Non-staircase summands vanish via `ezawSummand_merge`, the combinatorial non-mono front face, and the outer kill lemma. This is the combinatorial heart of `(A)`.

In this notation, lemma ezComponent_awComponent_comp_retraction (X : BisimplicialObject C) (r m : ℕ) : X.ezComponent r m ≫ X.awComponent r m ≫ (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫ ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map (PInftyToNormalizedMooreComplex X)).f r).f m = (((NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫ ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map (PInftyToNormalizedMooreComplex X)).f r).f m.

**Theorem 1.4 (shuffleMap_alexanderWhitney_comp_retractionNOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.shuffleMap_alexanderWhitney_comp_retractionNOne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.shuffleMap_alexanderWhitney_comp_retractionNOne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**(A) EM `f∇ = i` modulo norms.** Unnormalized, `shuffleMap ≫ alexanderWhitney = 𝟙 + D` with `D` landing in the degenerate subcomplex; the bi-normalized retraction `retractionNOne` annihilates `D`, leaving `retractionNOne`. The combinatorial core is the shuffle pairing `ezComponent ≫ awComponent` (diagonal `(r,s) = (p,q)` ↦ identity; off-diagonal ↦ degenerate).

In this notation, lemma shuffleMap_alexanderWhitney_comp_retractionNOne (X : BisimplicialObject C) : shuffleMap X ≫ alexanderWhitney X ≫ retractionNOne X = retractionNOne X.

**Theorem 1.5 (normalizedShuffle_alexanderWhitney).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.normalizedShuffle_alexanderWhitney`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.normalizedShuffle_alexanderWhitney` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**EM Thm 2.1a, first half (`f∇ = i`).** On normalized complexes the composite `∇ ≫ AW` is the identity *strictly* — the degenerate cross-terms that obstruct this on the unnormalized complex vanish modulo norms.

In this notation, lemma normalizedShuffle_alexanderWhitney (X : BisimplicialObject C) : normalizedShuffleMap X ≫ normalizedAlexanderWhitney X = 𝟙 (NOne.obj X).

**Definition 1.6 (eilenbergZilberNormalized).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.eilenbergZilberNormalized`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.eilenbergZilberNormalized` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

**Eilenberg–Zilber theorem on normalized complexes** (Eilenberg–Mac Lane II, Thm 2.1a). The bi-normalized total complex is homotopy equivalent to the normalized Moore complex of the diagonal. One direction is a strict identity; the other uses the EM homotopy.

In this notation, noncomputable def eilenbergZilberNormalized (X : BisimplicialObject C) : HomotopyEquiv (NOne.obj X) (NTwo.obj X).

**Definition 1.7 (diagonalNormalizationComparison).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.diagonalNormalizationComparison`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.diagonalNormalizationComparison` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The normalization comparison on the diagonal simplicial object.

In this notation, noncomputable abbrev diagonalNormalizationComparison (X : BisimplicialObject C) : HomotopyEquiv (NTwo.obj X) (FTwo.obj X).

**Definition 1.8 (eilenbergZilber).**

$$\forall u: UniverseLevel, \forall v: UniverseLevel, \forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{Abelian}\left(C\right)] \forall X: \operatorname{BisimplicialObject}\left(C\right), \operatorname{HomotopyEquiv}\left(\operatorname{FOne}\left(X\right), \operatorname{FTwo}\left(X\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.eilenbergZilber` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The unnormalized Eilenberg–Zilber homotopy equivalence `FOne(X) ≃ FTwo(X)`, obtained by transporting the normalized equivalence `eilenbergZilberNormalized` across the normalization comparisons: `FOne(X) ≃ NOne(X) ≃ NTwo(X) ≃ FTwo(X)`, where `normalizationComparison` is the inner/outer Moore normalization of the total complex (`NormalizationComparison`), and `diagonalNormalizationComparison` is the corresponding comparison for the diagonal simplicial object.

In this notation, noncomputable def eilenbergZilber (X : BisimplicialObject C) : HomotopyEquiv (FOne.obj X) (FTwo.obj X).

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.diagonalNormalizationComparison`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.eilenbergZilber`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.eilenbergZilberNormalized`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.ezComponent_awComponent_comp_retraction`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_comp_retractionNOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.inclusionNOne_shuffleMap_diag_normalize`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.normalizedShuffle_alexanderWhitney`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized.shuffleMap_alexanderWhitney_comp_retractionNOne`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial](Bisimplicial.md)
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison](NormalizationComparison.md)
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizedHomotopy](NormalizedHomotopy.md)
