# The shuffle chain map and Moore normalization

## Abstract

The shuffle chain map and Moore normalization

Fix an abelian category C : Type u with Category.{v} C and independent universes u,v. Every X is an arbitrary bisimplicial object in C. The complexes FOne and FTwo are the total double alternating-face complex and the diagonal alternating-face complex, respectively, in ChainComplex C ℕ.

The two coordinate maps of a (p,q)-shuffle give simplex maps [p+q] → [p] and [p+q] → [q]. Contravariance realizes their pair as X[p,q] → X[p+q,p+q]. The sum of these maps with integer shuffle signs is ezComponent. Its boundary splits into first-coordinate and second-coordinate insertion terms; the marked diagonal vertices cancel by the sign-reversing involution. Total descent packages the resulting shuffleMap : FOne(X) → FTwo(X).

NOne is the total complex after Moore normalization in both directions, and NTwo is the normalized Moore complex of the diagonal. Each uses the pinned Dold–Kan inclusion and retraction. The normalized shuffle and Alexander–Whitney maps are obtained by inclusion, the corresponding unnormalized map, and retraction. The Moore convention is the intersection of the positive-face kernels, rather than the quotient-by-degeneracies convention of the original product-chain formulation.

**Definition 1.1 (shuffleFstHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleFstHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleFstHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

First projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋p⦌`.

In this notation, def shuffleFstHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋p⦌.

**Definition 1.2 (shuffleSndHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleSndHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleSndHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Second projection of a shuffle as a `SimplexCategory` morphism `⦋p+q⦌ ⟶ ⦋q⦌`.

In this notation, def shuffleSndHom {p q : ℕ} (μ : Shuffle p q) : (⦋p + q⦌ : SimplexCategory) ⟶ ⦋q⦌.

**Definition 1.3 (ezComponent).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The `(p, q)` component of the shuffle map.

In this notation, noncomputable def ezComponent (X : BisimplicialObject C) (p q : ℕ) : (X.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶ (X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌).

**Theorem 1.4 (fstHom_insertLeftStep_comp_δ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_insertLeftStep_comp_δ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_insertLeftStep_comp_δ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Left insertion face factorization (fst component): `δ_{insertLeftIndex} ≫ eqToHom ≫ fstHom(insertLeftStep ν j) = fstHom(ν) ≫ δ(j)`.

In this notation, lemma fstHom_insertLeftStep_comp_δ {p q n : ℕ} (ν : Shuffle p q) (j : Fin (p + 2)) (hn : n + 1 = (p + 1) + q) : SimplexCategory.δ ((ν.insertLeftIndex j).cast (by omega)) ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleFstHom (ν.insertLeftStep j) = eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫ shuffleFstHom ν ≫ SimplexCategory.δ j.

**Theorem 1.5 (sndHom_insertRightStep_comp_δ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_insertRightStep_comp_δ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_insertRightStep_comp_δ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Right insertion face factorization (snd component): `δ_{insertRightIndex} ≫ eqToHom ≫ sndHom(insertRightStep ν k) = sndHom(ν) ≫ δ(k)`.

In this notation, lemma sndHom_insertRightStep_comp_δ {p q n : ℕ} (ν : Shuffle p q) (k : Fin (q + 2)) (hn : n + 1 = p + (q + 1)) : SimplexCategory.δ ((ν.insertRightIndex k).cast (by omega)) ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleSndHom (ν.insertRightStep k) = eqToHom (congrArg SimplexCategory.mk (by omega : n = p + q)) ≫ shuffleSndHom ν ≫ SimplexCategory.δ k.

**Theorem 1.6 (fstHom_swapDiagonalSteps_comp_δ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_swapDiagonalSteps_comp_δ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_swapDiagonalSteps_comp_δ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Composing `δ r ≫ eqToHom ≫ shuffleFstHom` of `swapDiagonalSteps μ` gives the same result as for `μ`, because `δ r` maps via `succAbove r` which avoids vertex `r`, and `swapDiagonalSteps` only changes the value at `r`.

In this notation, lemma fstHom_swapDiagonalSteps_comp_δ {p q n : ℕ} (μ : Shuffle p q) (r : Fin (n + 2)) (hn : n + 1 = p + q) (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) : SimplexCategory.δ r ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleFstHom (μ.swapDiagonalSteps (r.cast (by omega)) h) = SimplexCategory.δ r ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleFstHom μ.

**Theorem 1.7 (sndHom_swapDiagonalSteps_comp_δ).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_swapDiagonalSteps_comp_δ`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_swapDiagonalSteps_comp_δ` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Deleting the marked diagonal vertex makes the second-coordinate simplex maps agree before and after the corner swap.

In this notation, lemma sndHom_swapDiagonalSteps_comp_δ {p q n : ℕ} (μ : Shuffle p q) (r : Fin (n + 2)) (hn : n + 1 = p + q) (h : Shuffle.isDiagonalVertex μ (r.cast (by omega))) : SimplexCategory.δ r ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleSndHom (μ.swapDiagonalSteps (r.cast (by omega)) h) = SimplexCategory.δ r ≫ eqToHom (congrArg SimplexCategory.mk hn) ≫ shuffleSndHom μ.

**Theorem 1.8 (ezComponent_boundary).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent_boundary` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Boundary formula for `ezComponent`. Composing `ezComponent X p q` with the diagonal differential splits into the vertical boundary term coming from the first simplicial direction and the horizontal boundary term coming from the second. The differential is written as `.d` rather than `objD` to avoid index-cast noise.

In this notation, lemma ezComponent_boundary (X : BisimplicialObject C) (p q j : ℕ) (h : (ComplexShape.down ℕ).Rel (p + q) j) : ezComponent X p q ≫ @eqToHom _ _ ((X.obj (Opposite.op ⦋p + q⦌)).obj (Opposite.op ⦋p + q⦌)) (((alternatingFaceMapComplex C).obj (diag.obj X)).X (p + q)) rfl ≫ ((alternatingFaceMapComplex C).obj (diag.obj X)).d (p + q) j = (match p with | 0 => 0 | p' + 1 => ∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) • ((X.map (SimplexCategory.δ k).op).app (Opposite.op ⦋q⦌) ≫ ezComponent X p' q ≫ eqToHom (by have : j + 1 = p' + 1 + q := by rwa [ComplexShape.down_Rel] at h simp [show p' + q = j from by omega]))) + (match q with | 0 => 0 | q' + 1 => (-1 : ℤ) ^ p • ∑ k : Fin (q' + 2), (-1 : ℤ) ^ (k : ℕ) • ((X.obj (Opposite.op ⦋p⦌)).map (SimplexCategory.δ k).op ≫ ezComponent X p q' ≫ eqToHom (by have : j + 1 = p + (q' + 1) := by rwa [ComplexShape.down_Rel] at h simp [show p + q' = j from by omega]))).

**Definition 1.9 (shuffleMap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleMap`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleMap` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The shuffle chain map `FOne(X) ⟶ FTwo(X)`.

In this notation, noncomputable def shuffleMap (X : BisimplicialObject C) : FOne.obj X ⟶ FTwo.obj X.

**Theorem 1.10 (alexanderWhitney_comp_shuffleMap_f).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.alexanderWhitney_comp_shuffleMap_f`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.alexanderWhitney_comp_shuffleMap_f` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Degreewise formula for `alexanderWhitney ≫ shuffleMap`.

In this notation, lemma alexanderWhitney_comp_shuffleMap_f (X : BisimplicialObject C) (q : ℕ) : (alexanderWhitney X ≫ shuffleMap X).f q = ∑ p : Fin (q + 1), eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]) ≫ awComponent X p (q - p) ≫ ezComponent X p (q - p) ≫ eqToHom (by simp [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp p.isLt)]).

**Theorem 1.11 (awShuffle_f_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.awShuffle_f_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.awShuffle_f_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

In degree `0`, the composite `alexanderWhitney ≫ shuffleMap` is the identity.

In this notation, lemma awShuffle_f_zero (X : BisimplicialObject C) : (alexanderWhitney X ≫ shuffleMap X).f 0 = (𝟙 (FTwo.obj X) : (FTwo.obj X) ⟶ (FTwo.obj X)).f 0.

**Definition 1.12 (NOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **bi-normalized total complex**: normalize both simplicial directions (via the normalized Moore complex), then take the total complex. The normalized analogue of `FOne`.

In this notation, noncomputable abbrev NOne : BisimplicialObject C ⥤ ChainComplex C ℕ.

**Definition 1.13 (NTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NTwo`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NTwo` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The **normalized Moore complex of the diagonal**. The normalized analogue of `FTwo`.

In this notation, noncomputable abbrev NTwo : BisimplicialObject C ⥤ ChainComplex C ℕ.

**Definition 1.14 (mooreInclusion).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The Moore inclusion `N[-] ⟶ K[-]` packaged as a natural transformation. Needed to lift the inner-direction normalization through `mapHomologicalComplex`.

In this notation, noncomputable def mooreInclusion : normalizedMooreComplex C ⟶ alternatingFaceMapComplex C.

**Definition 1.15 (mooreRetraction).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreRetraction`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreRetraction` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The Dold–Kan retraction `K[-] ⟶ N[-]` (via `PInfty`) as a natural transformation.

In this notation, noncomputable def mooreRetraction : alternatingFaceMapComplex C ⟶ normalizedMooreComplex C.

**Theorem 1.16 (mooreInclusion_comp_mooreRetraction).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion_comp_mooreRetraction`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion_comp_mooreRetraction` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The Moore inclusion is a section of the Dold–Kan retraction.

In this notation, lemma mooreInclusion_comp_mooreRetraction : mooreInclusion ≫ mooreRetraction = 𝟙 (normalizedMooreComplex C).

**Definition 1.17 (inclusionNOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inclusion `NOne ↪ FOne` of the bi-normalized total complex into the unnormalized total complex, obtained by including both simplicial directions (`inclusionOfMooreComplexMap` outer, `mooreInclusion` inner) and totalizing.

In this notation, noncomputable def inclusionNOne : NOne.obj X ⟶ FOne.obj X.

**Definition 1.18 (retractionNOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Retraction `FOne ↠ NOne` onto the bi-normalized total complex (via `PInfty` in both directions).

In this notation, noncomputable def retractionNOne : FOne.obj X ⟶ NOne.obj X.

**Definition 1.19 (inclusionNTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNTwo`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNTwo` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inclusion `NTwo ↪ FTwo` for the diagonal (the Moore inclusion).

In this notation, noncomputable def inclusionNTwo : NTwo.obj X ⟶ FTwo.obj X.

**Definition 1.20 (retractionNTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNTwo`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNTwo` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Retraction `FTwo ↠ NTwo` for the diagonal (the `PInfty` retraction).

In this notation, noncomputable def retractionNTwo : FTwo.obj X ⟶ NTwo.obj X.

**Definition 1.21 (normalizedShuffleMap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedShuffleMap`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedShuffleMap` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The shuffle map on normalized complexes, `∇ : NOne → NTwo`. Option 3: the unnormalized `shuffleMap` conjugated by the Dold–Kan inclusion `NOne ↪ FOne` and the retraction `FTwo ↠ NTwo`, so it is levelwise-concrete.

In this notation, noncomputable def normalizedShuffleMap : NOne.obj X ⟶ NTwo.obj X.

**Definition 1.22 (normalizedAlexanderWhitney).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedAlexanderWhitney`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedAlexanderWhitney` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The Alexander–Whitney map on normalized complexes, `AW : NTwo → NOne`. Option 3: the unnormalized `alexanderWhitney` conjugated by the Dold–Kan inclusion `NTwo ↪ FTwo` and the retraction `FOne ↠ NOne`, so it is levelwise-concrete.

In this notation, noncomputable def normalizedAlexanderWhitney : NTwo.obj X ⟶ NOne.obj X.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.NTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.alexanderWhitney_comp_shuffleMap_f`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.awShuffle_f_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.ezComponent_boundary`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_insertLeftStep_comp_δ`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.fstHom_swapDiagonalSteps_comp_δ`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.inclusionNTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreInclusion_comp_mooreRetraction`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.mooreRetraction`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedAlexanderWhitney`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.normalizedShuffleMap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.retractionNTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleFstHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleMap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.shuffleSndHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_insertRightStep_comp_δ`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial.sndHom_swapDiagonalSteps_comp_δ`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/AlexanderWhitney](AlexanderWhitney.md)
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleDiagonal](ShuffleDiagonal.md)
