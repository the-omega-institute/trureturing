# Normalization of total complexes

## Abstract

Normalization of total complexes

Let C : Type u have Category.{v} C and Abelian C, with independent universes, and let X be bisimplicial. MOne(X) denotes the total complex with outer alternating faces and inner Moore normalization. The comparison factors as NOne(X) ≃ MOne(X) ≃ FOne(X), using the ordinary Dold–Kan normalization homotopy in each direction.

The outer homotopy-lifting construction is more general: I₁,I₂,J are arbitrary index types with shapes c₁,c₂,c, DecidableEq J and TotalComplexShape c₁ c₂ c. K,L are double complexes in C with HasTotal c, and φ,ψ : K → L. A Homotopy φ ψ in the first complex direction gives totalMapHomotopy. Its summand signs are the native ε₁ signs, and the homotopy vanishes away from c.Rel j′ j. The inner-direction version uses the corresponding homotopy in HomologicalComplex C c₁ and flips the double complexes.

The native totalFlipIso multiplies a natural-number bidegree (p,q) summand by (-1)^(p*q). Its naturality identifies the actual total map with the conjugate of the flipped total map. This transfers the inner normalization homotopy without altering either differential sign. The category and normalization suppliers are the pinned implementations.

**Definition 1.1 (MOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.MOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.MOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The intermediate total complex: outer unnormalized and inner normalized.

In this notation, noncomputable abbrev MOne (X : BisimplicialObject C) : ChainComplex C ℕ.

**Definition 1.2 (inclusionMOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The outer normalization inclusion `NOne(X) ⟶ MOne(X)`.

In this notation, noncomputable def inclusionMOne : NOne.obj X ⟶ MOne X.

**Definition 1.3 (retractionMOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionMOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionMOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The outer normalization retraction `MOne(X) ⟶ NOne(X)`.

In this notation, noncomputable def retractionMOne : MOne X ⟶ NOne.obj X.

**Definition 1.4 (inclusionFOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inner normalization inclusion `MOne(X) ⟶ FOne(X)`.

In this notation, noncomputable def inclusionFOne : MOne X ⟶ FOne.obj X.

**Definition 1.5 (retractionFOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOne`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOne` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inner normalization retraction `FOne(X) ⟶ MOne(X)`.

In this notation, noncomputable def retractionFOne : FOne.obj X ⟶ MOne X.

**Theorem 1.6 (inclusionMOne_comp_retractionMOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne_comp_retractionMOne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne_comp_retractionMOne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Outer Moore inclusion followed by outer Moore retraction is the identity on the twice-normalized total.

In this notation, @[reassoc] lemma inclusionMOne_comp_retractionMOne : inclusionMOne X ≫ retractionMOne X = 𝟙 (NOne.obj X).

**Theorem 1.7 (inclusionFOne_comp_retractionFOne).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne_comp_retractionFOne`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne_comp_retractionFOne` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Inner Moore inclusion followed by inner Moore retraction is the identity on the intermediate total.

In this notation, @[reassoc] lemma inclusionFOne_comp_retractionFOne : inclusionFOne X ≫ retractionFOne X = 𝟙 (MOne X).

**Definition 1.8 (totalMapHomotopyHom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyHom`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyHom` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The components `(K.total c).X j ⟶ (L.total c).X j'` of the homotopy on total complexes induced by a homotopy `h` between maps of bicomplexes that is homotopic in the first direction.

In this notation, noncomputable def totalMapHomotopyHom (h : Homotopy φ ψ) (j j' : J) : (K.total c).X j ⟶ (L.total c).X j'.

**Theorem 1.9 (totalMapHomotopy_zero).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_zero` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The total homotopy component vanishes when the target and source degrees do not satisfy the reversed differential relation.

In this notation, lemma totalMapHomotopy_zero (h : Homotopy φ ψ) (j j' : J) (hj : ¬ c.Rel j' j) : totalMapHomotopyHom (c := c) h j j' = 0.

**Theorem 1.10 (totalMapHomotopy_comm).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_comm`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_comm` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The totalized source map is dNext plus prevD of the constructed family plus the totalized target map.

In this notation, lemma totalMapHomotopy_comm (h : Homotopy φ ψ) (j : J) : (HomologicalComplex₂.total.map φ c).f j = dNext j (totalMapHomotopyHom h) + prevD j (totalMapHomotopyHom h) + (HomologicalComplex₂.total.map ψ c).f j.

**Definition 1.11 (totalMapHomotopy).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A homotopy of bicomplex morphisms in the outer direction induces a homotopy on total complexes.

In this notation, noncomputable def totalMapHomotopy (h : Homotopy φ ψ) : Homotopy (HomologicalComplex₂.total.map φ c) (HomologicalComplex₂.total.map ψ c).

**Definition 1.12 (flipMap).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMap`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMap` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The flip of a bicomplex morphism, as a morphism between the flipped bicomplexes.

In this notation, def flipMap (φ : K ⟶ L) : K.flip ⟶ L.flip.

**Theorem 1.13 (totalFlipIso_hom_naturality).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalFlipIso_hom_naturality`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalFlipIso_hom_naturality` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Naturality of the flip symmetry isomorphism `totalFlipIso` with respect to a bicomplex morphism `φ : K ⟶ L`: the totalization of `φ` and of its flip are related by conjugation.

In this notation, @[reassoc] lemma totalFlipIso_hom_naturality (φ : K ⟶ L) : (K.totalFlipIso c).hom ≫ HomologicalComplex₂.total.map φ c = HomologicalComplex₂.total.map (flipMap φ) c ≫ (L.totalFlipIso c).hom.

**Theorem 1.14 (total_map_eq_flipConjugate).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.total_map_eq_flipConjugate`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.total_map_eq_flipConjugate` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The totalization of a bicomplex morphism is conjugate to the totalization of its flip by `totalFlipIso`.

In this notation, lemma total_map_eq_flipConjugate (φ : K ⟶ L) : HomologicalComplex₂.total.map φ c = (K.totalFlipIso c).inv ≫ HomologicalComplex₂.total.map (flipMap φ) c ≫ (L.totalFlipIso c).hom.

**Definition 1.15 (totalMapHomotopyTwo).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyTwo`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyTwo` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inner-direction analog of `totalMapHomotopy`. It is obtained by applying `totalMapHomotopy` to the flipped bicomplex and transporting the result across `totalFlipIso`.

In this notation, noncomputable def totalMapHomotopyTwo {φ ψ : K ⟶ L} (h : Homotopy (flipMap φ) (flipMap ψ)) : Homotopy (HomologicalComplex₂.total.map φ c) (HomologicalComplex₂.total.map ψ c).

**Definition 1.16 (outerNormalizationComparisonPreTotal).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparisonPreTotal`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparisonPreTotal` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The outer Dold-Kan homotopy equivalence before totalization.

In this notation, noncomputable def outerNormalizationComparisonPreTotal : HomotopyEquiv (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj ((normalizedMooreComplex (SimplicialObject C)).obj X)) (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj ((alternatingFaceMapComplex (SimplicialObject C)).obj X)).

**Definition 1.17 (outerNormalizationComparison).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparison`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparison` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The outer half of `normalizationComparison`.

In this notation, noncomputable def outerNormalizationComparison : HomotopyEquiv (NOne.obj X) (MOne X).

**Definition 1.18 (flipMapHomologicalComplexHomotopy).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMapHomologicalComplexHomotopy`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMapHomologicalComplexHomotopy` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

A natural family of homotopies between chain-complex-valued functors lifts, after `flip`, to a homotopy between the corresponding `mapHomologicalComplex` morphisms.

In this notation, noncomputable def flipMapHomologicalComplexHomotopy {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜] {F G : 𝒜 ⥤ ChainComplex C ℕ} [F.Additive] [G.Additive] {α β : F ⟶ G} (h : ∀ Y, Homotopy (α.app Y) (β.app Y)) (hnat : ∀ {Y Z : 𝒜} (f : Y ⟶ Z) (i j : ℕ), (F.map f).f i ≫ (h Z).hom i j = (h Y).hom i j ≫ (G.map f).f j) (W : HomologicalComplex 𝒜 (ComplexShape.down ℕ)) : Homotopy (HomologicalComplex₂.flipMap ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app W)) (HomologicalComplex₂.flipMap ((NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app W)).

**Theorem 1.19 (alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Naturality of the homotopy operator in `homotopyPToId`.

In this notation, lemma alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom {Y Z : SimplicialObject C} (f : Y ⟶ Z) (q i j : ℕ) : ((alternatingFaceMapComplex C).map f).f i ≫ (homotopyPToId Z q).hom i j = (homotopyPToId Y q).hom i j ≫ ((alternatingFaceMapComplex C).map f).f j.

**Theorem 1.20 (homotopyInvHomId_hom_naturality).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.homotopyInvHomId_hom_naturality`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.homotopyInvHomId_hom_naturality` (`✓ std3`). ∎

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

Naturality, in the simplicial object, of the Dold–Kan contraction homotopy operator for `PInfty ≃ 𝟙` (i.e. `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId`). This is the `hnat` input to `flipMapHomologicalComplexHomotopy` for the inner normalization comparison.

In this notation, lemma homotopyInvHomId_hom_naturality {Y Z : SimplicialObject C} (f : Y ⟶ Z) (i j : ℕ) : ((alternatingFaceMapComplex C).map f).f i ≫ (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (A := C) (Y := Z)).homotopyInvHomId.hom i j = (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (A := C) (Y := Y)).homotopyInvHomId.hom i j ≫ ((alternatingFaceMapComplex C).map f).f j.

**Definition 1.21 (retractionFOneInclusionFOneFlipHomotopy).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOneInclusionFOneFlipHomotopy`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOneInclusionFOneFlipHomotopy` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The flipped inner Dold-Kan homotopy used in `innerNormalizationComparison`.

In this notation, noncomputable def retractionFOneInclusionFOneFlipHomotopy : Homotopy (HomologicalComplex₂.flipMap ((NatTrans.mapHomologicalComplex mooreRetraction _).app ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫ (NatTrans.mapHomologicalComplex mooreInclusion _).app ((alternatingFaceMapComplex (SimplicialObject C)).obj X))) (HomologicalComplex₂.flipMap (𝟙 (((alternatingFaceMapComplex C).mapHomologicalComplex _).obj ((alternatingFaceMapComplex (SimplicialObject C)).obj X)))).

**Definition 1.22 (innerNormalizationComparison).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.innerNormalizationComparison`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.innerNormalizationComparison` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The inner half of `normalizationComparison`.

In this notation, noncomputable def innerNormalizationComparison : HomotopyEquiv (MOne X) (FOne.obj X).

**Definition 1.23 (normalizationComparison).**

Lean statement: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.normalizationComparison`

*Formalization.* `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.normalizationComparison` (`✓ std3`).

*Citation.* Jeffrey Li (2026). *Bisimplicial Eilenberg–Zilber equivalence and recursive normalized homotopy*. URL: <https://github.com/LeanPool/lean-pool/tree/8bbde3a6de815108d41922c9362ebbe38422663a/LeanPool/EilenbergZilber>.

*Commentary.*

The full comparison between the normalized and unnormalized total complexes.

In this notation, noncomputable def normalizationComparison : HomotopyEquiv (NOne.obj X) (FOne.obj X).

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.MOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMap`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.flipMapHomologicalComplexHomotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.homotopyInvHomId_hom_naturality`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionFOne_comp_retractionFOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.inclusionMOne_comp_retractionMOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.innerNormalizationComparison`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.normalizationComparison`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparison`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.outerNormalizationComparisonPreTotal`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionFOneInclusionFOneFlipHomotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.retractionMOne`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalFlipIso_hom_naturality`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyHom`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopyTwo`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_comm`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.totalMapHomotopy_zero`
- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/NormalizationComparison.total_map_eq_flipConjugate`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/Bisimplicial](Bisimplicial.md)
- Dependency: [D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison](../../Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.md)
