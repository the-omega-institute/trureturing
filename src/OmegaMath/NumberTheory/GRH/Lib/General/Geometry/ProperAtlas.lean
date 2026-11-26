import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Hodge.HodgeSite
import OmegaMath.NumberTheory.GRH.Lib.General.Geometry.ProperSchemes
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: Smooth proper schemes are separated functors with finite étale atlases and affine
covers. -/

open CategoryTheory AlgebraicGeometry Limits PrimeSpectrum Spec pullback Over Category RingHom
  CommAlgCat HasRingHomProperty ULift


variable {k} [CommRing k] {R : CommRingCat} [Algebra R k] {W}

lemma isOpenSub_of_landsIn {Z} (t : ∀ {A}, @PointsIn k _ R _ W A → (Spec ⟨A⟩ ⟶ Z)) (ht : ∀ A B φ x,
  @t B (.map φ x) = specMap φ.hom ≫ @t A x) {V} U (h : ∀ A x, x ∈ U A ↔ LandsIn (t x) V) : IsOpenSub
  U := fun A x ↦ (t x ⁻¹ᵁ V).2.imp' _ fun I e B φ ↦ by erw [h, ht, ← zeroLocus_empty_iff_eq_top,
  zeroLocus_span, ← preimage_comap_zeroLocus, zeroLocus_span, e, compl_eq_bot, eq_top_iff]; rfl

attribute [local simp] map_inj ConcreteCategory.hom_ext_iff landsIn_opensRange
attribute [local simp ←] Spec.map_comp

instance isSepFunctor_algPoints [IsProper W.hom] : IsSepFunctor (algPointsOf k R W) :=
  ⟨fun _ ⟨x⟩ _ ↦ ((isProperOver_pointsToBase
  W.hom).1 _ ⟨x.1⟩ ⟨_⟩).imp fun _ h _ _ ↦ by erw [up_inj, OverMorphism.ext_iff, ← up_inj, h]; rfl⟩

/-- If W is proper over Spec R and its base change to the R-algebra k is smooth of relative
dimension d, then the functor of points of W on k-algebras has an atlas of dimension d. -/
lemma hasAtlas_algPoints d [IsProper W.hom] [h : SmoothOfRelativeDimension d (snd
    W.hom (specMap (algebraMap R k)))] : HasAtlas d (algPointsOf k R W) := by
  choose t u v using fun {A} (x : PointsIn W A) ↦ exists_lift _ _ _ (specOver k A).hom
    (x.1.w.trans (map_comp ..))
  have m A B φ x : @t B (x.map φ) = specMap φ.hom ≫ @t A x := by aesop
  choose V hV a h using fun z ↦ show ∃ V, z ∈ V ∧ ∃ a, ∀ A x, x ∈ EtaleChart.locus a A ↔
    LandsIn (t x) V by
    choose U hU V hV hz e H using h.1 z
    choose ρ hρ using map_surjective hU.fromSpec
    let := (ρ ≫ Scheme.Hom.appLE _ U V e).hom.toAlgebra
    choose g H using (H.comp (etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (Spec_iff.1
      (hρ ▸ inferInstance : Etale (map ρ))))).toAlgebra.exists_etale_mvPolynomial
    have E := by simpa [← hρ] using hU.SpecMap_appLE_fromSpec _ hV e
    have ⟨y, hy⟩ : ∃ y, @t (.of ..) y = hV.fromSpec := ⟨⟨homMk _ (by
      erw [assoc, condition, ← reassoc_of% E, ← map_comp]; rfl)⟩, hom_ext (u _) ((v _).trans E)⟩
    refine ⟨_, hV.opensRange_fromSpec.ge hz, ⟨_, y, _, MvPolynomial.aeval_unique g ▸ H, fun A φ ψ ↦
      (by simpa [m, hy, cancel_mono] using congrArg t ·), isOpenSub_of_landsIn t m _ ?q⟩, ?q⟩
    simpa -proj [← hy] using fun A x ↦ ⟨fun ⟨φ, e⟩ ↦ e ▸ ⟨_, (m ..).symm⟩, fun ⟨φ, e⟩ ↦ ⟨⟨ofHom
      ⟨_, by simpa [v] using e =≫ snd ..⟩⟩, up_inj.2 (OverMorphism.ext (by erw [← u, m, e, u]))⟩⟩
  exact (finite_cover_nhds ((V _).2.mem_nhds <| hV ·)).elim fun T e ↦ ⟨_,
    (a <| T.equivFin.symm ·), fun K k x ↦ let := k.toField
    by simpa [T.equivFin.surjective.exists, ↓h, landsIn_iff_mem] using e.ge ⟨⟩⟩

/-- If every ring ι(c) satisfies `IsComparableRing`, the points of a proper R-scheme W on these
rings are the restriction of a separated functor onto which the points of one affine scheme
surject at every ι(c) (`IsAffinelyCovered`). -/
lemma isAffinelyCovered_algPoints {C} [Category C] {ι : C ⥤ CommAlg k} (h : ∀ c,
  IsComparableRing (@id (ι c))) W [IsProper W.hom] : IsAffinelyCovered ι (algPointsOf k R W) :=
  (exists_finiteType_atlas (snd ..)).elim
  fun T ⟨t, _, H⟩ ↦ (map_surjective (t ≫ snd ..)).elim fun ρ E ↦ let := ρ.hom.toAlgebra
  ⟨isSepFunctor_algPoints, _,
    ⟨homMk _ (by erw [assoc, condition, ← reassoc_of% E, ← map_comp]; rfl)⟩,
    fun c x ↦ (H _ (h c) (lift _ _ (x.1.w.trans (map_comp (CommRingCat.ofHom _) _)))).elim fun u e ↦
    ⟨⟨ofHom ⟨u.1, by simpa [← E] using! (e =≫ _).trans (lift_snd ..)⟩⟩,
    by exact congr(⟨$(OverMorphism.ext ((e =≫ _).trans (lift_fst ..)))⟩)⟩⟩
