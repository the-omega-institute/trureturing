import OmegaMath.NumberTheory.GRH.Lib.Cohomology.ProperBaseChange.ValuativeDensity
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Proper functors: fibre products, base change, dense images, cover by the space of
places. -/

namespace IsProperOver

open CategoryTheory CartesianMonoidalCategory CommRingCat Functor ResiduePlace Pi Limits
variable {Y Z D T s Λ c} (h : @IsProperOver Z D s)
include h

lemma isRelAffine_pointMap y : @IsRelAffine (reprBy T) Z (pointMap y) :=
  .of_diag (F := uliftCoyoneda) ((isRelAffine_of_zero_unit_locus fun _ ↦
  (h.1 ..).imp' _ fun _ H ↦ ⟨∅, fun _ _ ↦ (Set.ext_iff.1 Set.range_diag _).trans (by
    simpa using! H ..)⟩).baseChange (v := Subfunctor.toRange (lift (𝟙 _) (𝟙 _))) (u :=
  (tensorLeftIsoProd Z).inv Z) (.of_horiz_isIso ⟨(Iso.eq_comp_inv _).2 (prod.comp_lift ..)⟩)) _

/-- Let Z be a functor proper over D, W proper over T, Y → W with Y proper over T, and Z → W
compatible with a ring map ψ: T → D. Then the fibre product V = Z ×_W Y is proper over D. -/
lemma of_isPullback {V W b v q p u} (hb : @IsProperOver W T b) (H : @IsPullback _ _ V Z Y W q v u p)
  (ht : IsProperOver (p ≫ b)) ψ (w : u ≫ b = s ≫ reprMap ψ) : IsProperOver (q ≫ s) := by
  obtain ⟨⟨e, H⟩, ⟨S, _, a, A⟩, R, _, c, B⟩ := isPullback_iff.1 H, h, ht
  have i C x y : x = y ↔ _ := ⟨by lia, ((H C _ _ (e ..)).unique · ⟨rfl, rfl⟩)⟩
  have ⟨_, ⟨g⟩, G⟩ := hb.isRelAffine_pointMap (u _ a) (pointMap (p _ c))
  have ⟨⟨φ⟩, k, G⟩ := (uliftCoyonedaEquiv.exists_congr_left.1 G).imp fun _ ↦ isPullback_iff.1
  have ⟨x, _⟩ := H _ (Y.map g c) (Z.map φ a) (by simpa using! k _ ⟨𝟙 _⟩)
  exact ⟨fun C x y ↦ (S C (q _ x) (q _ y)).elim fun I _ ↦ (R C (v _ x) (v _ y)).imp' (· ⊔ I)
    (by simp_all), _, x, fun O z i ↦ (A O (q _ z) i).elim fun f m ↦ (B O (v _ z)
    (congr(baseRingMap b $(e ..) ·) ▸ congr(baseRingMap $w _) ▸ i _)).elim fun l n ↦
    (G _ _ _ (hb.injective_map_valuationSubring O (by
    simpa [← m, ← n] using! e _ z))).imp' (·.1) (by rintro ⟨⟩ ⟨⟨⟨⟩, ⟨⟩⟩⟩; simp_all -dsimp)⟩

/-- Properness is stable under base change: if Z is proper over D via s: Z → h_D and φ: D → T is
a ring homomorphism, then Z ×_{h_D} h_T is proper over T via its second projection to h_T. -/
lemma baseChange φ : IsProperOver (fibreProd.snd s (@reprMap _ _ D T φ)) := (fun p : ∀ {D},
  IsProperOver (𝟙 (reprBy D)) ↦ p.of_isPullback p isPullback_fibreProd h φ rfl) ⟨fun _ x y ↦
  ⟨⨆ d, .span {x.1.hom d - y.1.hom d}, fun _ _ ↦ ULift.up_inj.trans (by
  simp [ConcreteCategory.hom_ext_iff])⟩, _, ⟨𝟙 _⟩, fun O ↦ (⟨ofHom <| ·.1.1.codRestrict O ·, rfl⟩)⟩

/-- Let c: Y → Z be a map over D with Y and Z both proper in the sense of `IsProperOver`. If c
is onto on points in every algebraically closed field, its image is dense for coefficients
in locally constant Λ-valued functions. -/
lemma hasCohomDenseImage_of_surjective (h' : @IsProperOver Y D (c ≫ s)) (H : ∀ k [Field k]
  [IsAlgClosed k], (⇑(c ⟨k⟩)).Surjective) : HasCohomDenseImage Λ c := h'.2.elim fun _ ⟨a, ha⟩ ↦
  .mono ((h.isRelAffine_pointMap _).hasCohomDenseImage_of_lifts fun O y ↦ (H ..).elim fun x e ↦
  (ha O x (congr(baseRingMap s $e ·) ▸ by simp)).imp' _ fun _ _ ↦ h.injective_map_valuationSubring O
  (.trans (by aesop) e)) fun _ _ ⟨u, e⟩ ↦ e ▸ ⟨_, c.naturality_apply _ a⟩

/-- For Z proper over D there are a ring P of dimension ≤ 0 with algebraically closed residue
fields, ξ ∈ Z(P), and z ∈ Z(T), T = `ResiduePlace.prodValRing`, agreeing with ξ over ∏ κ(q), whose
space of places `ResiduePlace.placeSpace` has dense image in Z for Λ. -/
lemma exists_placeSpace_cover : ∃ P ξ z, HasCohomDenseImage Λ (@placeSpaceMap Z D P s ξ z) := by
  obtain ⟨T, a, ha⟩ := h.2
  let K (j : PrimeSpectrum T) := AlgebraicClosure j.1.ResidueField
  have (q) i := (@IsTest.exists_valuationSubring_atPrime (∀ j, K j) _ .pi q i).1
  refine (Classical.skolem.1 fun j ↦ ha (valSubring j) (Z.map (ofHom (algebraMap ..)) a)
    (by simpa using! j.base_mem)).elim fun u e ↦ ⟨⟨∀ j, K j⟩, Z.map (ofHom (algebraMap ..)) a,
    ⟨Z.map (ofHom (.pi (u · |>.1))) a, ?z, h, (⟨·⁻¹, by aesop⟩), inferInstance⟩,
    h.hasCohomDenseImage_of_surjective isProperOver_placeSpace fun L _ _ y ↦ ?_⟩
  exact h.ext_of_jointly_injective (ofHom <|
    evalRingHom _ ·) (by bound) (by simpa only [← map_comp_apply])
  choose u r using ha ⊤ y (by simp)
  choose q l e using exists_factor_residueField (u ≫ ofHom (ValuationSubring.subtype _))
  algebraize [l.1]
  let k : K q →ₐ[_] L := IsAlgClosed.lift (R := q.1.ResidueField)
  exact (exists_factor_residueField (ofHom (k.1.comp (evalRingHom ..)))).elim fun p ⟨m, i⟩ ↦ ⟨⟨⟦_⟧⟩,
    (map_comp_apply ..).trans
    (congr(Z.map (ofHom (evalRingHom PlaceField ⟨p, ⊤, by simp⟩) ≫ m) $(?z)).trans
    (by simp_rw [← r, ← map_comp_apply, ← e]; congr 3 with; exact congr($i _).trans (k.2 _)))⟩

/-- A functor of points Z that is proper over D in the sense of `IsProperOver` has the
continuity property `IsCohomContinuous` for filtered limits, with coefficients in locally
constant Λ-valued functions. -/
lemma isCohomContinuous : IsCohomContinuous Λ Z := h.2.elim fun _ ⟨a, ha⟩ ↦ .of_atlas
  (h.isRelAffine_pointMap a) ((h.isRelAffine_pointMap _).hasCohomDenseImage_of_lifts fun O _ ↦
  (ha O _ (by simp)).imp' _ fun _ ↦ (h.injective_map_valuationSubring O <| .trans (by aesop) ·))
