/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Etale.AcyclicTests. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/AcyclicTests.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestEnvelope
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.FilteredColimits
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.BijectiveComparisons
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Relatively representable (affine) maps of functors on rings: pullbacks, closed and open
loci. Tests are acyclic; tests and locally constant functions commute with filtered colimits. -/

open CategoryTheory CommRingCat IsLocalization Ideal Quotient
variable {X Y W V : PointFunctor} {p : X ⟶ Y} {u : W ⟶ Y} {q v R} (s : X ⟶ reprBy R) (I)

/-- The property of a map X → Y of set-valued functors on rings that its pull-back along every
point h_A → Y is representable, of the form h_B → h_A. -/
abbrev IsRelAffine : MorphismProperty PointFunctor := reprFunctor.relativelyRepresentable

lemma IsRelAffine.baseChange : IsRelAffine p → IsPullback v q p u → @IsRelAffine V W q :=
  flip IsRelAffine.of_isPullback

lemma IsRelAffine.comp : @IsRelAffine W X v → IsRelAffine p → IsRelAffine (v ≫ p) :=
  IsRelAffine.comp_mem v p

lemma unitPoints_le_range_reprMap L [CommRing L] [Algebra R L] M [IsLocalization (R := R) M L] :
  unitPoints (𝟙 _) M ≤ .range (reprMap (ofHom (algebraMap R L))) := fun _ _ _ ↦
  ⟨⟨_⟩, congr(⟨ofHom $(lift_comp (by simpa))⟩)⟩

lemma isRelAffine_of_zero_unit_locus {U} (h : ∀ {R} y, ∃ A N : Set _, ∀ B f, @Y.map R B f y ∈ U B ↔
  (∀ a ∈ A, f a = 0) ∧ ∀ a ∈ N, IsUnit (f a)) : IsRelAffine (Subfunctor.ι U) := fun _ ↦
  uliftCoyonedaEquiv.forall_congr_left.2 (h · |>.elim fun A ⟨N, h⟩ ↦ let L := Localization (.closure
    N); ⟨_, ⟨ofHom (algebraMap _ (_ ⧸ span (algebraMap _ L '' A)))⟩, pointMap ⟨_, (h ..).2
    ⟨fun _ _ ↦ eq_zero_iff_mem.2 (by aesop), (isUnit_comp _ _ ⟨·, Submonoid.subset_closure ·⟩)⟩⟩,
    isPullback_iff.2 ⟨fun _ _ ↦ (Y.map_comp_apply ..).symm, by
    rintro _ ⟨⟩ ⟨⟩ ⟨⟩; cases (h ..).1 ‹_›; obtain ⟨l, ⟨⟩⟩ := (unitPoints_le_range_reprMap L _ _
      (((IsUnit.submonoid _).comap _).closure_le.2 ‹_›)); exact ⟨⟨ofHom (lift _ _ ((RingHom.ker
      _).span_le.2 (by simpa)))⟩, ⟨rfl, SetCoe.ext (Y.map_comp_apply ..).symm⟩, fun ⟨_⟩ ⟨a, _⟩ ↦
      congrArg _ (hom_ext (ringHom_ext (ringHom_ext (.closure N) congr($a.1.1))))⟩⟩⟩)

lemma isRelAffine_zeroPoints : IsRelAffine (zeroPoints s I).ι :=
  isRelAffine_of_zero_unit_locus (⟨baseRingMap s · '' I, ∅, by simp [zeroPoints]⟩)

open Limits colimit Concrete Function Abelian.Ext LocallyConstant PrimeSpectrum Comparison ULift
  IsFiltered
variable {Λ : Ab} {J B B' T T'} (q : T ⟶ testIncl ⋙ reprBy B) {q' :
  T' ⟶ testIncl ⋙ reprBy B'} [SmallCategory J] [IsFiltered J] {L : J ⥤ CommRingCat}

lemma isFilteredColimit_locConstSpec {c : Cocone L} (s : ∀ y : c.pt, ∃ j x, c.ι j x = y) (h : ∀ j x,
  c.ι j x = 0 → ∃ i f, @L.map j i f x = 0) : IsFilteredColimit ((locConstSpec Λ).mapCocone c) :=
  ⟨fun j x l ↦ (isClopen_iff_zeroLocus.1 (x.2.isClopen_fiber 0)).elim fun e ⟨i,
  o⟩ ↦ by peel h _ e ((i.map _).eq_zero_of_isNilpotent (nilpotent_iff_mem_prime.2
  (o.le congr($l.1 ⟨·, ·⟩) rfl))) using LocallyConstant.ext fun _ ↦ o.ge (by aesop),
  fun y ↦ (locallyConstant_mem_of_indicator (fun a e k ↦ (s e).elim fun j ⟨d, r⟩ ↦ (h _ (d * d - d)
  (by aesop)).elim fun i ⟨f, _⟩ ↦ by simpa only [← r, ← c.w f] using ⟨_, ι_desc_apply
  ((locConstSpec Λ).mapCocone c) i (indicator (.const ..) (isClopen_iff.2 ⟨_, by aesop, rfl⟩))⟩) y :
  y ∈ (desc (C := Ab) ..).hom.range).elim (colimit_exists_rep _ · |>.elim (by aesop))⟩

/-- For q: T → h_B on test rings, the map from locally constant functions Spec B → Λ to Hⁿ(T,
Λ): pull-back along q for n = 0, zero for n > 0. -/
noncomputable def locConstClass : ∀ n, locConstSpec Λ B →+ H (freeAb T) (locConstCoeff Λ) n
  | 0 => .comp (.mk' mk₀ mk₀_add)
    ((Comparison.homOfValue ⟨testIncl, 𝟙 (_ ⋙ liftCoeff _)⟩ q).comp (.mk' _ (by tauto))) | _ => 0

/-- Property of q: T → h_B on tests: pull-back LC(Spec B, Λ) → H^0(T, Λ) is bijective and H^n(T,
Λ) = 0 for n > 0. -/
def IsAcyclicOver Λ := Injective (@locConstClass Λ B T q 0) ∧ ∀ n,
  Surjective (@locConstClass Λ B T q n)

variable {q}

lemma map_locConstClass {e f f'} (h : ∀ c x, (locConstSpec Λ).map (q c (e c x)).1 f = (locConstSpec
  Λ).map (q' c x).1 f') : ∀ n, .map _ (freeAb.map e) n (locConstClass q n f) = locConstClass q' n f'
  | 0 => (mk₀_comp_mk₀ ..).trans (congrArg _ (freeAb.hom_ext fun _ _ ↦ congr(⟨$(by tauto)⟩)))
  | _+1 => map_zero _

lemma bijective_const_of_isDomain {Λ} [IsDomain B] :
  Bijective (⟨.const _ ·⟩ : Λ → ULift.{1} (LocallyConstant
  (PrimeSpectrum B) Λ)) := ⟨fun _ _ ↦ (congr($(·).1 ⊥)), fun ⟨x⟩ ↦ x.eq_const ⊥ ▸ ⟨_, rfl⟩⟩

lemma IsAcyclicOver.isCohomEquiv (a : IsDomain B) (b : IsDomain B') u (h : IsAcyclicOver q Λ)
    (h' : IsAcyclicOver q' Λ) : IsCohomEquiv (locConstCoeff Λ) (@freeAb.map T' T u)
  | 0 => (bijective_iff_of_comm_sq (by exact fun _ ↦ map_locConstClass (by tauto) 0) (.comp ⟨h.1,
    h.2 0⟩ (down_bijective.comp bijective_const_of_isDomain)) (.comp ⟨h'.1,
    h'.2 0⟩ (down_bijective.comp bijective_const_of_isDomain))).1 bijective_id
  | _+1 => ⟨(h.2 _).forall₂.2 (by tauto), (h'.2 _).forall.2 fun _ ↦ ⟨_, map_zero _⟩⟩

/-- A filtered colimit of test rings is a test ring. -/
lemma IsTest.filtered_colimit (h : ∀ j, IsTest (L.obj j)) : IsTest ↑(colimit L) := by
  choose j _ hy using colimit_exists_rep L
  choose! z hz using fun s x _ ↦
    Set.mem_range.2 ⟨_, hy _ ▸ w_apply L (toSup (.image ..) ∅ (by aesop)) _⟩
  use ⟨fun P ↦ (h _).exists_root_of_coeffs_subset_range (by tauto)⟩, fun f g ↦ ((h _).2 (z _ f) (z
    {f, g} g)).imp' (ι L _) (by grind [IsIdempotentElem, → map_dvd (ι L _).hom]), fun x ⟨n, e⟩ ↦ ?_
  erw [← hy x, ← map_zero (ι L _).hom, ← map_pow, (isColimit L).eq_iff'] at *
  grind [(h _).3.1 _ ⟨n, _⟩]

seal Comparison.homOfValue

/-- If B is a test ring and q : T → h_B is bijective on points in every test ring, then H⁰(T, Λ)
is, via q, the group of locally constant functions Spec B → Λ, and Hⁿ(T, Λ) = 0 for n > 0. -/
lemma IsAcyclicOver.of_bijective (h : IsTest B) (b : ∀ {C}, Bijective (q C)) : IsAcyclicOver q Λ :=
  (isBijective_reprBy_iff.1
  (.precomp_of_bijective (isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful testIncl ⟨B,
  h⟩) bijective_id) q (Category.comp_id _) @b)).elim fun a b ↦
  ((mk₀_bijective ..).comp (a.comp up_bijective)).imp_right (Nat.rec · fun _ _ ↦ (⟨0, (b _).1 _ ·⟩))

/-- The functor restricting a set-valued functor on commutative rings to the full subcategory of
test rings, by precomposition with the inclusion. -/
abbrev onTests := restrictAlong (D := Type 1) testIncl

/-- If a test ring A is the filtered colimit, as a ring, of test rings A_j, then the
Λ-cohomology H^n(h_A) on test rings is the colimit of the H^n(h_{A_j}), for every n. -/
lemma continuousUpTo_locConstCoeff (h : ∀ j, IsTest (L j)) :
    ∀ r, ContinuousUpTo (locConstCoeff Λ) ((reprFunctor ⋙ onTests).mapCone (cocone L).op) r :=
  forall_bijective_iff_bijectiveUpTo.1 (isFilteredColimit_iff_bijective.1 ∘' by
  choose i s using (@IsAcyclicOver.of_bijective Λ · _ (𝟙 _) · bijective_id)
  rintro ⟨⟩ <;> simp [IsFilteredColimit, (s _ _ _).forall, (s _ _ _).exists, (i ..).eq_iff,
    ↓fun A B φ x ↦ @map_locConstClass Λ A B _ _ (𝟙 _) (𝟙 _) (mapOnTests (reprMap φ)) x
    ((locConstSpec _).map φ x) (by tauto),
    _root_.map_eq_zero_iff, locConstClass.eq_2, IsTest.filtered_colimit h, nonempty, *]
  exacts [isFilteredColimit_locConstSpec (colimit_exists_rep _) fun _ x ↦ by simpa using
    ((isColimit L).eq_iff' x 0).1, (⟨·, ⟨𝟙 _⟩⟩)])
