/- GID: D5/S3/Quantum/Foundation/ActualExclusionBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ActualExclusionBoundary
   mirror-E: none(waiver:abstract-convex-geometric-construction)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Whole exclusions cover the actual boundary and detect its boundary midpoints. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Relative-boundary geometry of the entire original normalized cone base. -/

noncomputable section
open Set Topology

namespace D5.S3.Quantum.Foundation.ActualExclusionBoundary

open CircuitBalancedConfirmation WeightedRelationConfirmation FacetZeroGluing
open WholePairBallConfirmation ExclusionBallFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℝ V] in
private theorem cone_interior_base_interior {x : V} (hx : x ∈ base C u)
    (hi : x ∈ interior (C : Set V)) : x ∈ intrinsicInterior ℝ (base C u) := by
  let A : AffineSubspace ℝ V := ({(1 : ℝ)} : AffineSubspace ℝ ℝ).comap u.toAffineMap
  have hKA : affineSpan ℝ (base C u) ≤ A := affineSpan_le.mpr (by
    intro y hy
    simpa [A] using hy.2)
  have hunit (y : affineSpan ℝ (base C u)) : u y = 1 := by
    have hh := hKA y.property
    simpa [A] using hh
  let a : affineSpan ℝ (base C u) := ⟨x, subset_affineSpan ℝ _ hx⟩
  refine ⟨a, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  have hn : {y : affineSpan ℝ (base C u) | (y : V) ∈ C} ∈ nhds a :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hi)
  exact Filter.mem_of_superset hn (fun y hy => ⟨hy, hunit y⟩)

private theorem exclusion_boundary
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : exclusion C u p ⊆ intrinsicFrontier ℝ (base C u) := by
  have hK := (base_compact hclosed hstrict).isClosed
  obtain ⟨f, hf, hzero⟩ := (exclusion_ball_faces hclosed hstrict hgen hB).1 p |>.2.2.2.2.2.2
  intro x hx
  rw [← closure_sdiff_intrinsicInterior, hK.closure_eq]
  refine ⟨hx.1, ?_⟩
  rintro ⟨a, ha, he⟩
  let : Nonempty (affineSpan ℝ (base C u)) := ⟨a⟩
  let b : affineSpan ℝ (base C u) := ⟨p, subset_affineSpan ℝ _ (pure_mem p)⟩
  have hcont : Continuous (fun t : ℝ => AffineMap.lineMap (k := ℝ) b a t) :=
    AffineMap.lineMap_continuous
  obtain ⟨t, ht, hz⟩ := hcont.tendsto' 1 a (AffineMap.lineMap_apply_one b a) |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp ha) |>.exists_gt
  have hfx : f x = 0 := (hzero ▸ hx).2
  have hbound := (hf.1 _ hz.1).1
  have hval : f ((AffineMap.lineMap (k := ℝ) b a t : affineSpan ℝ (base C u)) : V) =
      1 - t := by
    rw [AffineMap.lineMap_apply]
    change f (t • ((a : V) - (p : V)) + (p : V)) = 1 - t
    simp only [map_add, map_sub, map_smul, smul_eq_mul, he, hfx, hf.2]
    ring
  rw [hval] at hbound
  linarith

private theorem boundary_support_face
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    {x : V} (hx : x ∈ intrinsicFrontier ℝ (base C u)) :
    ∃ F : Set V, x ∈ F ∧ Convex ℝ F ∧ IsExtreme ℝ (base C u) F ∧ F ≠ base C u := by
  have hK := (base_compact hclosed hstrict).isClosed
  have hxK := intrinsicFrontier_subset hK hx
  have hnot : x ∉ interior (C : Set V) := by
    intro hi
    have hii := cone_interior_base_interior hxK hi
    rw [← closure_sdiff_intrinsicInterior, hK.closure_eq] at hx
    exact hx.2 hii
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hgen]
    rfl
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point C.convex hnot hint
  have h0 : 0 ≤ f x := by simpa using hmax 0 C.zero_mem
  have h2 := hmax ((2 : ℝ) • x) (C.smul_mem (by norm_num) hxK.1)
  have hfx : f x = 0 := by simp only [map_smul, smul_eq_mul] at h2; linarith
  let F : Set V := f.toExposed (base C u)
  have hext : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hxF : x ∈ F := ⟨hxK, fun y hy => by simpa [hfx] using hmax y hy.1⟩
  refine ⟨F, hxF, ?_, hext.isExtreme, ?_⟩
  · exact hext.convex (base_convex C u)
  · intro he
    have hzero (p : pure C u) : f p = 0 := by
      have hpF : (p : V) ∈ F := he.symm ▸ pure_mem p
      exact le_antisymm (by simpa [hfx] using hmax p (pure_mem p).1)
        (by simpa [hfx] using hpF.2 x hxK)
    have hs : Submodule.span ℝ (pure C u) ≤ LinearMap.ker f.toLinearMap :=
      Submodule.span_le.mpr (fun p hp => hzero ⟨p, hp⟩)
    rw [pure_span (base_compact hclosed hstrict) hstrict hgen] at hs
    apply hf
    have heq := LinearMap.ker_eq_top.mp (top_le_iff.mp hs)
    ext y
    exact LinearMap.congr_fun heq y

/-- With the original full effects and variable positive exclusion dimensions,
whole exclusions cover the entire actual relative boundary. Two base points
have a boundary midpoint exactly when they belong to one whole exclusion ball.
No repeated-label, Pair or quotient regularity assumption is used. -/
theorem original_boundary_cover_and_midpoint
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    (∀ x ∈ intrinsicFrontier ℝ (base C u), ∃ p : pure C u, x ∈ exclusion C u p) ∧
    ∀ x ∈ base C u, ∀ y ∈ base C u,
      midpoint ℝ x y ∈ intrinsicFrontier ℝ (base C u) ↔
        ∃ p : pure C u, x ∈ exclusion C u p ∧ y ∈ exclusion C u p := by
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  have hcover : ∀ x ∈ intrinsicFrontier ℝ (base C u),
      ∃ p : pure C u, x ∈ exclusion C u p := by
    intro x hx
    obtain ⟨F, hxF, hconv, hface, hproper⟩ := boundary_support_face hclosed hstrict hgen hx
    rcases all.2.1 F ⟨x, hxF⟩ hconv hface hproper with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hxp : x = p := by simpa [hp] using hxF
      have g := all.1 p
      obtain ⟨q, hq⟩ := g.2.1.extremePoints_nonempty g.1.nonempty
      have hqP : q ∈ pure C u := g.2.2.2.2.1.extremePoints_subset_extremePoints hq
      exact ⟨⟨q, hqP⟩, hxp ▸ (exclusion_symmetric p ⟨q, hqP⟩).mp hq.1⟩
    · exact ⟨p, hp ▸ hxF⟩
  refine ⟨hcover, ?_⟩
  intro x hx y hy
  constructor
  · intro hm
    obtain ⟨p, hp⟩ := hcover _ hm
    have hseg : midpoint ℝ x y ∈ openSegment ℝ x y := midpoint_mem_openSegment x y
    have hf := (all.1 p).2.2.2.2.1
    exact ⟨p, hf.left_mem_of_mem_openSegment hx hy hp hseg,
      hf.right_mem_of_mem_openSegment hx hy hp hseg⟩
  · rintro ⟨p, hp, hq⟩
    exact exclusion_boundary hclosed hstrict hgen hB p
      ((all.1 p).2.2.1.midpoint_mem hp hq)

private theorem repeated_ball_isolated
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p s : pure C u) (hps : p ≠ s) (hs : exclusion C u s = exclusion C u p)
    (q : pure C u) :
    exclusion C u p = exclusion C u q ∨ Disjoint (exclusion C u p) (exclusion C u q) := by
  classical
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  have two (a b : pure C u) {x y : V}
      (hx : x ∈ exclusion C u a ∩ exclusion C u b)
      (hy : y ∈ exclusion C u a ∩ exclusion C u b) (hxy : x ≠ y) :
      exclusion C u a = exclusion C u b := by
    have hc := (all.1 a).2.2.1.inter (all.1 b).2.2.1
    have hf := (all.1 a).2.2.2.2.1.inter (all.1 b).2.2.2.2.1
    have hn : (exclusion C u a ∩ exclusion C u b).Nontrivial := ⟨x, hx, y, hy, hxy⟩
    have ha := chart_face_eq (hB a).some hc
      (hf.mono (all.1 a).2.2.2.2.1.subset inter_subset_left) hn
    have hb := chart_face_eq (hB b).some hc
      (hf.mono (all.1 b).2.2.2.2.1.subset inter_subset_right) hn
    exact ha.symm.trans hb
  by_cases he : exclusion C u p = exclusion C u q
  · exact Or.inl he
  right
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  have hsingle : exclusion C u p ∩ exclusion C u q = {x} := by
    apply Set.Subsingleton.eq_singleton_of_mem (s := exclusion C u p ∩ exclusion C u q)
      _ (show x ∈ exclusion C u p ∩ exclusion C u q from ⟨hxp, hxq⟩)
    intro a ha b hb
    by_contra hab
    exact he (two p q ha hb hab)
  have hxP : x ∈ pure C u := by
    apply isExtreme_singleton.mp
    rw [← hsingle]
    exact (all.1 p).2.2.2.2.1.inter (all.1 q).2.2.2.2.1
  let r : pure C u := ⟨x, hxP⟩
  have hpr : (p : V) ∈ exclusion C u r := (exclusion_symmetric p r).mp hxp
  have hsr : (s : V) ∈ exclusion C u r := (exclusion_symmetric s r).mp (hs.symm ▸ hxp)
  have hqr : (q : V) ∈ exclusion C u r := (exclusion_symmetric q r).mp hxq
  have hpure : (exclusion C u p).extremePoints ℝ ⊆ exclusion C u q := by
    intro y hy
    have hyP : y ∈ pure C u := (all.1 p).2.2.2.2.1.extremePoints_subset_extremePoints hy
    let t : pure C u := ⟨y, hyP⟩
    have hpt : (p : V) ∈ exclusion C u t := (exclusion_symmetric p t).mp hy.1
    have hst : (s : V) ∈ exclusion C u t :=
      (exclusion_symmetric s t).mp (hs.symm ▸ hy.1)
    have htr : exclusion C u t = exclusion C u r :=
      two t r ⟨hpt, hpr⟩ ⟨hst, hsr⟩ (fun h => hps (Subtype.ext h))
    exact (exclusion_symmetric q t).mpr (htr.symm ▸ hqr)
  have hsub : exclusion C u p ⊆ exclusion C u q := by
    rw [← closure_convexHull_extremePoints (all.1 p).2.1 (all.1 p).2.2.1]
    exact closure_minimal (convexHull_min hpure (all.1 q).2.2.1) (all.1 q).2.1.isClosed
  exact he (chart_face_eq (hB q).some (all.1 p).2.2.1
    ((all.1 p).2.2.2.2.1.mono (all.1 q).2.2.2.2.1.subset hsub) (all.1 p).1)

/-- In the all-repeated contradiction branch, the literal midpoint relation on
all of the actual relative boundary is a closed equivalence relation. Its actual
quotient is compact Hausdorff, and the canonical projection is continuous,
surjective and closed. No regularity of the quotient is assumed. -/
theorem original_all_repeated_boundary_quotient
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p) :
    ∃ r : Setoid (intrinsicFrontier ℝ (base C u)),
      (∀ x y, r x y ↔ midpoint ℝ (x : V) (y : V) ∈ intrinsicFrontier ℝ (base C u)) ∧
      (∀ x y, r x y ↔ ∃ p : pure C u, (x : V) ∈ exclusion C u p ∧
        (y : V) ∈ exclusion C u p) ∧
      IsClosed {z : intrinsicFrontier ℝ (base C u) × intrinsicFrontier ℝ (base C u) |
        r z.1 z.2} ∧
      CompactSpace (Quotient r) ∧ T2Space (Quotient r) ∧
      Continuous (Quotient.mk r) ∧ Function.Surjective (Quotient.mk r) ∧
      IsClosedMap (Quotient.mk r) ∧
      ∀ b : Quotient r, ∃ p : pure C u,
        Subtype.val '' ((Quotient.mk r) ⁻¹' {b}) = exclusion C u p := by
  classical
  let S := intrinsicFrontier ℝ (base C u)
  have hSclosed : IsClosed S :=
    isClosed_intrinsicFrontier (affineSpan ℝ (base C u)).closed_of_finiteDimensional
  have hSK : S ⊆ base C u := intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
  have hScompact : IsCompact S := (base_compact hclosed hstrict).of_isClosed_subset hSclosed hSK
  let : CompactSpace S := isCompact_iff_compactSpace.mp hScompact
  have crit := (original_boundary_cover_and_midpoint hclosed hstrict hgen hB).2
  let r : Setoid S :=
    { r := fun x y => midpoint ℝ (x : V) (y : V) ∈ S
      iseqv := ⟨by intro x; simpa only [midpoint_self] using x.property,
        by intro x y h; simpa only [midpoint_comm] using h,
        by
          intro x y z hxy hyz
          obtain ⟨p, hxp, hyp⟩ := (crit x (hSK x.property) y (hSK y.property)).mp hxy
          obtain ⟨q, hyq, hzq⟩ := (crit y (hSK y.property) z (hSK z.property)).mp hyz
          obtain ⟨s, hps, hs⟩ := hrepeated p
          rcases repeated_ball_isolated hclosed hstrict hgen hB p s hps hs q with he | hd
          · exact (crit x (hSK x.property) z (hSK z.property)).mpr ⟨p, hxp, he.symm ▸ hzq⟩
          · exact ((Set.disjoint_left.mp hd) hyp hyq).elim⟩ }
  have hgraph : IsClosed {z : S × S | r z.1 z.2} := by
    apply hSclosed.preimage
    rw [show (fun z : S × S => midpoint ℝ (z.1 : V) (z.2 : V)) =
      (fun z => (1 / 2 : ℝ) • ((z.1 : V) + (z.2 : V))) by
        funext z; simp [midpoint_eq_smul_add, invOf_eq_inv]]
    exact ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).const_smul _
  let q : S → Quotient r := Quotient.mk r
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hqclosed : IsClosedMap q := by
    intro F hF
    apply hq.isCoinducing.isClosed_preimage.mp
    have he : q ⁻¹' (q '' F) = Prod.snd ''
        ({z : S × S | r z.1 z.2} ∩ (F ×ˢ univ)) := by
      ext b
      constructor
      · rintro ⟨a, ha, hab⟩
        exact ⟨(a,b), ⟨Quotient.exact hab, ha, mem_univ b⟩, rfl⟩
      · rintro ⟨⟨a,c⟩, ⟨hac, ha, _⟩, rfl⟩
        exact ⟨a, ha, Quotient.sound hac⟩
    rw [he]
    exact isClosedMap_snd_of_compactSpace _ (hgraph.inter (hF.prod isClosed_univ))
  have hproper : IsProperMap q := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hq.continuous, hqclosed, ?_⟩
    intro b
    obtain ⟨a, rfl⟩ := Quotient.exists_rep b
    have he : q ⁻¹' {q a} = {c | r a c} := by
      ext c
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      exact ⟨fun h => Quotient.exact h.symm, fun h => (Quotient.sound h).symm⟩
    rw [he]
    exact (hgraph.preimage (continuous_const.prodMk continuous_id)).isCompact
  have hprod : IsQuotientMap (Prod.map q q) :=
    (hproper.prodMap hproper).isClosedMap.isQuotientMap
      (hq.continuous.prodMap hq.continuous) (hq.surjective.prodMap hq.surjective)
  have hT2 : T2Space (Quotient r) := by
    apply t2_iff_isClosed_diagonal.mpr
    apply hprod.isCoinducing.isClosed_preimage.mp
    convert hgraph using 1
    ext z
    exact Quotient.eq
  refine ⟨r, (by intros; rfl), ?_, hgraph, inferInstance, hT2,
    hq.continuous, hq.surjective, hqclosed, ?_⟩
  · intro x y
    exact crit x (hSK x.property) y (hSK y.property)
  · intro b
    obtain ⟨x, rfl⟩ := Quotient.exists_rep b
    obtain ⟨p, hxp⟩ := (original_boundary_cover_and_midpoint hclosed hstrict hgen hB).1
      x x.property
    refine ⟨p, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hxz : r x z := Quotient.exact (mem_singleton_iff.mp hz).symm
      obtain ⟨a, hxa, hza⟩ := (crit x (hSK x.property) z (hSK z.property)).mp hxz
      obtain ⟨s, hps, hs⟩ := hrepeated p
      rcases repeated_ball_isolated hclosed hstrict hgen hB p s hps hs a with he | hd
      · exact he.symm ▸ hza
      · exact ((Set.disjoint_left.mp hd) hxp hxa).elim
    · intro hy
      let z : S := ⟨y, exclusion_boundary hclosed hstrict hgen hB p hy⟩
      have hxz : r x z := (crit x (hSK x.property) z (hSK z.property)).mpr ⟨p, hxp, hy⟩
      exact ⟨z, (Quotient.sound hxz).symm, rfl⟩

private theorem intrinsic_level_of_straddling {K : Set V} (hK : Convex ℝ K)
    (f : V →ₗ[ℝ] ℝ) {x y : V} (hx : x ∈ K) (hy : y ∈ K)
    {t : ℝ} (hxt : f x < t) (hty : t < f y) :
    ∃ z ∈ intrinsicInterior ℝ K, f z = t := by
  obtain ⟨c, hc⟩ := Set.Nonempty.intrinsicInterior hK ⟨x, hx⟩
  rcases lt_trichotomy (f c) t with hct | hct | htc
  · have ht : t ∈ f.toAffineMap '' openSegment ℝ c y := by
      rw [image_openSegment]
      exact Ioo_subset_openSegment ⟨hct, hty⟩
    obtain ⟨z, hz, he⟩ := ht
    exact ⟨z, hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hc (subset_intrinsicClosure hy) hz, he⟩
  · exact ⟨c, hc, hct⟩
  · have ht : t ∈ f.toAffineMap '' openSegment ℝ x c := by
      rw [image_openSegment]
      exact Ioo_subset_openSegment ⟨hxt, htc⟩
    obtain ⟨z, hz, he⟩ := ht
    rw [openSegment_symm] at hz
    exact ⟨z, hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hc (subset_intrinsicClosure hx) hz, he⟩

/-- Actual rational slices of the original boundary quotient. The open set is
chosen within closed crossing sets, so every one of its whole fibers has points
on both sides of the very same slice. -/
theorem original_all_repeated_rational_slice [Nontrivial V]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p) :
    ∃ r : Setoid (intrinsicFrontier ℝ (base C u)),
      (∀ x y, r x y ↔ midpoint ℝ (x : V) (y : V) ∈ intrinsicFrontier ℝ (base C u)) ∧
      CompactSpace (Quotient r) ∧ T2Space (Quotient r) ∧
      Continuous (Quotient.mk r) ∧ IsClosedMap (Quotient.mk r) ∧
      (∀ b : Quotient r, ∃ p : pure C u,
        Subtype.val '' ((Quotient.mk r) ⁻¹' {b}) = exclusion C u p) ∧
      ∃ (f : V →ₗ[ℝ] ℝ) (t : ℚ) (O : Set (Quotient r)),
        f ≠ 0 ∧ IsOpen O ∧ O.Nonempty ∧
        (∃ c ∈ intrinsicInterior ℝ (base C u), f c = (t : ℝ)) ∧
        O ⊆ (Quotient.mk r) '' {x | f (x : V) = (t : ℝ)} ∧
        ∀ b ∈ O, ∃ x y : intrinsicFrontier ℝ (base C u),
          Quotient.mk r x = b ∧ Quotient.mk r y = b ∧
          f (x : V) < (t : ℝ) ∧ (t : ℝ) < f (y : V) := by
  classical
  obtain ⟨r, hr, _, _, hcompact, ht2, hq, _, hqc, hfib⟩ :=
    original_all_repeated_boundary_quotient hclosed hstrict hgen hB hrepeated
  let S := intrinsicFrontier ℝ (base C u)
  let q : S → Quotient r := Quotient.mk r
  let := hcompact
  let := ht2
  have hSclosed : IsClosed S :=
    isClosed_intrinsicFrontier (affineSpan ℝ (base C u)).closed_of_finiteDimensional
  have hSK : S ⊆ base C u := intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((base_compact hclosed hstrict).of_isClosed_subset hSclosed hSK)
  have hP : (pure C u).Nonempty := by
    by_contra hn
    have hh := pure_span (base_compact hclosed hstrict) hstrict hgen
    rw [Set.not_nonempty_iff_eq_empty.mp hn, Submodule.span_empty] at hh
    exact bot_ne_top hh
  obtain ⟨p₀, hp₀⟩ := hP
  obtain ⟨z₀, hz₀⟩ := ((exclusion_ball_faces hclosed hstrict hgen hB).1 ⟨p₀, hp₀⟩).1.nonempty
  let : Nonempty S := ⟨⟨z₀, exclusion_boundary hclosed hstrict hgen hB ⟨p₀,hp₀⟩ hz₀⟩⟩
  let : Nonempty (Quotient r) := ⟨q (Classical.choice inferInstance)⟩
  let e := (Module.finBasis ℝ V).equivFun
  let f (i : Fin (Module.finrank ℝ V)) : V →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp e.toLinearMap
  let J := Fin (Module.finrank ℝ V) × ℚ × ℚ
  let F (j : J) : Set (Quotient r) :=
    if j.2.1 < j.2.2 then
      q '' {x : S | f j.1 x ≤ (j.2.1 : ℝ)} ∩
      q '' {x : S | (j.2.2 : ℝ) ≤ f j.1 x}
    else ∅
  have hFclosed (j : J) : IsClosed (F j) := by
    dsimp [F]
    split_ifs
    · exact (hqc _ (isClosed_le
        ((f j.1).continuous_of_finiteDimensional.comp continuous_subtype_val) continuous_const)).inter
        (hqc _ (isClosed_le continuous_const
        ((f j.1).continuous_of_finiteDimensional.comp continuous_subtype_val)))
    · exact isClosed_empty
  have hcover : ⋃ j, F j = univ := by
    apply eq_univ_of_forall
    intro b
    obtain ⟨p, hp⟩ := hfib b
    obtain ⟨x, hx, y, hy, hxy⟩ := ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).1
    have hcoord : ∃ i, f i x ≠ f i y := by
      by_contra hn
      push Not at hn
      exact hxy (e.injective (funext hn))
    obtain ⟨i, hi⟩ := hcoord
    have across : ∃ x y : S, q x = b ∧ q y = b ∧ f i x < f i y := by
      obtain ⟨a, ha, hax⟩ := hp.symm ▸ hx
      obtain ⟨c, hc, hcy⟩ := hp.symm ▸ hy
      have ha' : q a = b := ha
      have hc' : q c = b := hc
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact ⟨a, c, ha', hc', by simpa [hax, hcy] using hlt⟩
      · exact ⟨c, a, hc', ha', by simpa [hax, hcy] using hgt⟩
    obtain ⟨a, c, ha, hc, hac⟩ := across
    obtain ⟨v, hav, hvc⟩ := exists_rat_btwn hac
    obtain ⟨w, hvw, hwc⟩ := exists_rat_btwn hvc
    have hvw' : v < w := by exact_mod_cast hvw
    apply mem_iUnion.mpr
    refine ⟨(i,v,w), ?_⟩
    simp only [F, hvw', ↓reduceIte]
    exact ⟨⟨a, hav.le, ha⟩, ⟨c, hwc.le, hc⟩⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hcover
  have hab : j.2.1 < j.2.2 := by
    by_contra hn
    simp [F, hn] at hj
  have habR : (j.2.1 : ℝ) < (j.2.2 : ℝ) := by exact_mod_cast hab
  let t : ℚ := (j.2.1 + j.2.2) / 2
  have hat : (j.2.1 : ℝ) < (t : ℝ) := by dsimp [t]; push_cast; linarith
  have htb : (t : ℝ) < (j.2.2 : ℝ) := by dsimp [t]; push_cast; linarith
  have across (b : Quotient r) (hb : b ∈ interior (F j)) :
      ∃ x y : S, q x = b ∧ q y = b ∧ f j.1 x < (t : ℝ) ∧ (t : ℝ) < f j.1 y := by
    have hh := interior_subset hb
    simp only [F, hab, ↓reduceIte] at hh
    obtain ⟨⟨x, hx, hxb⟩, ⟨y, hy, hyb⟩⟩ := hh
    exact ⟨x,y,hxb,hyb,hx.trans_lt hat,htb.trans_le hy⟩
  obtain ⟨b, hb⟩ := hj.exists
  obtain ⟨x,y,_,_,hx,hy⟩ := across b hb
  refine ⟨r, hr, hcompact, ht2, hq, hqc, hfib, f j.1, t, interior (F j),
    ?_, isOpen_interior, hj, ?_, ?_, across⟩
  · intro he
    have hx' := hx
    have hy' := hy
    rw [he] at hx' hy'
    simp only [LinearMap.zero_apply] at hx' hy'
    linarith
  · exact intrinsic_level_of_straddling (base_convex C u) (f j.1)
      (hSK x.property) (hSK y.property) hx hy
  · intro b hb
    obtain ⟨x,y,hxb,hyb,hx,hy⟩ := across b hb
    obtain ⟨p,hp⟩ := hfib b
    have hxD : (x : V) ∈ exclusion C u p := hp ▸ ⟨x,hxb,rfl⟩
    have hyD : (y : V) ∈ exclusion C u p := hp ▸ ⟨y,hyb,rfl⟩
    have ht : (t : ℝ) ∈ (f j.1).toAffineMap '' segment ℝ (x : V) (y : V) := by
      rw [image_segment]
      exact Icc_subset_segment ⟨hx.le,hy.le⟩
    obtain ⟨z,hz,hzt⟩ := ht
    have hzD := ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).2.2.1.segment_subset hxD hyD hz
    obtain ⟨a,ha,haz⟩ := hp.symm ▸ hzD
    exact ⟨a, by simpa [haz] using hzt, ha⟩

end D5.S3.Quantum.Foundation.ActualExclusionBoundary
