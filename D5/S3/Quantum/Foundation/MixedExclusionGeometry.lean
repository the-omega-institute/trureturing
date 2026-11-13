/- GID: D5/S3/Quantum/Foundation/MixedExclusionGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/MixedExclusionGeometry
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Proper.Basic]
   utility: none
   digest: Actual nonpure exclusion fibers have continuous labels and a fiberwise contraction. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import Mathlib.LinearAlgebra.AffineSpace.Restrict
import D5.S3.Topology.TauCeti.Topology.Category.TopPair

/-! Original mixed-state fibers and their actual label-preserving maps. -/

noncomputable section
open Set

namespace D5.S3.Quantum.Foundation.MixedExclusionGeometry

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]
  {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- All nonpure states belonging to an entire original exclusion. -/
def mixedExcluded (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set V :=
  {x | x ∉ pure C u ∧ ∃ p : pure C u, x ∈ exclusion C u p}

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤)
  (hB : exclusionBalls C u) (hW : weakPair C u)

include hc hs hg in
omit [Nontrivial V] in
theorem frontier_covered {x : V} (hx : x ∈ intrinsicFrontier ℝ (base C u)) :
    ∃ p : pure C u, x ∈ exclusion C u p := by
  have hxK := intrinsicFrontier_subset (base_compact hc hs).isClosed hx
  have hxnot : x ∉ interior (C : Set V) := by
    intro hxi
    have hri : x ∈ intrinsicInterior ℝ (base C u) := by
      let A : AffineSubspace ℝ V := ({(1 : ℝ)} : AffineSubspace ℝ ℝ).comap u.toAffineMap
      have hKA : affineSpan ℝ (base C u) ≤ A := affineSpan_le.mpr (by
        intro y hy
        simpa [A] using hy.2)
      let y : affineSpan ℝ (base C u) := ⟨x,subset_affineSpan ℝ _ hxK⟩
      refine ⟨y,mem_interior_iff_mem_nhds.mpr ?_,rfl⟩
      have hn : {z : affineSpan ℝ (base C u) | (z : V) ∈ C} ∈ nhds y :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hxi)
      exact Filter.mem_of_superset hn (fun z hz => ⟨hz,by simpa [A] using hKA z.property⟩)
    rw [← closure_sdiff_intrinsicInterior] at hx
    exact hx.2 hri
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem),hg]
    rfl
  obtain ⟨f,hf,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point C.convex hxnot hint
  have hfx : f x = 0 := by
    have h0 := hmax 0 C.zero_mem
    have h2 := hmax ((2 : ℝ) • x) (C.smul_mem (by norm_num) hxK.1)
    simp only [map_zero,map_smul,smul_eq_mul] at h0 h2
    linarith
  obtain ⟨p,g,hg',hz⟩ := ExclusionBallFaces.positive_support_confirmer hc hs hg
    (g := -f.toLinearMap) (by
      intro he
      apply hf
      ext v
      have hv := LinearMap.congr_fun he v
      simpa using hv) (by
      intro y hy
      have hh := hmax y hy
      change 0 ≤ -f y
      linarith)
  exact ⟨p,hxK,g,hg',hz x (by simpa using hfx)⟩

include hc hs hg hB in
omit [Nontrivial V] in
theorem exclusion_frontier (p : pure C u) :
    exclusion C u p ⊆ intrinsicFrontier ℝ (base C u) := by
  intro x hx
  rw [← closure_sdiff_intrinsicInterior]
  refine ⟨subset_closure hx.1,?_⟩
  rintro ⟨a,ha,he⟩
  obtain ⟨f,hf,hzero⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.2.2.2.2.2
  have hfx : f x = 0 := (hzero ▸ hx).2
  let : Nonempty (affineSpan ℝ (base C u)) := ⟨a⟩
  let b : affineSpan ℝ (base C u) := ⟨p,subset_affineSpan ℝ _ (pure_mem p)⟩
  have hcont : Continuous (fun t : ℝ => AffineMap.lineMap b a t) := AffineMap.lineMap_continuous
  obtain ⟨t,ht,hmem⟩ := hcont.tendsto' 1 a (AffineMap.lineMap_apply_one b a) |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp ha) |>.exists_gt
  have hneg := (hf.1 (AffineMap.lineMap b a t : V) hmem.1).1
  have hline : (AffineMap.lineMap b a t : V) = AffineMap.lineMap (p : V) x t := by
    rw [← he]
    exact (affineSpan ℝ (base C u)).subtype.apply_lineMap b a t
  rw [hline,AffineMap.lineMap_apply_module,map_add,map_smul,map_smul,hf.2,hfx] at hneg
  simp only [smul_eq_mul,mul_one,mul_zero,add_zero] at hneg
  linarith

include hc hs hg hB in
omit [Nontrivial V] in
private theorem mixed_boundary :
    mixedExcluded C u = intrinsicFrontier ℝ (base C u) \ pure C u := by
  ext x
  constructor
  · rintro ⟨hn,p,hp⟩
    exact ⟨exclusion_frontier hc hs hg hB p hp,hn⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hn,frontier_covered hc hs hg hx⟩

include hc hs hg hB hW in
private theorem pure_boundary : pure C u ⊆ intrinsicFrontier ℝ (base C u) := by
  intro p hp
  let p' : pure C u := ⟨p,hp⟩
  obtain ⟨q,r,ht⟩ := (whole_joint_completion hc hs hg hB hW).2.1 p'
  have hpq : p ∈ exclusion C u q :=
    (exclusion_symmetric p' q).mp ⟨pure_mem q,ht.2.2.1⟩
  exact exclusion_frontier hc hs hg hB q hpq

include hc hs hg hB hW in
private theorem label_unique {x : V} (hx : x ∉ pure C u)
    {p q : pure C u} (hp : x ∈ exclusion C u p) (hq : x ∈ exclusion C u q) : p = q := by
  have g := (exclusion_ball_faces hc hs hg hB).1
  let F := exclusion C u p ∩ exclusion C u q
  have hF : IsExtreme ℝ (base C u) F :=
    (g p).2.2.2.2.1.inter (g q).2.2.2.2.1
  have hn : F.Nontrivial := by
    by_contra hn
    have he : F = {x} := (Set.not_nontrivial_iff.mp hn).eq_singleton_of_mem ⟨hp,hq⟩
    apply hx
    exact isExtreme_singleton.mp (he ▸ hF)
  obtain ⟨bp⟩ := hB p
  obtain ⟨bq⟩ := hB q
  have hconv := (g p).2.2.1.inter (g q).2.2.1
  have he := chart_face_eq bp hconv (hF.mono (g p).2.2.2.2.1.subset inter_subset_left) hn
  have he' := chart_face_eq bq hconv (hF.mono (g q).2.2.2.2.1.subset inter_subset_right) hn
  exact ContinuousFrameSum.exclusion_injective hc hs hg hB hW (he.symm.trans he')

/-- The label is chosen from actual original full-effect incidence. -/
def label (x : mixedExcluded C u) : pure C u := x.property.2.choose

include hc hs hg hB hW in
private theorem label_iff (x : mixedExcluded C u) (p : pure C u) :
    label x = p ↔ (x : V) ∈ exclusion C u p := by
  constructor
  · intro he
    exact he ▸ x.property.2.choose_spec
  · intro hp
    exact label_unique hc hs hg hB hW x.property.1 x.property.2.choose_spec hp

include hc hs hg in
omit [Nontrivial V] in
private theorem incidence_closed :
    IsClosed {s : V × pure C u | s.1 ∈ exclusion C u s.2} := by
  let : CompactSpace (effects C u) := isCompact_iff_compactSpace.mp (effects_compact hs hg)
  let Z : Set ((V × pure C u) × effects C u) :=
    {s | s.1.1 ∈ base C u ∧ s.2.1 s.1.2 = 1 ∧ s.2.1 s.1.1 = 0}
  have hZ : IsClosed Z :=
    ((base_compact (C := C) (u := u) hc hs).isClosed.preimage (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))
  have he : {s : V × pure C u | s.1 ∈ exclusion C u s.2} = Prod.fst '' Z := by
    ext s
    constructor
    · rintro ⟨hx,f,hf,hz⟩
      exact ⟨(s,⟨f.toContinuousLinearMap,hf.1⟩),⟨hx,hf.2,hz⟩,rfl⟩
    · rintro ⟨⟨s,f⟩,⟨hx,hf,hz⟩,rfl⟩
      exact ⟨hx,f.1.toLinearMap,⟨f.property,hf⟩,hz⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace Z hZ

include hc hs hg hB hW in
private theorem label_continuous : Continuous (label (C := C) (u := u)) := by
  let : CompactSpace (pure C u) :=
    isCompact_iff_compactSpace.mp (original_pure_compact hc hs hg hB hW)
  apply continuous_of_isClosed_graph
  have he : (label (C := C) (u := u)).graph =
      (fun s : mixedExcluded C u × pure C u => ((s.1 : V),s.2)) ⁻¹'
        {s : V × pure C u | s.1 ∈ exclusion C u s.2} := by
    ext s
    exact label_iff hc hs hg hB hW s.1 s.2
  rw [he]
  exact (incidence_closed hc hs hg).preimage (by fun_prop)

include hc hs hg hB in
omit [Nontrivial V] in
private theorem chart_mixed (p : pure C u) (b : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin b.dim)) :
    b.param v ∈ exclusion C u p ∧ b.param v ∉ pure C u ↔ ‖v‖ < 1 := by
  have hb := OriginalFacePolarity.chart_boundary hc hs hg hB p b
  constructor
  · rintro ⟨hv,hn⟩
    have hle : ‖v‖ ≤ 1 := by
      have := b.injective.mem_set_image.mp (b.whole.symm ▸ hv)
      simpa using this
    apply lt_of_le_of_ne hle
    intro he
    apply hn
    have : b.param v ∈ exclusion C u p ∩ pure C u := by
      rw [hb]
      exact ⟨v,by simpa using he,rfl⟩
    exact this.2
  · intro hv
    refine ⟨b.whole ▸ ⟨v,by simpa using hv.le,rfl⟩,?_⟩
    intro hp
    have hh : b.param v ∈ exclusion C u p ∩ pure C u :=
      ⟨b.whole ▸ ⟨v,by simpa using hv.le,rfl⟩,hp⟩
    rw [hb] at hh
    obtain ⟨w,hw,he⟩ := hh
    have he' := b.injective he
    subst w
    have : ‖v‖ = 1 := by simpa using hw
    linarith

omit [FiniteDimensional ℝ V] [Nontrivial V] in
private theorem chart_intrinsic (p : pure C u) (b : ExclusionChart C u p) :
    intrinsicInterior ℝ (exclusion C u p) = b.param '' Metric.ball 0 1 := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  let A : AffineSubspace ℝ V := (⊤ : AffineSubspace ℝ E).map b.param
  let e : E ≃ᵃ[ℝ] A := (AffineSubspace.topEquiv ℝ E E).symm.trans
    (AffineEquiv.ofBijective (AffineMap.restrict.bijective
      (E := (⊤ : AffineSubspace ℝ E)) b.injective))
  have he (v : E) : (e v : V) = b.param v := rfl
  have himage (T : Set E) : b.param '' T = A.subtypeₐᵢ '' (e '' T) := by
    rw [image_image]
    rfl
  have hint : intrinsicInterior ℝ (Metric.closedBall (0 : E) 1) = Metric.ball 0 1 := by
    have hspan : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ :=
      (convex_closedBall (0 : E) 1).interior_nonempty_iff_affineSpan_eq_top.mp
        ⟨0,by simp [interior_closedBall]⟩
    let B := affineSpan ℝ (Metric.closedBall (0 : E) 1)
    let : Nonempty B := ⟨⟨0,subset_affineSpan ℝ _ (by simp)⟩⟩
    let h := AffineIsometryEquiv.ofTop B hspan
    have hcoe : (h : B → E) = ((↑) : B → E) := by
      funext x
      exact AffineIsometryEquiv.ofTop_apply hspan x
    change ((↑) : B → E) '' interior (((↑) : B → E) ⁻¹' Metric.closedBall 0 1) = _
    rw [← hcoe]
    change h.toHomeomorph '' interior (h.toHomeomorph ⁻¹' Metric.closedBall 0 1) = _
    rw [h.toHomeomorph.image_interior]
    change interior ((h : B → E) '' ((h : B → E) ⁻¹' Metric.closedBall 0 1)) = _
    rw [Set.image_preimage_eq (f := (h : B → E)) _ h.surjective]
    simp [interior_closedBall]
  rw [← b.whole,himage,A.subtypeₐᵢ.intrinsicInterior_image,e.intrinsicInterior_image,hint]
  exact (himage (Metric.ball 0 1)).symm

include hc hs hg hB in
omit [Nontrivial V] in
private theorem exclusion_interior (p : pure C u) :
    intrinsicInterior ℝ (exclusion C u p) = exclusion C u p \ pure C u := by
  let b := (hB p).some
  rw [chart_intrinsic p b]
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (chart_mixed hc hs hg hB p b v).mpr (by simpa using hv)
  · rintro ⟨hx,hn⟩
    obtain ⟨v,hv,rfl⟩ := b.whole.symm ▸ hx
    exact ⟨v,by simpa using (chart_mixed hc hs hg hB p b v).mp ⟨hx,hn⟩,rfl⟩

include hc hs hg hB in
omit [Nontrivial V] in
private theorem center_mixed (p : pure C u) : center hB p ∈ mixedExcluded C u := by
  have hh := (chart_mixed hc hs hg hB p (hB p).some 0).mpr (by simp)
  exact ⟨hh.2,p,hh.1⟩

/-- The actual center section, with its mixed-state membership proved from the ball geometry. -/
def centerSection (p : pure C u) : mixedExcluded C u :=
  ⟨center hB p,center_mixed hc hs hg hB p⟩

include hc hs hg hB hW in
private theorem center_continuous : Continuous (centerSection hc hs hg hB) := by
  apply Continuous.subtype_mk
  have hsum := ((original_continuous_frame_sum hc hs hg hB).1 hW).2.1
  have he : center hB = fun p : pure C u => (1/2 : ℝ) • (sumVector hB p - p) := by
    funext p
    simp [sumVector,smul_smul]
  rw [he]
  exact continuous_const.smul (hsum.sub continuous_subtype_val)

include hc hs hg hB hW in
private theorem label_center (p : pure C u) : label (centerSection hc hs hg hB p) = p := by
  apply (label_iff hc hs hg hB hW _ p).mpr
  exact (chart_mixed hc hs hg hB p (hB p).some 0).mpr (by simp) |>.1

include hc hs hg hB in
omit [Nontrivial V] in
private theorem contraction_mem (x : mixedExcluded C u) (t : Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (x : V) (center hB (label x)) (t : ℝ) ∈ mixedExcluded C u ∧
      AffineMap.lineMap (x : V) (center hB (label x)) (t : ℝ) ∈ exclusion C u (label x) := by
  let p := label x
  let b := (hB p).some
  have hx : (x : V) ∈ exclusion C u p := x.property.2.choose_spec
  obtain ⟨v,hv,he⟩ := b.whole.symm ▸ hx
  have hnorm : ‖v‖ < 1 := (chart_mixed hc hs hg hB p b v).mp
    ⟨he.symm ▸ hx,he.symm ▸ x.property.1⟩
  have hball : AffineMap.lineMap v 0 (t : ℝ) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin b.dim)) 1 :=
    (convex_ball (0 : EuclideanSpace ℝ (Fin b.dim)) 1).lineMap_mem
      (by simpa using hnorm) (by simp) t.property
  have hm := (chart_mixed hc hs hg hB p b (AffineMap.lineMap v 0 (t : ℝ))).mpr
    (by simpa using hball)
  have hmap : b.param (AffineMap.lineMap v 0 (t : ℝ)) =
      AffineMap.lineMap (x : V) (center hB p) (t : ℝ) := by
    rw [b.param.apply_lineMap,he]
    rfl
  rw [hmap] at hm
  exact ⟨⟨hm.2,p,hm.1⟩,hm.1⟩

/-- Straight motion in the original exclusion, without continuous choices of ball charts. -/
def contraction (z : Set.Icc (0 : ℝ) 1 × mixedExcluded C u) : mixedExcluded C u :=
  ⟨AffineMap.lineMap (z.2 : V) (center hB (label z.2)) (z.1 : ℝ),
    (contraction_mem hc hs hg hB z.2 z.1).1⟩

include hc hs hg hB hW in
private theorem contraction_label (t : Set.Icc (0 : ℝ) 1) (x : mixedExcluded C u) :
    label (contraction hc hs hg hB (t,x)) = label x :=
  (label_iff hc hs hg hB hW _ _).mpr (contraction_mem hc hs hg hB x t).2

include hc hs hg hB hW in
private theorem contraction_continuous : Continuous (contraction hc hs hg hB) := by
  apply Continuous.subtype_mk
  simp only [AffineMap.lineMap_apply_module]
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd) |>.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp ((center_continuous hc hs hg hB hW).comp
          ((label_continuous hc hs hg hB hW).comp continuous_snd))))

include hc hs hg hB in
omit [Nontrivial V] in
private theorem reflection_mem (x : mixedExcluded C u) :
    (2 : ℝ) • center hB (label x) - (x : V) ∈ mixedExcluded C u ∧
      (2 : ℝ) • center hB (label x) - (x : V) ∈ exclusion C u (label x) := by
  let p := label x
  let b := (hB p).some
  have hx : (x : V) ∈ exclusion C u p := x.property.2.choose_spec
  obtain ⟨v,hv,he⟩ := b.whole.symm ▸ hx
  have hnorm : ‖v‖ < 1 := (chart_mixed hc hs hg hB p b v).mp
    ⟨he.symm ▸ hx,he.symm ▸ x.property.1⟩
  have hm := (chart_mixed hc hs hg hB p b (-v)).mpr (by simpa using hnorm)
  have hmid : b.param 0 = (1/2 : ℝ) • (b.param v + b.param (-v)) := by
    simpa [midpoint_eq_smul_add] using b.param.map_midpoint v (-v)
  have hmap : b.param (-v) = (2 : ℝ) • center hB p - (x : V) := by
    change b.param (-v) = (2 : ℝ) • b.param 0 - (x : V)
    rw [hmid,he,smul_smul]
    module
  rw [hmap] at hm
  exact ⟨⟨hm.2,p,hm.1⟩,hm.1⟩

/-- Reflection in the actual center of the uniquely determined exclusion ball. -/
def reflection (x : mixedExcluded C u) : mixedExcluded C u :=
  ⟨(2 : ℝ) • center hB (label x) - (x : V),(reflection_mem hc hs hg hB x).1⟩

include hc hs hg hB hW in
private theorem reflection_label (x : mixedExcluded C u) :
    label (reflection hc hs hg hB x) = label x :=
  (label_iff hc hs hg hB hW _ _).mpr (reflection_mem hc hs hg hB x).2

include hc hs hg hB hW in
private theorem reflection_laws :
    Continuous (reflection hc hs hg hB) ∧
    Function.Involutive (reflection hc hs hg hB) ∧
    (∀ x : mixedExcluded C u, reflection hc hs hg hB x = x ↔
      x ∈ Set.range (centerSection hc hs hg hB)) := by
  refine ⟨?_,?_,?_⟩
  · apply Continuous.subtype_mk
    exact (continuous_const.smul (continuous_subtype_val.comp
      ((center_continuous hc hs hg hB hW).comp (label_continuous hc hs hg hB hW)))).sub
        continuous_subtype_val
  · intro x
    apply Subtype.ext
    change (2 : ℝ) • center hB (label (reflection hc hs hg hB x)) -
      ((2 : ℝ) • center hB (label x) - (x : V)) = _
    rw [reflection_label hc hs hg hB hW]
    abel
  · intro x
    constructor
    · intro he
      refine ⟨label x,?_⟩
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change (2 : ℝ) • center hB (label x) - (x : V) = (x : V) at hh
      have hh' : (2 : ℝ) • center hB (label x) = (2 : ℝ) • (x : V) := by
        rw [sub_eq_iff_eq_add] at hh
        simpa [two_smul] using hh
      exact (smul_right_injective V (by norm_num : (2 : ℝ) ≠ 0)) hh'
    · rintro ⟨p,rfl⟩
      apply Subtype.ext
      change (2 : ℝ) • center hB (label (centerSection hc hs hg hB p)) - center hB p = _
      rw [label_center hc hs hg hB hW]
      simp [two_smul,centerSection]

include hc hs hg hB hW in
/-- The actual contraction preserves every complete mixed fiber and its complement. -/
theorem original_mixed_exclusion_contraction :
    (pure C u ⊆ intrinsicFrontier ℝ (base C u)) ∧
    mixedExcluded C u = intrinsicFrontier ℝ (base C u) \ pure C u ∧
    (∀ (x : mixedExcluded C u) (p : pure C u), label x = p ↔
      (x : V) ∈ intrinsicInterior ℝ (exclusion C u p)) ∧
    Continuous (reflection hc hs hg hB) ∧
    Function.Involutive (reflection hc hs hg hB) ∧
    (∀ x : mixedExcluded C u, reflection hc hs hg hB x = x ↔
      x ∈ Set.range (centerSection hc hs hg hB)) ∧
    Continuous (label (C := C) (u := u)) ∧
    Continuous (centerSection hc hs hg hB) ∧
    (∀ p : pure C u, label (centerSection hc hs hg hB p) = p) ∧
    Continuous (contraction hc hs hg hB) ∧
    (∀ x : mixedExcluded C u,
      contraction hc hs hg hB (⟨0,by norm_num⟩,x) = x ∧
      contraction hc hs hg hB (⟨1,by norm_num⟩,x) = centerSection hc hs hg hB (label x)) ∧
    (∀ (p : pure C u) (t : Set.Icc (0 : ℝ) 1),
      contraction hc hs hg hB (t,centerSection hc hs hg hB p) = centerSection hc hs hg hB p) ∧
    (∀ (p : pure C u) (t : Set.Icc (0 : ℝ) 1) (x : mixedExcluded C u),
      ((contraction hc hs hg hB (t,x) : mixedExcluded C u) : V) ∈ exclusion C u p ↔
        (x : V) ∈ exclusion C u p) := by
  have hri (x : mixedExcluded C u) (p : pure C u) : label x = p ↔
      (x : V) ∈ intrinsicInterior ℝ (exclusion C u p) := by
    rw [exclusion_interior hc hs hg hB,label_iff hc hs hg hB hW]
    exact ⟨fun h => ⟨h,x.property.1⟩,fun h => h.1⟩
  refine ⟨pure_boundary hc hs hg hB hW,mixed_boundary hc hs hg hB,hri,
    (reflection_laws hc hs hg hB hW).1,(reflection_laws hc hs hg hB hW).2.1,
    (reflection_laws hc hs hg hB hW).2.2,
    label_continuous hc hs hg hB hW,center_continuous hc hs hg hB hW,
    label_center hc hs hg hB hW,contraction_continuous hc hs hg hB hW,?_,?_,?_⟩
  · intro x
    constructor <;> apply Subtype.ext <;> simp [contraction,centerSection]
  · intro p t
    apply Subtype.ext
    change AffineMap.lineMap (center hB p) (center hB (label (centerSection hc hs hg hB p))) _ = _
    rw [label_center hc hs hg hB hW]
    simp [centerSection]
  · intro p t x
    rw [← label_iff hc hs hg hB hW,← label_iff hc hs hg hB hW,
      contraction_label hc hs hg hB hW]

/-- The endpoint of the contraction as a continuous self-map of the mixed boundary. -/
def centerRetraction : C(mixedExcluded C u,mixedExcluded C u) :=
  ⟨fun x => centerSection hc hs hg hB (label x),
    (center_continuous hc hs hg hB hW).comp (label_continuous hc hs hg hB hW)⟩

/-- The actual straight-line strong deformation as a homotopy of continuous maps. -/
def contractionHomotopy : (ContinuousMap.id (mixedExcluded C u)).Homotopy
    (centerRetraction hc hs hg hB hW) where
  toFun := contraction hc hs hg hB
  continuous_toFun := contraction_continuous hc hs hg hB hW
  map_zero_left x := by apply Subtype.ext; simp [contraction]
  map_one_left x := by apply Subtype.ext; simp [contraction,centerRetraction,centerSection]

/-- The genuine pair obtained by deleting one complete mixed exclusion fiber. -/
private def incidencePair (p : pure C u) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (mixedExcluded C u))
    {x | (x : V) ∉ exclusion C u p}

/-- The actual punctured pure-point pair. -/
def deletedPointPair (p : pure C u) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (pure C u)) {q | q ≠ p}

open CategoryTheory

/-- The unique original labels give a continuous map of the deleted pairs. -/
private def incidenceLabelMap (p : pure C u) : incidencePair p ⟶ deletedPointPair p :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨label,label_continuous hc hs hg hB hW⟩) (by
    intro x hx he
    exact hx ((label_iff hc hs hg hB hW x p).mp he))

/-- The actual center section gives a map back to the deleted mixed-boundary pair. -/
private def incidenceCenterMap (p : pure C u) : deletedPointPair p ⟶ incidencePair p :=
  TopPair.ofSubsetMap (TopCat.ofHom
    ⟨centerSection hc hs hg hB,center_continuous hc hs hg hB hW⟩) (by
      intro q hq hm
      exact hq ((label_center hc hs hg hB hW q).symm.trans
        ((label_iff hc hs hg hB hW _ p).mpr hm)))

/-- The center contraction joins the identity to the composite of the actual pair maps. -/
private def incidencePairHomotopy (p : pure C u) :
    TopPair.Homotopy (𝟙 (incidencePair p))
      (incidenceLabelMap hc hs hg hB hW p ≫ incidenceCenterMap hc hs hg hB hW p) := by
  have H := TopPair.ofSubsetHomotopy
    (X := TopCat.of (mixedExcluded C u)) (Y := TopCat.of (mixedExcluded C u))
    (B := {x | (x : V) ∉ exclusion C u p})
    (B' := {x | (x : V) ∉ exclusion C u p})
    (g₀ := TopCat.ofHom (ContinuousMap.id (mixedExcluded C u)))
    (g₁ := TopCat.ofHom (centerRetraction hc hs hg hB hW))
    (contractionHomotopy hc hs hg hB hW) (by
      intro t x hx hm
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hpres⟩ :=
        original_mixed_exclusion_contraction hc hs hg hB hW
      exact hx ((hpres p t x).mp hm))
  convert H using 1 <;> rfl


/-- Delete one full exclusion from the literal nonpure intrinsic boundary of the original base. -/
def deletedFiberPair (p : pure C u) : TopPair :=
  TopPair.ofSubset (X := TopCat.of ↥(intrinsicFrontier ℝ (base C u) \ pure C u))
    {x | (x : V) ∉ exclusion C u p}

private def boundaryPairIso (p : pure C u) : deletedFiberPair p ≅ incidencePair p :=
  TopPair.ofSubsetIso (Homeomorph.setCongr (mixed_boundary hc hs hg hB).symm)
    (by intro x; rfl)

/-- The incidence-derived label on every actual nonpure relative-boundary point. -/
def pairLabelMap (p : pure C u) : deletedFiberPair p ⟶ deletedPointPair p :=
  (boundaryPairIso hc hs hg hB p).hom ≫ incidenceLabelMap hc hs hg hB hW p

/-- The actual centers as a map back to the literal mixed-boundary pair. -/
def pairCenterMap (p : pure C u) : deletedPointPair p ⟶ deletedFiberPair p :=
  incidenceCenterMap hc hs hg hB hW p ≫ (boundaryPairIso hc hs hg hB p).inv

/-- The actual center contraction on the original boundary with a complete fiber deleted. -/
def deletedFiberPairHomotopy (p : pure C u) :
    TopPair.Homotopy (𝟙 (deletedFiberPair p))
      (pairLabelMap hc hs hg hB hW p ≫ pairCenterMap hc hs hg hB hW p) := by
  let e := boundaryPairIso hc hs hg hB p
  have H := (TopPair.Homotopy.refl e.inv).comp
    ((incidencePairHomotopy hc hs hg hB hW p).comp (TopPair.Homotopy.refl e.hom))
  change TopPair.Homotopy (𝟙 _)
    ((e.hom ≫ incidenceLabelMap hc hs hg hB hW p) ≫
      (incidenceCenterMap hc hs hg hB hW p ≫ e.inv))
  simpa only [Category.assoc, Category.comp_id, Iso.hom_inv_id] using H

end D5.S3.Quantum.Foundation.MixedExclusionGeometry
