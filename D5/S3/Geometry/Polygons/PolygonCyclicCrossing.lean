/- GID: D5/S3/Geometry/Polygons/PolygonCyclicCrossing
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonCyclicCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polygon boundary edges propagate strict chord sides along cyclic arcs. -/

import D5.S3.Geometry.Polygons.PolygonFilledBoundary
import D5.S3.Geometry.Polygons.PolygonCatalanSupplier
import Mathlib.Analysis.Convex.Side

/-! Strict sides along the actual cyclic boundary chains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Module

namespace D5.S3.Geometry.Polygons.PolygonCyclicCrossing
open PolygonInteriorDiagonals PolygonFilledBoundary PolygonEarSlide
open ClusterAlgebras.TypeA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} [NeZero n]

private theorem line_section {K : Set E} {a b z : E} (hab : a ≠ b)
    (ha : a ∈ K.extremePoints ℝ) (hb : b ∈ K.extremePoints ℝ)
    (hz : z ∈ K) (hl : z ∈ line[ℝ, a, b]) : z ∈ segment ℝ a b := by
  have hc : Collinear ℝ ({a,z,b} : Set E) := by
    convert collinear_insert_of_mem_affineSpan_pair hl using 1
    ext x
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto
  rcases hc.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact mem_segment_iff_wbtw.mpr h
  · rcases (mem_extremePoints_iff_forall_segment.mp hb).2 z hz a ha.1
      (mem_segment_iff_wbtw.mpr h) with h | h
    · simpa only [h] using right_mem_segment ℝ a b
    · exact (hab h).elim
  · rcases (mem_extremePoints_iff_forall_segment.mp ha).2 b hb.1 z hz
      (mem_segment_iff_wbtw.mpr h) with h | h
    · exact (hab h.symm).elim
    · simpa only [h] using left_mem_segment ℝ a b

private theorem vertex_extreme {poly : Polygon E n} (B : BoundaryModel poly) (i : ZMod n) :
    vertex poly i ∈ (convexHull ℝ (range poly.vertices)).extremePoints ℝ :=
  B.extreme_vertices _

private theorem boundary_edge {poly : Polygon E n} (B : BoundaryModel poly)
    (k : ZMod n) : segment ℝ (vertex poly k) (vertex poly (k+1)) ⊆
      frontier (convexHull ℝ (range poly.vertices)) := by
  intro z hz
  rw [← B.boundary_eq]
  apply mem_iUnion.mpr
  refine ⟨(ZMod.finEquiv n).symm k,?_⟩
  simpa only [Polygon.edgeSet,affineSegment_eq_segment,← vertex_succ,vertex] using hz

private theorem edge_sign [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    (hn : 3 ≤ n) {poly : Polygon E n} (B : BoundaryModel poly)
    {a b k : ZMod n} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hfab : f (vertex poly b) = f (vertex poly a)) :
    ¬ (f (vertex poly k) - f (vertex poly a)) *
      (f (vertex poly (k+1)) - f (vertex poly a)) < 0 := by
  intro hmul
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  have hroot : f (vertex poly a) ∈
      openSegment ℝ (f (vertex poly k)) (f (vertex poly (k+1))) := by
    rcases mul_neg_iff.mp hmul with h | h
    · rw [openSegment_symm,openSegment_eq_Ioo (by linarith : f (vertex poly (k+1)) < f (vertex poly k))]
      exact ⟨by linarith,by linarith⟩
    · rw [openSegment_eq_Ioo
        (by linarith : f (vertex poly k) < f (vertex poly (k+1)))]
      exact ⟨by linarith,by linarith⟩
  have himage := image_openSegment ℝ f.toLinearMap.toAffineMap (vertex poly k) (vertex poly (k+1))
  change f '' openSegment ℝ (vertex poly k) (vertex poly (k+1)) =
    openSegment ℝ (f (vertex poly k)) (f (vertex poly (k+1))) at himage
  rw [← himage] at hroot
  obtain ⟨z,hz,hfz⟩ := hroot
  have ha := vertex_extreme B a
  have hb := vertex_extreme B b
  have hk := vertex_extreme B k
  have hk' := vertex_extreme B (k+1)
  have hzK := (convex_convexHull ℝ (range poly.vertices)).openSegment_subset hk.1 hk'.1 hz
  have hzline := level_mem_line hdim (hv.ne hab) f hf hfab hfz
  have hzseg := line_section (hv.ne hab) ha hb hzK hzline
  have hzne (j : ZMod n) (hkj : k ≠ j) : vertex poly j ≠ z := by
    intro he
    have hx := (mem_extremePoints.mp (vertex_extreme B j)).2
      (vertex poly k) hk.1 (vertex poly (k+1)) hk'.1 (he ▸ hz)
    exact (hv.ne hkj) hx.1
  have hzopen := mem_openSegment_of_ne_left_right (hzne a hka) (hzne b hkb) hzseg
  have hzfront := boundary_edge B k (openSegment_subset_segment ℝ _ _ hz)
  by_cases hD : Carrier.IsDiagonal s(a,b)
  · have hzint := ((isDiagonal_iff_openSegment_subset_interior hdim hn poly B a b).mp hD).2 hzopen
    exact (disjoint_left.mp disjoint_interior_frontier) hzint hzfront
  · have hznot : z ∉ interior (convexHull ℝ (range poly.vertices)) :=
      fun hi => (disjoint_left.mp disjoint_interior_frontier) hi hzfront
    obtain ⟨g,hg,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
      (convex_convexHull ℝ _) hznot (interior_nonempty hdim hn B)
    obtain ⟨hga,hgb⟩ := maximal_endpoints ha.1 hb.1 hzopen g hmax
    obtain ⟨hgk,_⟩ := maximal_endpoints hk.1 hk'.1 hz g hmax
    rcases common_level_only_two hdim ha hb hk (hv.ne hab) g hg
      (hgb.trans hga.symm) (hgk.trans hga.symm) with h | h
    · exact hka (hv h)
    · exact hkb (hv h)

private theorem arc_constant (P : ZMod n → Prop) {a b : ZMod n}
    (step : ∀ k, sbtw a k b → sbtw a (k+1) b → (P k ↔ P (k+1)))
    {c d : ZMod n} (hc : sbtw a c b) (hd : sbtw a d b) : P c ↔ P d := by
  let L := (b-a).val
  let w := fun k : ℕ => a + (k : ZMod n)
  have pos (x : ZMod n) : basePos a x = ((x-a).val : ℤ) := rfl
  have apos : basePos a a = 0 := by simp [basePos]
  have arc (x : ZMod n) : sbtw a x b ↔ 0 < (x-a).val ∧ (x-a).val < L := by
    rw [sbtw_iff_sbtw_basePos a,Int.sbtw_iff,apos,pos,pos]
    have hx := basePos_nonneg a x
    have hb := basePos_nonneg a b
    dsimp [L]
    omega
  have hw (k : ℕ) (hk : k < n) : (w k-a).val = k := by
    dsimp [w]
    rw [add_sub_cancel_left,ZMod.val_natCast_of_lt hk]
  have hpath : ∀ t, 1 ≤ t → t < L → (P (w 1) ↔ P (w t)) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; exact Iff.rfl
    | succ t ht ih =>
      intro htl
      have htn : t+1 < n := lt_trans htl (ZMod.val_lt (b-a))
      have htw : w (t+1) = w t+1 := by simp [w,Nat.cast_add,add_assoc]
      refine (ih (by omega)).trans ?_
      rw [htw]
      apply step
      · apply (arc _).mpr
        rw [hw t (by omega)]
        omega
      · apply (arc _).mpr
        rw [← htw,hw (t+1) htn]
        omega
  have hcw : w (c-a).val = c := by simp [w]
  have hdw : w (d-a).val = d := by simp [w]
  have hc' := (arc c).mp hc
  have hd' := (arc d).mp hd
  have h1 := hpath (c-a).val (by omega) hc'.2
  have h2 := hpath (d-a).val (by omega) hd'.2
  rw [hcw] at h1
  rw [hdw] at h2
  exact h1.symm.trans h2

/-- The actual boundary successor chain keeps every open cyclic arc on one strict chord side. -/
theorem same_arc_sign (hdim : finrank ℝ E = 2) (hn : 3 ≤ n)
    (poly : Polygon E n) (B : BoundaryModel poly) {a b c d : ZMod n}
    (hab : a ≠ b) (hc : sbtw a c b) (hd : sbtw a d b)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hfab : f (vertex poly b) = f (vertex poly a)) :
    (f (vertex poly c) - f (vertex poly a)) *
      (f (vertex poly d) - f (vertex poly a)) > 0 := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  have ha := vertex_extreme B a
  have hb := vertex_extreme B b
  have hnz (k : ZMod n) (hk : sbtw a k b) :
      f (vertex poly k) - f (vertex poly a) ≠ 0 := by
    intro hz
    rcases common_level_only_two hdim ha hb (vertex_extreme B k) (hv.ne hab) f hf hfab
      (sub_eq_zero.mp hz) with he | he
    · have hka : k ≠ a := fun he => by subst k; exact sbtw_irrefl_left hk
      exact hka (hv he)
    · have hkb : k ≠ b := fun he => by subst k; exact sbtw_irrefl_right hk
      exact hkb (hv he)
  have hsign : (0 < f (vertex poly c) - f (vertex poly a)) ↔
      (0 < f (vertex poly d) - f (vertex poly a)) := by
    apply arc_constant _ (c := c) (d := d) _ hc hd
    intro k hk hk'
    have hka : k ≠ a := fun he => by subst k; exact sbtw_irrefl_left hk
    have hkb : k ≠ b := fun he => by subst k; exact sbtw_irrefl_right hk
    have hm := edge_sign hdim hn B hab hka hkb f hf hfab
    have h0 := hnz k hk
    have h1 := hnz (k+1) hk'
    constructor
    · intro h
      by_contra! hh
      exact hm (mul_neg_of_pos_of_neg h (lt_of_le_of_ne hh h1))
    · intro h
      by_contra! hh
      exact hm (mul_neg_of_neg_of_pos (lt_of_le_of_ne hh h0) h)
  rcases lt_or_gt_of_ne (hnz c hc) with h | h
  · have hdneg : f (vertex poly d) - f (vertex poly a) < 0 := by
      have := mt hsign.mpr (not_lt.mpr h.le)
      exact lt_of_le_of_ne (not_lt.mp this) (hnz d hd)
    exact mul_pos_of_neg_of_neg h hdneg
  · exact mul_pos h (hsign.mp h)

private theorem arc_cases {a b k : ZMod n} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    sbtw a k b ∨ sbtw b k a := by
  have h1 := (ZMod.val_injective n).ne hab
  have h2 := (ZMod.val_injective n).ne hka
  have h3 := (ZMod.val_injective n).ne hkb
  rw [sbtw_iff_val,sbtw_iff_val]
  omega

private theorem no_short_arc (hn : 3 ≤ n) (a k : ZMod n) : ¬ sbtw a k (a+1) := by
  rw [sbtw_iff_sbtw_basePos a,Int.sbtw_iff,basePos_add_one]
  have ha : basePos a a = 0 := by simp [basePos]
  have hk := basePos_nonneg a k
  rw [ha,if_neg (by omega)]
  omega

private theorem not_two_positive_arcs [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = 2) (hn : 3 ≤ n) {poly : Polygon E n} (B : BoundaryModel poly)
    {a b c d : ZMod n} (hab : a ≠ b) (hc : sbtw a c b) (hd : sbtw b d a)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (hfab : f (vertex poly b) = f (vertex poly a))
    (hfc : 0 < f (vertex poly c) - f (vertex poly a))
    (hfd : 0 < f (vertex poly d) - f (vertex poly a)) : False := by
  have hvertices (k : ZMod n) : f (vertex poly a) ≤ f (vertex poly k) := by
    by_cases hka : k = a
    · simp [hka]
    by_cases hkb : k = b
    · simp [hkb,hfab]
    rcases arc_cases hab hka hkb with hk | hk
    · have hp := same_arc_sign hdim hn poly B hab hc hk f hf hfab
      nlinarith
    · have hp := same_arc_sign hdim hn poly B hab.symm hd hk f hf hfab.symm
      rw [hfab] at hp
      nlinarith
  have hmin : ∀ x ∈ convexHull ℝ (range poly.vertices), f (vertex poly a) ≤ f x := by
    apply convexHull_min _ (convex_halfSpace_ge f.toLinearMap.isLinear (f (vertex poly a)))
    rintro x ⟨i,rfl⟩
    change f (vertex poly a) ≤ f (poly i)
    simpa only [vertex,RingEquiv.symm_apply_apply] using hvertices (ZMod.finEquiv n i)
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  have hadj := supporting_pair_is_side hdim B ((ZMod.finEquiv n).symm.injective.ne hab)
    (-f) (neg_ne_zero.mpr hf) (by intro x hx; simpa only [neg_apply,neg_le_neg_iff,vertex] using hmin x hx)
    (by simpa only [neg_apply,vertex] using congrArg Neg.neg hfab)
  rcases hadj with hadj | hadj
  · have he : b = a+1 := hv (by
      change poly ((ZMod.finEquiv n).symm b) = vertex poly (a+1)
      rw [hadj,vertex_succ])
    exact no_short_arc hn a c (he ▸ hc)
  · have he : a = b+1 := hv (by
      change poly ((ZMod.finEquiv n).symm a) = vertex poly (b+1)
      rw [hadj,vertex_succ])
    exact no_short_arc hn b d (he ▸ hd)

private theorem opposite_arc_sign [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = 2) (hn : 3 ≤ n) {poly : Polygon E n} (B : BoundaryModel poly)
    {a b c d : ZMod n} (hab : a ≠ b) (hc : sbtw a c b) (hd : sbtw b d a)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (hfab : f (vertex poly b) = f (vertex poly a)) :
    (f (vertex poly c)-f (vertex poly a)) *
      (f (vertex poly d)-f (vertex poly a)) < 0 := by
  have hc0 := same_arc_sign hdim hn poly B hab hc hc f hf hfab
  have hd0 := same_arc_sign hdim hn poly B hab.symm hd hd f hf hfab.symm
  rw [hfab] at hd0
  by_contra! hnonneg
  rcases lt_trichotomy (f (vertex poly c)-f (vertex poly a)) 0 with hcneg | hcz | hcpos
  · have hdneg : f (vertex poly d)-f (vertex poly a) < 0 := by nlinarith
    exact not_two_positive_arcs hdim hn B hab hc hd (-f) (neg_ne_zero.mpr hf)
      (by simpa only [neg_apply,vertex] using congrArg Neg.neg hfab)
      (by simpa only [neg_apply] using (show 0 < -f (vertex poly c) - -f (vertex poly a) by linarith))
      (by simpa only [neg_apply] using (show 0 < -f (vertex poly d) - -f (vertex poly a) by linarith))
  · nlinarith
  · have hdpos : 0 < f (vertex poly d)-f (vertex poly a) := by nlinarith
    exact not_two_positive_arcs hdim hn B hab hc hd f hf hfab hcpos hdpos

private theorem scalar_cross_iff [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = 2) (hn : 3 ≤ n) {poly : Polygon E n} (B : BoundaryModel poly)
    {a b c d : ZMod n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (hfab : f (vertex poly b) = f (vertex poly a)) :
    (f (vertex poly c)-f (vertex poly a)) * (f (vertex poly d)-f (vertex poly a)) < 0 ↔
      Carrier.Cross s(a,b) s(c,d) := by
  change _ ↔ ClusterAlgebras.Cross s(a,b) s(c,d)
  rw [cross_mk_iff]
  constructor
  · intro hneg
    rcases arc_cases hab hca hcb with hc | hc <;>
      rcases arc_cases hab hda hdb with hd | hd
    · have := same_arc_sign hdim hn poly B hab hc hd f hf hfab
      linarith
    · exact Or.inl ⟨hc,hd⟩
    · exact Or.inr ⟨hd,hc⟩
    · have := same_arc_sign hdim hn poly B hab.symm hc hd f hf hfab.symm
      rw [hfab] at this
      linarith
  · rintro (⟨hc,hd⟩ | ⟨hd,hc⟩)
    · exact opposite_arc_sign hdim hn B hab hc hd f hf hfab
    · rw [mul_comm]
      exact opposite_arc_sign hdim hn B hab hd hc f hf hfab

private theorem chord_functional [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    (a b : E) : ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ f b = f a := by
  have hlt : (ℝ ∙ (b-a) : Submodule ℝ E) < ⊤ :=
    span_lt_top_of_card_lt_finrank (by simp [hdim])
  obtain ⟨g,hg,hker⟩ := (ℝ ∙ (b-a) : Submodule ℝ E).exists_le_ker_of_lt_top hlt
  refine ⟨g.toContinuousLinearMap,?_,?_⟩
  · intro hzero
    apply hg
    ext x
    exact congrArg (fun f : E →L[ℝ] ℝ => f x) hzero
  · have hz := hker (Submodule.subset_span (by simp : b-a ∈ ({b-a} : Set E)))
    change g (b-a) = 0 at hz
    simpa only [LinearMap.coe_toContinuousLinearMap',map_sub,sub_eq_zero] using hz

private theorem level_of_mem_line {a b x : E} (f : E →L[ℝ] ℝ)
    (hfb : f b = f a) (hx : x ∈ line[ℝ, a, b]) : f x = f a := by
  obtain ⟨t,rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  simp only [AffineMap.lineMap_apply_module,map_add,map_smul,hfb,smul_eq_mul]
  ring

private theorem scalar_side_iff [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {a b c d : E} (hab : a ≠ b) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hfb : f b = f a) (hfc : f c ≠ f a) (hfd : f d ≠ f a) :
    line[ℝ, a, b].SOppSide c d ↔ (f c-f a)*(f d-f a) < 0 := by
  constructor
  · intro hs
    obtain ⟨z,hzl,hbet⟩ := hs.exists_sbtw
    have hfz := level_of_mem_line f hfb hzl
    have hm := (hbet.wbtw.map f.toLinearMap.toAffineMap).mem_segment
    change f z ∈ segment ℝ (f c) (f d) at hm
    rw [hfz,segment_eq_uIcc,mem_uIcc] at hm
    rcases hm with hm | hm <;> rcases hm with ⟨h1,h2⟩
    · exact mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_le_of_ne h1 hfc))
        (sub_pos.mpr (lt_of_le_of_ne h2 hfd.symm))
    · exact mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_le_of_ne h2 hfc.symm))
        (sub_neg.mpr (lt_of_le_of_ne h1 hfd))
  · intro hm
    have hroot : f a ∈ openSegment ℝ (f c) (f d) := by
      rcases mul_neg_iff.mp hm with h | h
      · rw [openSegment_symm,openSegment_eq_Ioo (by linarith : f d < f c)]
        exact ⟨by linarith,by linarith⟩
      · rw [openSegment_eq_Ioo (by linarith : f c < f d)]
        exact ⟨by linarith,by linarith⟩
    have himage := image_openSegment ℝ f.toLinearMap.toAffineMap c d
    change f '' openSegment ℝ c d = openSegment ℝ (f c) (f d) at himage
    rw [← himage] at hroot
    obtain ⟨z,hz,hfz⟩ := hroot
    have hzc : z ≠ c := fun he => hfc (he ▸ hfz)
    have hzd : z ≠ d := fun he => hfd (he ▸ hfz)
    have hbet : Sbtw ℝ c z d :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ c d hz),hzc,hzd⟩
    exact hbet.sOppSide_of_notMem_of_mem
      (fun hl => hfc (level_of_mem_line f hfb hl))
      (level_mem_line hdim hab f hf hfb hfz)

/-- Actual line sides are exactly native cyclic alternation, including the empty short arc. -/
theorem sOppSide_iff_cross (hdim : finrank ℝ E = 2) (hn : 3 ≤ n)
    (poly : Polygon E n) (B : BoundaryModel poly) {a b c d : ZMod n}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    line[ℝ, vertex poly a, vertex poly b].SOppSide (vertex poly c) (vertex poly d) ↔
      Carrier.Cross s(a,b) s(c,d) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  obtain ⟨f,hf,hfab⟩ := chord_functional hdim (vertex poly a) (vertex poly b)
  have hnz (k : ZMod n) (hka : k ≠ a) (hkb : k ≠ b) :
      f (vertex poly k) ≠ f (vertex poly a) := by
    intro he
    rcases common_level_only_two hdim (vertex_extreme B a) (vertex_extreme B b)
      (vertex_extreme B k) (hv.ne hab) f hf hfab he with he | he
    · exact hka (hv he)
    · exact hkb (hv he)
  exact (scalar_side_iff hdim (hv.ne hab) f hf hfab (hnz c hca hcb) (hnz d hda hdb)).trans
    (scalar_cross_iff hdim hn B hab hca hcb hda hdb f hf hfab)

/-- Proper geometric crossing uses only actual distinct endpoints and open chord intersection.
No cyclic order or native crossing predicate occurs in this definition. -/
def ProperCross (poly : Polygon E n) (e f : Sym2 (ZMod n)) : Prop :=
  ∃ a b c d : ZMod n, e = s(a,b) ∧ f = s(c,d) ∧
    vertex poly a ≠ vertex poly b ∧ vertex poly c ≠ vertex poly d ∧
    Disjoint ({vertex poly a,vertex poly b} : Set E) {vertex poly c,vertex poly d} ∧
    (openSegment ℝ (vertex poly a) (vertex poly b) ∩
      openSegment ℝ (vertex poly c) (vertex poly d)).Nonempty

private theorem strict_segment_of_extreme {poly : Polygon E n} (B : BoundaryModel poly)
    {a b c d : ZMod n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {z : E} (hz : z ∈ openSegment ℝ (vertex poly c) (vertex poly d))
    (hzl : z ∈ line[ℝ, vertex poly a, vertex poly b]) :
    z ∈ openSegment ℝ (vertex poly a) (vertex poly b) := by
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  have ha := vertex_extreme B a
  have hb := vertex_extreme B b
  have hc := vertex_extreme B c
  have hd := vertex_extreme B d
  have hzK := (convex_convexHull ℝ _).openSegment_subset hc.1 hd.1 hz
  have hzseg := line_section (hv.ne hab) ha hb hzK hzl
  have hzne (k : ZMod n) (hck : c ≠ k) : vertex poly k ≠ z := by
    intro he
    have hh := (mem_extremePoints.mp (vertex_extreme B k)).2
      (vertex poly c) hc.1 (vertex poly d) hd.1 (he ▸ hz)
    exact (hv.ne hck) hh.1
  exact mem_openSegment_of_ne_left_right (hzne a hca) (hzne b hcb) hzseg

/-- Exact correspondence on every native unordered vertex pair, including all degeneracies. -/
theorem cross_iff_properCross (hdim : finrank ℝ E = 2) (hn : 3 ≤ n)
    (poly : Polygon E n) (B : BoundaryModel poly) (e f : Sym2 (ZMod n)) :
    Carrier.Cross e f ↔ ProperCross poly e f := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  have hv : Function.Injective (vertex poly) :=
    B.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  constructor
  · rintro ⟨a,b,c,d,rfl,rfl,hc,hd⟩
    have hab : a ≠ b := fun he => by subst b; exact sbtw_irrefl_left_right hc
    have hca : c ≠ a := fun he => by subst c; exact sbtw_irrefl_left hc
    have hcb : c ≠ b := fun he => by subst c; exact sbtw_irrefl_right hc
    have hda : d ≠ a := fun he => by subst d; exact sbtw_irrefl_right hd
    have hdb : d ≠ b := fun he => by subst d; exact sbtw_irrefl_left hd
    have hcd : c ≠ d := by
      intro he
      rw [he] at hc
      exact sbtw_asymm hc hd
    have hs := (sOppSide_iff_cross hdim hn poly B hab hca hcb hda hdb).mpr
      ⟨a,b,c,d,rfl,rfl,hc,hd⟩
    obtain ⟨z,hzl,hbet⟩ := hs.exists_sbtw
    have hzcd := mem_openSegment_of_ne_left_right hbet.2.1.symm hbet.2.2.symm hbet.wbtw.mem_segment
    refine ⟨a,b,c,d,rfl,rfl,hv.ne hab,hv.ne hcd,?_,z,?_,hzcd⟩
    · rw [Set.disjoint_left]
      intro x hx hy
      simp only [mem_insert_iff,mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with he | he
      · exact (hv.ne hca) he.symm
      · exact (hv.ne hda) he.symm
      · exact (hv.ne hcb) he.symm
      · exact (hv.ne hdb) he.symm
    · exact strict_segment_of_extreme B hab hca hcb hzcd hzl
  · rintro ⟨a,b,c,d,rfl,rfl,hab,hcd,hdis,z,hza,hzc⟩
    have hca : c ≠ a := fun he => Set.disjoint_left.mp hdis
      (by simp : vertex poly a ∈ ({vertex poly a,vertex poly b} : Set E)) (by simp [he])
    have hcb : c ≠ b := fun he => Set.disjoint_left.mp hdis
      (by simp : vertex poly b ∈ ({vertex poly a,vertex poly b} : Set E)) (by simp [he])
    have hda : d ≠ a := fun he => Set.disjoint_left.mp hdis
      (by simp : vertex poly a ∈ ({vertex poly a,vertex poly b} : Set E)) (by simp [he])
    have hdb : d ≠ b := fun he => Set.disjoint_left.mp hdis
      (by simp : vertex poly b ∈ ({vertex poly a,vertex poly b} : Set E)) (by simp [he])
    have hzl : z ∈ line[ℝ, vertex poly a, vertex poly b] :=
      AffineSubspace.mem_of_wbtw
        (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ _ _ hza))
        (left_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)
    have hnot : vertex poly c ∉ line[ℝ, vertex poly a, vertex poly b] := by
      intro hl
      obtain ⟨g,hg,hgab⟩ := chord_functional hdim (vertex poly a) (vertex poly b)
      have he := level_of_mem_line g hgab hl
      rcases common_level_only_two hdim (vertex_extreme B a) (vertex_extreme B b)
        (vertex_extreme B c) hab g hg hgab he with he | he
      · exact hca (hv he)
      · exact hcb (hv he)
    have hzc_ne (k : ZMod n) : z ≠ vertex poly k := by
      intro he
      have hh := (mem_extremePoints.mp (vertex_extreme B k)).2
        (vertex poly c) (vertex_extreme B c).1 (vertex poly d) (vertex_extreme B d).1 (he ▸ hzc)
      exact hcd (hh.1.trans hh.2.symm)
    have hbet : Sbtw ℝ (vertex poly c) z (vertex poly d) :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ _ _ hzc),hzc_ne c,hzc_ne d⟩
    exact (sOppSide_iff_cross hdim hn poly B (fun he => hab (congrArg (vertex poly) he)) hca hcb hda hdb).mp
      (hbet.sOppSide_of_notMem_of_mem hnot hzl)

end D5.S3.Geometry.Polygons.PolygonCyclicCrossing
