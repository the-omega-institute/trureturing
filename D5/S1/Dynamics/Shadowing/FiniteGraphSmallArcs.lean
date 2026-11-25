/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphSmallArcs
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphSmallArcs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small affine graph balls control the diameter of locally injective interval paths. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Rolle

/-! Closed neighborhoods and short arcs of the affine graph realization. -/

open Set Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

noncomputable section

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

private theorem vertex_or_edge (x : Space G) :
    (∃ u, x = vertex G u) ∨
      ∃ (u v : V) (h : G.Adj u v) (t : Icc (0 : ℝ) 1), x = edgeChart G h t := by
  rcases x.property with hv | he
  · obtain ⟨u, hu⟩ := hv
    exact .inl ⟨u, Subtype.ext hu.symm⟩
  · obtain ⟨⟨⟨u, v⟩, h⟩, t, ht⟩ := mem_iUnion.mp he
    exact .inr ⟨u, v, h, t, Subtype.ext ht.symm⟩

/-- The closed segment between two parameters on one oriented edge. -/
def edgeSegment {u v : V} (h : G.Adj u v) (s t : Icc (0 : ℝ) 1) : Set (Space G) :=
  edgeChart G h '' uIcc s t

/-- The closed star at scale `ρ < 1`, described by the coordinate of its center. -/
def closedStar (u : V) (ρ : ℝ) : Set (Space G) :=
  {x | 1 - ρ ≤ coord G x u}

theorem mem_closedStar_iff {u : V} {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    {x : Space G} :
    x ∈ closedStar G u ρ ↔ x = vertex G u ∨
      ∃ (v : V) (h : G.Adj u v) (t : Icc (0 : ℝ) 1),
        (t : ℝ) ≤ ρ ∧ x = edgeChart G h t := by
  change (1 - ρ ≤ coord G x u) ↔ _
  constructor
  · intro hx
    have hp : 0 < coord G x u := (sub_pos.mpr hρ₁).trans_le hx
    rcases vertex_or_edge G x with ⟨v, rfl⟩ | ⟨v, w, h, t, rfl⟩
    · by_cases hu : u = v
      · exact .inl (by subst v; rfl)
      · simp [coord, vertex, vertexVector, hu] at hp
    · rcases endpoint_of_pos hp with hu | hu
      · subst v
        rw [coord_edgeChart, edgeVector_left h.ne] at hx
        exact .inr ⟨w, h, t, by linarith, rfl⟩
      · subst w
        rw [coord_edgeChart, edgeVector_right h.ne] at hx
        exact .inr ⟨v, h.symm, ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2,
          sub_le_self _ t.2.1⟩, by linarith, (edgeChart_reverse G h t).symm⟩
  · rintro (rfl | ⟨v, h, t, ht, rfl⟩)
    · simpa [coord, vertex, vertexVector] using sub_le_self (1 : ℝ) hρ₀
    · rw [coord_edgeChart, edgeVector_left h.ne]
      linarith

/-- Two distinct positive coordinates determine an oriented edge chart. -/
theorem exists_edgeChart_of_two_pos {u v : V} (huv : u ≠ v) {x : Space G}
    (hu : 0 < coord G x u) (hv : 0 < coord G x v) :
    ∃ (h : G.Adj u v) (t : Icc (0 : ℝ) 1), x = edgeChart G h t := by
  rcases vertex_or_edge G x with ⟨w, rfl⟩ | ⟨a, b, h, t, rfl⟩
  · by_cases huw : u = w
    · subst w
      simp [coord, vertex, vertexVector, huv.symm] at hv
    · simp [coord, vertex, vertexVector, huw] at hu
  · rcases endpoint_of_pos hu with hua | hub <;> rcases endpoint_of_pos hv with hva | hvb
    · exact (huv (hua.trans hva.symm)).elim
    · subst a
      subst b
      exact ⟨h, t, rfl⟩
    · subst b
      subst a
      exact ⟨h.symm, ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩,
        (edgeChart_reverse G h t).symm⟩
    · exact (huv (hub.trans hvb.symm)).elim

section Metric

variable [Fintype V]

private theorem dist_coord_le (x y : Space G) (u : V) :
    |coord G x u - coord G y u| ≤ dist x y := by
  change |(x : V → ℝ) u - (y : V → ℝ) u| ≤ dist (x : V → ℝ) (y : V → ℝ)
  simpa only [Real.dist_eq] using dist_le_pi_dist (x : V → ℝ) (y : V → ℝ) u

private theorem dist_edgeChart_vertex {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) :
    dist (edgeChart G h t) (vertex G u) = (t : ℝ) := by
  rw [← edgeChart_zero G h, dist_edgeChart]
  simpa using abs_of_nonneg t.2.1

theorem closedStar_eq_closedBall {u : V} {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    closedStar G u ρ = Metric.closedBall (vertex G u) ρ := by
  ext x
  constructor
  · intro hx
    rcases (mem_closedStar_iff G hρ₀ hρ₁).mp hx with rfl | ⟨v, h, t, ht, rfl⟩
    · exact Metric.mem_closedBall_self hρ₀
    · rwa [Metric.mem_closedBall, dist_edgeChart_vertex G h t]
  · intro hx
    have hcoord := (dist_coord_le G x (vertex G u) u).trans (Metric.mem_closedBall.mp hx)
    have hv : coord G (vertex G u) u = 1 := by simp [coord, vertex, vertexVector]
    rw [hv, abs_le] at hcoord
    change 1 - ρ ≤ coord G x u
    linarith [hcoord.1]

/-- Every closed ball of radius below a quarter lies in an edge interval or in
a closed star of twice the radius. In the star case the center is within
one radius of the vertex. -/
theorem closedBall_subset_edge_or_closedStar {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 4)
    (x : Space G) :
    (∃ (u v : V) (h : G.Adj u v) (s t : Icc (0 : ℝ) 1),
      Metric.closedBall x r ⊆ edgeSegment G h s t) ∨
    (∃ u : V, dist x (vertex G u) ≤ r ∧
      Metric.closedBall x r ⊆ closedStar G u (2 * r)) := by
  have near_vertex (u : V) (hu : dist x (vertex G u) ≤ r) :
      Metric.closedBall x r ⊆ closedStar G u (2 * r) := by
    rw [closedStar_eq_closedBall G (by positivity) (by linarith)]
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    linarith [dist_triangle y x (vertex G u)]
  rcases vertex_or_edge G x with ⟨u, hxu⟩ | ⟨u, v, h, p, hxp⟩
  · have hu : dist x (vertex G u) ≤ r := by simpa [hxu] using hr.le
    exact .inr ⟨u, hu, near_vertex u hu⟩
  · by_cases hp₀ : r < (p : ℝ)
    · by_cases hp₁ : r < 1 - (p : ℝ)
      · let s : Icc (0 : ℝ) 1 := ⟨(p : ℝ) - r, by linarith, by linarith [p.2.2]⟩
        let t : Icc (0 : ℝ) 1 := ⟨(p : ℝ) + r, by linarith [p.2.1], by linarith⟩
        refine .inl ⟨u, v, h, s, t, ?_⟩
        intro y hy
        have hy' := Metric.mem_closedBall.mp hy
        have hu := abs_le.mp ((dist_coord_le G y x u).trans hy')
        have hv := abs_le.mp ((dist_coord_le G y x v).trans hy')
        rw [hxp, coord_edgeChart, edgeVector_left h.ne] at hu
        rw [hxp, coord_edgeChart, edgeVector_right h.ne] at hv
        obtain ⟨h', q, rfl⟩ := exists_edgeChart_of_two_pos G h.ne
          (show 0 < coord G y u by linarith [hu.1])
          (show 0 < coord G y v by linarith [hv.1])
        rw [coord_edgeChart, edgeVector_right h.ne] at hv
        have hst : s ≤ t := show (p : ℝ) - r ≤ (p : ℝ) + r by linarith
        exact ⟨q, by
          rw [uIcc_of_le hst]
          exact ⟨show (p : ℝ) - r ≤ (q : ℝ) by linarith [hv.1],
            show (q : ℝ) ≤ (p : ℝ) + r by linarith [hv.2]⟩, rfl⟩
      · have hv : dist x (vertex G v) ≤ r := by
          rw [hxp, ← edgeChart_reverse G h p, dist_edgeChart_vertex]
          exact le_of_not_gt hp₁
        exact .inr ⟨v, hv, near_vertex v hv⟩
    · have hu : dist x (vertex G u) ≤ r := by
        rw [hxp, dist_edgeChart_vertex]
        exact le_of_not_gt hp₀
      exact .inr ⟨u, hu, near_vertex u hu⟩

/-- The diameter of a closed interval on one edge is its endpoint distance. -/
theorem diam_edgeSegment {u v : V} (h : G.Adj u v) (s t : Icc (0 : ℝ) 1) :
    Metric.diam (edgeSegment G h s t) = dist (edgeChart G h s) (edgeChart G h t) := by
  have hb : Bornology.IsBounded (edgeSegment G h s t) := Metric.isBounded_of_compactSpace
  refine le_antisymm (Metric.diam_le_of_forall_dist_le dist_nonneg ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    simp only [dist_edgeChart]
    rw [mem_uIcc] at hp hq
    simpa only [Real.dist_eq] using Real.dist_le_of_mem_uIcc
      (mem_uIcc.mpr hp : (p : ℝ) ∈ uIcc (s : ℝ) (t : ℝ))
      (mem_uIcc.mpr hq : (q : ℝ) ∈ uIcc (s : ℝ) (t : ℝ))
  · exact Metric.dist_le_diam_of_mem hb
      ⟨s, left_mem_uIcc, rfl⟩ ⟨t, right_mem_uIcc, rfl⟩

/-- The diameter of two initial segments on distinct germs is their outer endpoint distance. -/
theorem diam_edgeSegments_incident {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w)
    (hvw : v ≠ w) (s t : Icc (0 : ℝ) 1) :
    let zero : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
    Metric.diam (edgeSegment G hv zero s ∪ edgeSegment G hw zero t) =
      dist (edgeChart G hv s) (edgeChart G hw t) := by
  dsimp only
  let zero : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  let A := edgeSegment G hv zero s
  let B := edgeSegment G hw zero t
  have hb : Bornology.IsBounded (A ∪ B) := Metric.isBounded_of_compactSpace
  have hdA : Metric.diam A = (s : ℝ) := by
    rw [diam_edgeSegment, edgeChart_zero, dist_comm, dist_edgeChart_vertex]
  have hdB : Metric.diam B = (t : ℝ) := by
    rw [diam_edgeSegment, edgeChart_zero, dist_comm, dist_edgeChart_vertex]
  have cross (x : Space G) (hx : x ∈ A) (y : Space G) (hy : y ∈ B) :
      dist x y ≤ max (s : ℝ) (t : ℝ) := by
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    rw [dist_edgeChart_incident G hv hw hvw]
    rw [uIcc_of_le (show zero ≤ s from s.2.1)] at hp
    rw [uIcc_of_le (show zero ≤ t from t.2.1)] at hq
    exact max_le_max hp.2 hq.2
  refine le_antisymm (Metric.diam_le_of_forall_dist_le dist_nonneg ?_) ?_
  · intro x hx y hy
    rw [dist_edgeChart_incident G hv hw hvw]
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (Metric.dist_le_diam_of_mem (hb.subset subset_union_left) hx hy).trans
        (hdA.le.trans (le_max_left _ _))
    · exact cross x hx y hy
    · rw [dist_comm]
      exact cross y hy x hx
    · exact (Metric.dist_le_diam_of_mem (hb.subset subset_union_right) hx hy).trans
        (hdB.le.trans (le_max_right _ _))
  · exact Metric.dist_le_diam_of_mem hb
      (Or.inl ⟨s, right_mem_uIcc, rfl⟩) (Or.inr ⟨t, right_mem_uIcc, rfl⟩)

end Metric

private theorem coord_vertex_ne {u v : V} (hvu : v ≠ u) :
    coord G (vertex G u) v = 0 := by
  simp [coord, vertex, vertexVector, hvu]

private theorem injOn_coord_edge {u v : V} (h : G.Adj u v) :
    InjOn (fun x => coord G x v) (range (edgeChart G h)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ he
  simp only [coord_edgeChart, edgeVector_right h.ne] at he
  exact congrArg (edgeChart G h) (Subtype.ext he)

private theorem injOn_coord_positive_spoke {u v : V} {ρ : ℝ} (huv : u ≠ v)
    (hρ₁ : ρ < 1) :
    InjOn (fun x => coord G x v) (closedStar G u ρ ∩ {x | 0 < coord G x v}) := by
  intro x hx y hy he
  obtain ⟨hx, hxp⟩ := hx
  obtain ⟨hy, hyp⟩ := hy
  obtain ⟨hx', s, rfl⟩ := exists_edgeChart_of_two_pos G huv
    ((sub_pos.mpr hρ₁).trans_le hx) hxp
  obtain ⟨hy', t, rfl⟩ := exists_edgeChart_of_two_pos G huv
    ((sub_pos.mpr hρ₁).trans_le hy) hyp
  exact injOn_coord_edge G hx' (mem_range_self s) (mem_range_self t) he

/-- An interval path inside a small star covers the segment from its center
to each positive point reached on an incident edge. -/
theorem edgeSegment_subset_image_of_star_path {u v : V} (h : G.Adj u v)
    {ρ a b : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) {g : ℝ → Space G}
    (hg : ContinuousOn g (uIcc a b)) (hmap : MapsTo g (uIcc a b) (closedStar G u ρ))
    (ha : g a = vertex G u) {s : Icc (0 : ℝ) 1} (hb : g b = edgeChart G h s)
    (hs : (s : ℝ) ≤ ρ) :
    edgeSegment G h ⟨0, le_rfl, zero_le_one⟩ s ⊆ g '' uIcc a b := by
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (t : ℝ) ≤ s := by
    rw [uIcc_of_le (show (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1) ≤ s from s.2.1)] at ht
    exact ht.2
  by_cases hz : (t : ℝ) = 0
  · exact ⟨a, left_mem_uIcc, by
      rw [ha, show t = ⟨0, le_rfl, zero_le_one⟩ from Subtype.ext hz, edgeChart_zero]⟩
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm hz)
  let q := fun x => coord G (g x) v
  have hqa : q a = 0 := by simp [q, ha, coord_vertex_ne G h.ne.symm]
  have hqb : q b = (s : ℝ) := by simp [q, hb, edgeVector_right h.ne]
  have hmem : (t : ℝ) ∈ uIcc (q a) (q b) := by
    rw [hqa, hqb]; exact mem_uIcc_of_le htpos.le ht'
  obtain ⟨x, hx, hqx⟩ := intermediate_value_uIcc
    ((continuous_coord G v).comp_continuousOn hg) hmem
  have hxt : edgeChart G h t ∈ closedStar G u ρ :=
    (mem_closedStar_iff G hρ hρ₁).mpr (.inr ⟨v, h, t, ht'.trans hs, rfl⟩)
  have hco : coord G (edgeChart G h t) v = (t : ℝ) := by simp [edgeVector_right h.ne]
  change q x = (t : ℝ) at hqx
  have hpx : 0 < coord G (g x) v := (hqx.symm ▸ htpos : 0 < q x)
  have hpt : 0 < coord G (edgeChart G h t) v := hco.symm ▸ htpos
  exact ⟨x, hx, injOn_coord_positive_spoke G h.ne hρ₁
    ⟨hmap hx, hpx⟩ ⟨hxt, hpt⟩ (hqx.trans hco.symm)⟩

/-- An embedded interval through a star center covers two different incident segments. -/
theorem two_incident_segments_of_star_path {u : V} {ρ a b c : ℝ}
    (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hc : c ∈ Ioo a b) {g : ℝ → Space G}
    (hg : ContinuousOn g (Icc a b)) (hmap : MapsTo g (Icc a b) (closedStar G u ρ))
    (hinj : InjOn g (Icc a b)) (hcenter : g c = vertex G u) :
    ∃ (v w : V) (hv : G.Adj u v) (hw : G.Adj u w) (s t : Icc (0 : ℝ) 1),
      v ≠ w ∧ 0 < (s : ℝ) ∧ 0 < (t : ℝ) ∧
      edgeSegment G hv ⟨0, le_rfl, zero_le_one⟩ s ⊆ g '' Icc a b ∧
      edgeSegment G hw ⟨0, le_rfl, zero_le_one⟩ t ⊆ g '' Icc a b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr (hc.1.trans hc.2).le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr (hc.1.trans hc.2).le
  have hcl : c ∈ Icc a b := Ioo_subset_Icc_self hc
  have hna : g a ≠ vertex G u := fun e => hc.1.ne (hinj ha hcl (e.trans hcenter.symm))
  have hnb : g b ≠ vertex G u := fun e => hc.2.ne (hinj hcl hb (hcenter.trans e.symm))
  obtain ⟨v, hv, s, hsρ, hsa⟩ := ((mem_closedStar_iff G hρ hρ₁).mp (hmap ha)).resolve_left hna
  obtain ⟨w, hw, t, htρ, htb⟩ := ((mem_closedStar_iff G hρ hρ₁).mp (hmap hb)).resolve_left hnb
  have hpositive {q : V} (hq : G.Adj u q) {p : Icc (0 : ℝ) 1} {x : ℝ}
      (he : g x = edgeChart G hq p) (hn : g x ≠ vertex G u) : 0 < (p : ℝ) := by
    by_contra! hp
    have hp₀ : p = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext (le_antisymm hp p.2.1)
    exact hn (by simpa only [hp₀, edgeChart_zero] using he)
  have hs := hpositive hv hsa hna
  have ht := hpositive hw htb hnb
  have hca : uIcc c a ⊆ Icc a b := uIcc_subset_Icc hcl ha
  have hcb : uIcc c b ⊆ Icc a b := uIcc_subset_Icc hcl hb
  have hL := edgeSegment_subset_image_of_star_path G hv hρ hρ₁
    (hg.mono hca) (hmap.mono_left hca) hcenter hsa hsρ
  have hR := edgeSegment_subset_image_of_star_path G hw hρ hρ₁
    (hg.mono hcb) (hmap.mono_left hcb) hcenter htb htρ
  refine ⟨v, w, hv, hw, s, t, ?_, hs, ht, hL.trans (image_mono hca),
    hR.trans (image_mono hcb)⟩
  rintro rfl
  let p : Icc (0 : ℝ) 1 := ⟨min (s : ℝ) (t : ℝ),
    (lt_min hs ht).le, (min_le_left _ _).trans s.2.2⟩
  have hp : 0 < (p : ℝ) := lt_min hs ht
  obtain ⟨l, hl, hle⟩ := hL ⟨p, mem_uIcc_of_le hp.le (min_le_left _ _), rfl⟩
  obtain ⟨r, hr, hre⟩ := hR ⟨p, mem_uIcc_of_le hp.le (min_le_right _ _), rfl⟩
  have hlr := hinj (hca hl) (hcb hr) (hle.trans hre.symm)
  have hlc : l = c := by
    rw [uIcc_of_ge hc.1.le] at hl
    rw [← hlr, uIcc_of_le hc.2.le] at hr
    exact le_antisymm hl.2 hr.1
  have hz : coord G (edgeChart G hv p) v = 0 := by
    rw [← hle, hlc, hcenter, coord_vertex_ne G hv.ne.symm]
  simp only [coord_edgeChart, edgeVector_right hv.ne] at hz
  exact hp.ne' hz

private theorem not_isExtrOn_of_locally_injective {g : ℝ → ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hg : ContinuousOn g (Icc a b))
    (hi : ∃ U ∈ 𝓝 c, InjOn g U) : ¬ IsExtrOn g (Icc a b) c := by
  obtain ⟨U, hU, hUi⟩ := hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (isOpen_Ioo.mem_nhds hc))
  let l := c - δ / 2
  let r := c + δ / 2
  have hl : l < c := by dsimp [l]; linarith
  have hr : c < r := by dsimp [r]; linarith
  have hsub : Icc l r ⊆ U ∩ Ioo a b := by
    have hs := (Metric.closedBall_subset_ball (x := c)
      (show δ / 2 < δ by linarith)).trans hball
    rwa [Real.closedBall_eq_Icc] at hs
  have hI : Icc l r ⊆ Icc a b :=
    hsub.trans (inter_subset_right.trans Ioo_subset_Icc_self)
  have hlm : l ∈ Icc l r := left_mem_Icc.mpr (hl.trans hr).le
  have hrm : r ∈ Icc l r := right_mem_Icc.mpr (hl.trans hr).le
  have hcm : c ∈ Icc l r := ⟨hl.le, hr.le⟩
  have hgi : InjOn g (Icc l r) := hUi.mono (hsub.trans inter_subset_left)
  have hm := (hg.mono hI).strictMonoOn_of_injOn_Icc' (hl.trans hr).le hgi
  rintro (hmin | hmax)
  · rcases hm with hm | hm
    · exact (not_lt_of_ge (hmin (hI hlm))) (hm hlm hcm hl)
    · exact (not_lt_of_ge (hmin (hI hrm))) (hm hcm hrm hr)
  · rcases hm with hm | hm
    · exact (not_lt_of_ge (hmax (hI hrm))) (hm hcm hrm hr)
    · exact (not_lt_of_ge (hmax (hI hlm))) (hm hlm hcm hl)

/-- A locally injective interval path in a truncated star cannot exceed both
endpoint values on any noncentral coordinate. -/
theorem coord_le_max_endpoints_of_mapsTo_closedStar {u v : V} {ρ a b : ℝ}
    (huv : u ≠ v) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) {f : ℝ → Space G}
    (hf : ContinuousOn f (Icc a b)) (hmap : MapsTo f (Icc a b) (closedStar G u ρ))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) {t : ℝ} (ht : t ∈ Icc a b) :
    coord G (f t) v ≤ max (coord G (f a) v) (coord G (f b) v) := by
  let g := fun s => coord G (f s) v
  change g t ≤ max (g a) (g b)
  have hg : ContinuousOn g (Icc a b) := (continuous_coord G v).comp_continuousOn hf
  by_contra! hbad
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t, ht⟩ hg
  have hgt : max (g a) (g b) < g c := hbad.trans_le (hmax ht)
  have hci : c ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hc.1 (fun h => (not_lt_of_ge (le_max_left (g a) (g b))) (h ▸ hgt)),
      lt_of_le_of_ne hc.2 (fun h => (not_lt_of_ge (le_max_right (g a) (g b))) (h ▸ hgt))⟩
  have hna : 0 ≤ g a := by
    rcases (mem_closedStar_iff G hρ₀ hρ₁).mp (hmap (left_mem_Icc.mpr (ht.1.trans ht.2))) with
      he | ⟨w, h, s, _, he⟩
    · simp [g, he, coord_vertex_ne G huv.symm]
    · change 0 ≤ coord G (f a) v
      rw [he, coord_edgeChart]
      by_cases hvw : v = w
      · subst w
        rw [edgeVector_right h.ne]
        exact s.2.1
      · rw [edgeVector_other huv.symm hvw]
  have hp : 0 < g c := hna.trans_lt ((le_max_left _ _).trans_lt hgt)
  obtain ⟨U, hU, hi⟩ := hloc c hci
  have hN : Icc a b ∈ 𝓝 c :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hci) Ioo_subset_Icc_self
  have hpos : {s | 0 < g s} ∈ 𝓝 c :=
    ((hg c hc).continuousAt hN) (Ioi_mem_nhds hp)
  refine not_isExtrOn_of_locally_injective hci hg
    ⟨(U ∩ Icc a b) ∩ {s | 0 < g s}, inter_mem (inter_mem hU hN) hpos, ?_⟩ (.inr hmax)
  intro x hx y hy he
  exact hi hx.1.1 hy.1.1
    (injOn_coord_positive_spoke G huv hρ₁ ⟨hmap hx.1.2, hx.2⟩
      ⟨hmap hy.1.2, hy.2⟩ he)

private theorem injOn_interval_of_injective_coordinate {α : Type*} [TopologicalSpace α]
    {f : ℝ → α} {g : α → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : Continuous g)
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U)
    (hcoord : InjOn g (f '' Icc a b)) : InjOn f (Icc a b) := by
  have no_return (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s < t) :
      f s ≠ f t := by
    intro he
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hgc : ContinuousOn (g ∘ f) (Icc s t) := hg.comp_continuousOn (hf.mono hsub)
    obtain ⟨c, hc, hce⟩ := exists_Ioo_extr_on_Icc hst hgc (congrArg g he)
    obtain ⟨U, hU, hUi⟩ := hloc c ⟨hs.1.trans_lt hc.1, hc.2.trans_le ht.2⟩
    have hN : Icc a b ∈ 𝓝 c :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hc) (Ioo_subset_Icc_self.trans hsub)
    refine not_isExtrOn_of_locally_injective hc hgc ⟨U ∩ Icc a b, inter_mem hU hN, ?_⟩ hce
    intro x hx y hy hxy
    exact hUi hx.1 hy.1 (hcoord (mem_image_of_mem f hx.2) (mem_image_of_mem f hy.2) hxy)
  intro s hs t ht he
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (no_return s t hs ht hst he).elim
  · exact hst
  · exact (no_return t s ht hs hst he.symm).elim

/-- A path in a closed edge that is locally injective throughout the interior
of its parameter interval is injective on the whole interval. -/
theorem injOn_interval_of_mapsTo_edge {u v : V} (h : G.Adj u v) {a b : ℝ}
    {f : ℝ → Space G} (hf : ContinuousOn f (Icc a b))
    (hmap : MapsTo f (Icc a b) (range (edgeChart G h)))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) : InjOn f (Icc a b) :=
  injOn_interval_of_injective_coordinate hf (continuous_coord G v) hloc
    ((injOn_coord_edge G h).mono (mapsTo_iff_image_subset.mp hmap))

/-- A path in a truncated star that is locally injective throughout the
interior of its parameter interval is injective on the whole interval. -/
theorem injOn_interval_of_mapsTo_closedStar {u : V} {ρ a b : ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ₁ : ρ < 1) {f : ℝ → Space G} (hf : ContinuousOn f (Icc a b))
    (hmap : MapsTo f (Icc a b) (closedStar G u ρ))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) : InjOn f (Icc a b) := by
  have no_return (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s < t) :
      f s ≠ f t := by
    intro he
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hfs := hf.mono hsub
    have hmaps := hmap.mono_left hsub
    have hlocs (x : ℝ) (hx : x ∈ Ioo s t) : ∃ U ∈ 𝓝 x, InjOn f U :=
      hloc x ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
    have hcap (w : V) (huw : u ≠ w) (x : ℝ) (hx : x ∈ Icc s t) :
        coord G (f x) w ≤ coord G (f s) w := by
      simpa only [← he, max_self] using
        coord_le_max_endpoints_of_mapsTo_closedStar G huw hρ₀ hρ₁ hfs hmaps hlocs hx
    rcases (mem_closedStar_iff G hρ₀ hρ₁).mp (hmap hs) with hhub | ⟨v, h, p, _, hsp⟩
    · have hconstant (x : ℝ) (hx : x ∈ Icc s t) : f x = vertex G u := by
        rcases (mem_closedStar_iff G hρ₀ hρ₁).mp (hmaps hx) with hcenter | ⟨w, hw, q, _, hxw⟩
        · exact hcenter
        · have hz := hcap w hw.ne x hx
          rw [hxw, hhub, coord_vertex_ne G hw.ne.symm, coord_edgeChart,
            edgeVector_right hw.ne] at hz
          have hq : q = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext (le_antisymm hz q.2.1)
          rw [hxw, hq, edgeChart_zero]
      have hi : InjOn (fun x => coord G x u) (f '' Icc s t) := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
        rw [hconstant x hx, hconstant y hy]
      exact hst.ne (injOn_interval_of_injective_coordinate hfs (continuous_coord G u) hlocs hi
        (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) he)
    · have hsingle : MapsTo f (Icc s t) (range (edgeChart G h)) := by
        intro x hx
        rcases (mem_closedStar_iff G hρ₀ hρ₁).mp (hmaps hx) with hcenter | ⟨w, hw, q, _, hxw⟩
        · exact ⟨⟨0, le_rfl, zero_le_one⟩, (edgeChart_zero G h).trans hcenter.symm⟩
        · by_cases hwv : w = v
          · subst w
            exact ⟨q, hxw.symm⟩
          · have hz := hcap w hw.ne x hx
            rw [hxw, hsp, coord_edgeChart, edgeVector_right hw.ne, coord_edgeChart,
              edgeVector_other hw.ne.symm hwv] at hz
            have hq : q = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext (le_antisymm hz q.2.1)
            exact ⟨⟨0, le_rfl, zero_le_one⟩, by rw [hxw, hq, edgeChart_zero, edgeChart_zero]⟩
      exact hst.ne (injOn_interval_of_mapsTo_edge G h hfs hsingle hlocs
        (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) he)
  intro s hs t ht he
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (no_return s t hs ht hst he).elim
  · exact hst
  · exact (no_return t s ht hs hst he.symm).elim

section Metric

variable [Fintype V]

private theorem diam_image_eq_of_forall_dist_le {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → Space G}
    (h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (f s) (f t) ≤ dist (f a) (f b)) :
    Metric.diam (f '' Icc a b) = dist (f a) (f b) := by
  refine le_antisymm (Metric.diam_le_of_forall_dist_le dist_nonneg ?_) ?_
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact h s hs t ht
  · exact Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace
      (mem_image_of_mem f (left_mem_Icc.mpr hab)) (mem_image_of_mem f (right_mem_Icc.mpr hab))

/-- A locally injective interval path in one edge has image diameter equal
to the distance between its endpoints. -/
theorem diam_image_of_mapsTo_edge {u v : V} (h : G.Adj u v) {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → Space G} (hf : ContinuousOn f (Icc a b))
    (hmap : MapsTo f (Icc a b) (range (edgeChart G h)))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) :
    Metric.diam (f '' Icc a b) = dist (f a) (f b) := by
  let g := fun x => coord G (f x) v
  have hgi : InjOn g (Icc a b) := by
    intro x hx y hy he
    exact injOn_interval_of_mapsTo_edge G h hf hmap hloc hx hy
      (injOn_coord_edge G h (hmap hx) (hmap hy) he)
  have hgc : ContinuousOn g (Icc a b) := (continuous_coord G v).comp_continuousOn hf
  have hga : ∀ x ∈ Icc a b, g x ∈ uIcc (g a) (g b) := by
    intro x hx
    have ha := left_mem_Icc.mpr hab
    have hb := right_mem_Icc.mpr hab
    rcases hgc.strictMonoOn_of_injOn_Icc' hab hgi with hm | hm
    · exact mem_uIcc.mpr (.inl ⟨hm.monotoneOn ha hx hx.1, hm.monotoneOn hx hb hx.2⟩)
    · exact mem_uIcc.mpr (.inr ⟨hm.antitoneOn hx hb hx.2, hm.antitoneOn ha hx hx.1⟩)
  have hdist (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc a b) :
      dist (f x) (f y) = dist (g x) (g y) := by
    obtain ⟨s, hs⟩ := hmap hx
    obtain ⟨t, ht⟩ := hmap hy
    simp [g, ← hs, ← ht, dist_edgeChart, Real.dist_eq, h.ne]
  apply diam_image_eq_of_forall_dist_le G hab
  intro x hx y hy
  rw [hdist x hx y hy, hdist a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab)]
  exact Real.dist_le_of_mem_uIcc (hga x hx) (hga y hy)

/-- A locally injective interval path in a truncated star has image diameter
equal to the distance between its endpoints in the affine sup metric. -/
theorem diam_image_of_mapsTo_closedStar {u : V} {ρ a b : ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ₁ : ρ < 1) (hab : a ≤ b) {f : ℝ → Space G} (hf : ContinuousOn f (Icc a b))
    (hmap : MapsTo f (Icc a b) (closedStar G u ρ))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) :
    Metric.diam (f '' Icc a b) = dist (f a) (f b) := by
  let d := dist (f a) (f b)
  have ha := hmap (left_mem_Icc.mpr hab)
  have hb := hmap (right_mem_Icc.mpr hab)
  have hshape {x : ℝ} (hx : x ∈ Icc a b) := (mem_closedStar_iff G hρ₀ hρ₁).mp (hmap hx)
  have hcap (w : V) (hu : u ≠ w) {x : ℝ} (hx : x ∈ Icc a b) :
      coord G (f x) w ≤ max (coord G (f a) w) (coord G (f b) w) :=
    coord_le_max_endpoints_of_mapsTo_closedStar G hu hρ₀ hρ₁ hf hmap hloc hx
  by_cases hw : ∃ w : V, u ≠ w ∧ 0 < coord G (f a) w ∧ 0 < coord G (f b) w
  · obtain ⟨v, huv, hva, hvb⟩ := hw
    obtain ⟨h, s, hs⟩ := exists_edgeChart_of_two_pos G huv
      ((sub_pos.mpr hρ₁).trans_le ha) hva
    obtain ⟨_, t, ht⟩ := exists_edgeChart_of_two_pos G huv
      ((sub_pos.mpr hρ₁).trans_le hb) hvb
    have hsingle : MapsTo f (Icc a b) (range (edgeChart G h)) := by
      intro x hx
      rcases hshape hx with hcenter | ⟨w, hw, q, _, hq⟩
      · exact ⟨⟨0, le_rfl, zero_le_one⟩, (edgeChart_zero G h).trans hcenter.symm⟩
      · by_cases he : w = v
        · subst w
          exact ⟨q, hq.symm⟩
        · have hz := hcap w hw.ne hx
          rw [hq, hs, ht, coord_edgeChart, edgeVector_right hw.ne, coord_edgeChart,
            edgeVector_other hw.ne.symm he, coord_edgeChart,
            edgeVector_other hw.ne.symm he, max_self] at hz
          have hz' : q = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext (le_antisymm hz q.2.1)
          exact ⟨⟨0, le_rfl, zero_le_one⟩, by rw [hq, hz', edgeChart_zero, edgeChart_zero]⟩
    exact diam_image_of_mapsTo_edge G h hab hf hsingle hloc
  · have hnonneg {x : ℝ} (hx : x ∈ Icc a b) {w : V} (hwu : w ≠ u) :
        0 ≤ coord G (f x) w := by
      rcases hshape hx with hcenter | ⟨v, h, t, _, hxt⟩
      · rw [hcenter, coord_vertex_ne G hwu]
      · rw [hxt, coord_edgeChart]
        by_cases he : w = v
        · subst w
          simpa only [edgeVector_right h.ne] using t.2.1
        · rw [edgeVector_other hwu he]
    have hwidth {w : V} (huw : u ≠ w) :
        max (coord G (f a) w) (coord G (f b) w) ≤ d := by
      have haz := hnonneg (left_mem_Icc.mpr hab) huw.symm
      have hbz := hnonneg (right_mem_Icc.mpr hab) huw.symm
      have hd := dist_coord_le G (f a) (f b) w
      by_cases hapos : 0 < coord G (f a) w
      · have hbzero : coord G (f b) w = 0 :=
          le_antisymm (le_of_not_gt fun h => hw ⟨w, huw, hapos, h⟩) hbz
        rw [hbzero, max_eq_left haz]
        simpa only [hbzero, sub_zero, abs_of_nonneg haz] using hd
      · have hazero : coord G (f a) w = 0 := le_antisymm (le_of_not_gt hapos) haz
        rw [hazero, max_eq_right hbz]
        simpa only [hazero, zero_sub, abs_neg, abs_of_nonneg hbz] using hd
    have hcenter {x : ℝ} (hx : x ∈ Icc a b) :
        1 - d ≤ coord G (f x) u ∧ coord G (f x) u ≤ 1 := by
      rcases hshape hx with he | ⟨v, h, t, _, hxt⟩
      · simp [he, coord, vertex, vertexVector, show 0 ≤ d from dist_nonneg]
      · have ht := (hcap v h.ne hx).trans (hwidth h.ne)
        rw [hxt, coord_edgeChart, edgeVector_right h.ne] at ht
        rw [hxt, coord_edgeChart, edgeVector_left h.ne]
        constructor <;> linarith [t.2.1]
    apply diam_image_eq_of_forall_dist_le G hab
    intro x hx y hy
    change dist (f x : V → ℝ) (f y : V → ℝ) ≤ d
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro w
    change dist (coord G (f x) w) (coord G (f y) w) ≤ d
    rw [Real.dist_eq, abs_le]
    by_cases he : w = u
    · subst w
      constructor <;> linarith [(hcenter hx).1, (hcenter hx).2, (hcenter hy).1, (hcenter hy).2]
    · have huw : u ≠ w := Ne.symm he
      constructor <;> linarith [hnonneg hx he, hnonneg hy he,
        (hcap w huw hx).trans (hwidth huw), (hcap w huw hy).trans (hwidth huw)]

/-- Within a uniform affine closed ball, a continuous interval path locally
injective on the interior is globally injective and has endpoint diameter. -/
theorem injOn_and_diam_image_of_mapsTo_closedBall {r a b : ℝ} (hr : 0 < r)
    (hr' : r < 1 / 4) (hab : a ≤ b) (z : Space G) {f : ℝ → Space G}
    (hf : ContinuousOn f (Icc a b)) (hmap : MapsTo f (Icc a b) (Metric.closedBall z r))
    (hloc : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, InjOn f U) :
    InjOn f (Icc a b) ∧ Metric.diam (f '' Icc a b) = dist (f a) (f b) := by
  rcases closedBall_subset_edge_or_closedStar G hr hr' z with
    ⟨u, v, h, s, t, hst⟩ | ⟨u, _, hu⟩
  · have he : MapsTo f (Icc a b) (range (edgeChart G h)) :=
      hmap.mono_right (hst.trans (image_subset_range _ _))
    exact ⟨injOn_interval_of_mapsTo_edge G h hf he hloc,
      diam_image_of_mapsTo_edge G h hab hf he hloc⟩
  · have hs := hmap.mono_right hu
    have hρ₀ : 0 ≤ 2 * r := by positivity
    have hρ₁ : 2 * r < 1 := by linarith
    exact ⟨injOn_interval_of_mapsTo_closedStar G hρ₀ hρ₁ hf hs hloc,
      diam_image_of_mapsTo_closedStar G hρ₀ hρ₁ hab hf hs hloc⟩

end Metric

#print axioms closedBall_subset_edge_or_closedStar
#print axioms diam_edgeSegment
#print axioms diam_edgeSegments_incident
#print axioms injOn_interval_of_mapsTo_edge
#print axioms injOn_interval_of_mapsTo_closedStar
#print axioms diam_image_of_mapsTo_edge
#print axioms diam_image_of_mapsTo_closedStar
#print axioms injOn_and_diam_image_of_mapsTo_closedBall

end

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
