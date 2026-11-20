/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong transitivity replicates strict folds of any iterate at open-edge points. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
import Mathlib.Topology.Order.Rolle

/-!
A strict fold of any iterate can be pulled back along any orbit that hits its
center. The resulting splits yield indexed coalescing families by the doubling
argument of Gangloff–Guillon–Oprocha, arXiv:2310.17241v1, Remark 3.4 and Lemma 3.7.
-/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

noncomputable section

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

private def edgePoint {u v : V} (h : G.Adj u v) (t : ℝ) : Space G :=
  edgeChart G h (projIcc 0 1 zero_le_one t)

private theorem continuous_edgePoint {u v : V} (h : G.Adj u v) :
    Continuous (edgePoint G h) :=
  (continuous_edgeChart G h).comp continuous_projIcc

private theorem edgePoint_val {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) :
    edgePoint G h t = edgeChart G h t := by
  rw [edgePoint, projIcc_of_mem zero_le_one t.property]

private theorem coord_edgePoint {u v : V} (h : G.Adj u v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : coord G (edgePoint G h t) v = t := by
  rw [edgePoint, projIcc_of_mem zero_le_one ht, coord_edgeChart, edgeVector_right h.ne]

private theorem vertex_or_interior_edge (x : Space G) :
    (∃ u, x = vertex G u) ∨
      ∃ (u v : V) (h : G.Adj u v) (t : Icc (0 : ℝ) 1),
        (t : ℝ) ∈ Ioo 0 1 ∧ x = edgeChart G h t := by
  rcases x.property with ⟨u, hu⟩ | hx
  · exact .inl ⟨u, Subtype.ext hu.symm⟩
  · obtain ⟨⟨⟨u, v⟩, h⟩, t, ht⟩ := mem_iUnion.mp hx
    change G.Adj u v at h
    have he : x = edgeChart G h t := Subtype.ext ht.symm
    by_cases hzero : (t : ℝ) = 0
    · exact .inl ⟨u, by rw [he, show t = ⟨0, le_rfl, zero_le_one⟩ from Subtype.ext hzero,
        edgeChart_zero]⟩
    by_cases hone : (t : ℝ) = 1
    · exact .inl ⟨v, by rw [he, show t = ⟨1, zero_le_one, le_rfl⟩ from Subtype.ext hone,
        edgeChart_one]⟩
    exact .inr ⟨u, v, h, t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm hzero), lt_of_le_of_ne t.2.2 hone⟩, he⟩

private theorem mem_edge_range_of_pos {u v : V} (h : G.Adj u v) {x : Space G}
    (hu : 0 < coord G x u) (hv : 0 < coord G x v) : x ∈ range (edgeChart G h) := by
  rcases vertex_or_interior_edge G x with ⟨w, rfl⟩ | ⟨a, b, hab, t, _, rfl⟩
  · by_cases huw : u = w
    · subst w
      simp [coord, vertex, vertexVector, h.ne.symm] at hv
    · simp [coord, vertex, vertexVector, huw] at hu
  · rcases endpoint_of_pos hu with hua | hub <;> rcases endpoint_of_pos hv with hva | hvb
    · exact (h.ne (hua.trans hva.symm)).elim
    · subst a
      subst b
      exact mem_range_self t
    · subst b
      subst a
      exact ⟨⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩,
        edgeChart_reverse G hab t⟩
    · exact (h.ne (hub.trans hvb.symm)).elim

private theorem vertex_or_incident_edge_of_pos {u : V} {x : Space G}
    (hu : 0 < coord G x u) :
    x = vertex G u ∨ ∃ (v : V) (h : G.Adj u v) (t : Icc (0 : ℝ) 1),
      x = edgeChart G h t := by
  rcases vertex_or_interior_edge G x with ⟨w, rfl⟩ | ⟨a, b, h, t, _, rfl⟩
  · by_cases huw : u = w
    · exact .inl (congrArg (vertex G) huw.symm)
    · simp [coord, vertex, vertexVector, huw] at hu
  · rcases endpoint_of_pos hu with hua | hub
    · subst a
      exact .inr ⟨b, h, t, rfl⟩
    · subst b
      exact .inr ⟨a, h.symm, ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2,
        sub_le_self _ t.2.1⟩, (edgeChart_reverse G h t).symm⟩

private theorem edgePoint_coord {u v : V} (h : G.Adj u v) {x : Space G}
    (hx : x ∈ range (edgeChart G h)) : edgePoint G h (coord G x v) = x := by
  obtain ⟨t, rfl⟩ := hx
  rw [coord_edgeChart, edgeVector_right h.ne, edgePoint_val]

private def openSubarc {u v : V} (h : G.Adj u v) (a b : ℝ) : Set (Space G) :=
  edgePoint G h '' Ioo a b

private theorem isOpen_openSubarc {u v : V} (h : G.Adj u v) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) : IsOpen (openSubarc G h a b) := by
  have he : openSubarc G h a b =
      {x | 0 < coord G x u} ∩ (fun x => coord G x v) ⁻¹' Ioo a b := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩
      rw [show edgePoint G h t = edgeChart G h ⟨t, htI⟩ from edgePoint_val G h ⟨t, htI⟩]
      change 0 < coord G (edgeChart G h ⟨t, htI⟩) u ∧
        coord G (edgeChart G h ⟨t, htI⟩) v ∈ Ioo a b
      rw [coord_edgeChart, edgeVector_left h.ne, coord_edgeChart, edgeVector_right h.ne]
      exact ⟨sub_pos.mpr (ht.2.trans_le hb), ht⟩
    · rintro ⟨hu, hv⟩
      exact ⟨coord G x v, hv, edgePoint_coord G h
        (mem_edge_range_of_pos G h hu (ha.trans_lt hv.1))⟩
  rw [he]
  exact (isOpen_lt continuous_const (continuous_coord G u)).inter
    (isOpen_Ioo.preimage (continuous_coord G v))

private theorem exists_closed_interval {a : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 a) :
    ∃ l r : ℝ, l < a ∧ a < r ∧ Icc l r ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨a - δ / 2, a + δ / 2, by linarith, by linarith, ?_⟩
  have h := (Metric.closedBall_subset_ball (x := a) (show δ / 2 < δ by linarith)).trans hball
  rwa [Real.closedBall_eq_Icc] at h

private theorem finite_fibre_isolation {X : Type*} [TopologicalSpace X] [T1Space X]
    {g : X → X} (x : X) (hfin : (g ⁻¹' {g x}).Finite) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, y ≠ x → g y ≠ g x := by
  let S := g ⁻¹' {g x} \ {x}
  have hS : S.Finite := hfin.sdiff
  refine ⟨Sᶜ, hS.isClosed.isOpen_compl.mem_nhds (by simp [S]), ?_⟩
  exact fun y hy hne he => hy ⟨he, hne⟩

private def StrictFoldAt (H : ℝ → Space G) (c : ℝ) : Prop :=
  ∃ (u v : V) (h : G.Adj u v) (a b : ℝ), a < c ∧ c < b ∧
    MapsTo H (Icc a b) (range (edgeChart G h)) ∧
    ∀ t ∈ Icc a b, t ≠ c → coord G (H c) v < coord G (H t) v

private theorem strictFold_of_extremum {H : ℝ → Space G} {u v : V} (h : G.Adj u v)
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hmap : MapsTo H (Icc a b) (range (edgeChart G h)))
    (hiso : ∃ U ∈ 𝓝 c, ∀ t ∈ U, t ≠ c → H t ≠ H c)
    (he : IsExtrOn (fun t => coord G (H t) v) (Icc a b) c) :
    StrictFoldAt G H c := by
  obtain ⟨U, hU, hne⟩ := hiso
  obtain ⟨l, r, hl, hr, hsub⟩ :=
    exists_closed_interval (inter_mem (isOpen_Ioo.mem_nhds hc) hU)
  have hsubI := hsub.trans (inter_subset_left.trans Ioo_subset_Icc_self)
  have hcm : c ∈ Icc a b := Ioo_subset_Icc_self hc
  have hneq (t : ℝ) (ht : t ∈ Icc l r) (htc : t ≠ c) :
      coord G (H t) v ≠ coord G (H c) v := by
    intro heq
    apply hne t (hsub ht).2 htc
    rw [← edgePoint_coord G h (hmap (hsubI ht)), ← edgePoint_coord G h (hmap hcm), heq]
  rcases he with hmin | hmax
  · exact ⟨u, v, h, l, r, hl, hr, hmap.mono_left hsubI,
      fun t ht htc => lt_of_le_of_ne (hmin (hsubI ht)) (hneq t ht htc).symm⟩
  · have hreverse {x : Space G} (hx : x ∈ range (edgeChart G h)) :
        x ∈ range (edgeChart G h.symm) ∧ coord G x u = 1 - coord G x v := by
      obtain ⟨q, rfl⟩ := hx
      exact ⟨⟨_, edgeChart_reverse G h q⟩, by
        rw [coord_edgeChart, edgeVector_left h.ne, coord_edgeChart, edgeVector_right h.ne]⟩
    refine ⟨v, u, h.symm, l, r, hl, hr, fun t ht => (hreverse (hmap (hsubI ht))).1, ?_⟩
    intro t ht htc
    rw [(hreverse (hmap hcm)).2, (hreverse (hmap (hsubI ht))).2]
    exact sub_lt_sub_left (lt_of_le_of_ne (hmax (hsubI ht)) (hneq t ht htc)) 1

private theorem strictFold_of_collision_on_edge {H : ℝ → Space G} {u v : V}
    (h : G.Adj u v) {a b : ℝ} (hab : a < b) (hH : Continuous H)
    (hmap : MapsTo H (Icc a b) (range (edgeChart G h))) (he : H a = H b)
    (hiso : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, ∀ t ∈ U, t ≠ c → H t ≠ H c) :
    ∃ c ∈ Ioo a b, StrictFoldAt G H c := by
  obtain ⟨c, hc, hce⟩ := exists_Ioo_extr_on_Icc hab
    ((continuous_coord G v).comp hH).continuousOn (congrArg (fun x => coord G x v) he)
  exact ⟨c, hc, strictFold_of_extremum G h hc hmap (hiso c hc) hce⟩

private theorem strictFold_of_collision_in_star {H : ℝ → Space G} {u : V} {a b : ℝ}
    (hab : a < b) (hH : Continuous H)
    (hmap : MapsTo H (Icc a b) {x | 0 < coord G x u}) (he : H a = H b)
    (hiso : ∀ c ∈ Ioo a b, ∃ U ∈ 𝓝 c, ∀ t ∈ U, t ≠ c → H t ≠ H c) :
    ∃ c ∈ Ioo a b, StrictFoldAt G H c := by
  have hstar {x : Space G} (hx : x ∈ {x | 0 < coord G x u}) :=
    vertex_or_incident_edge_of_pos G hx
  have hcoord_center (w : V) (hw : w ≠ u) :
      coord G (vertex G u) w = 0 := by simp [coord, vertex, vertexVector, hw]
  -- An excursion into another spoke has an interior peak in that spoke.
  by_cases hpeak : ∃ w : V, w ≠ u ∧
      ∃ t ∈ Icc a b, 0 < coord G (H t) w ∧ coord G (H a) w < coord G (H t) w
  · obtain ⟨w, hwu, t, ht, hpos, hgt⟩ := hpeak
    let g := fun s => coord G (H s) w
    have hg : Continuous g := (continuous_coord G w).comp hH
    obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t, ht⟩ hg.continuousOn
    have hgc : 0 < g c := hpos.trans_le (hmax ht)
    have hac : g a < g c := hgt.trans_le (hmax ht)
    have hbc : g b < g c := by simpa only [g, ← he] using hac
    have hci : c ∈ Ioo a b := ⟨lt_of_le_of_ne hc.1 (fun e => hac.ne (congrArg g e)),
      lt_of_le_of_ne hc.2 (fun e => hbc.ne (congrArg g e.symm))⟩
    obtain ⟨v, h, p, hp⟩ : ∃ (v : V) (h : G.Adj u v) (p : Icc (0 : ℝ) 1),
        H c = edgeChart G h p := by
      rcases hstar (hmap hc) with hhub | hs
      · simp only [g, hhub, hcoord_center w hwu, lt_self_iff_false] at hgc
      · exact hs
    have hv : w = v :=
      (endpoint_of_pos (show 0 < coord G (edgeChart G h p) w from hp ▸ hgc)).resolve_left hwu
    subst v
    obtain ⟨l, r, hl, hr, hsub⟩ := exists_closed_interval
      (inter_mem (isOpen_Ioo.mem_nhds hci) (hg.continuousAt (Ioi_mem_nhds hgc)))
    have hsubI : Icc l r ⊆ Icc a b :=
      hsub.trans (inter_subset_left.trans Ioo_subset_Icc_self)
    refine ⟨c, hci, strictFold_of_extremum G h ⟨hl, hr⟩ ?_ (hiso c hci)
      (.inr (fun s hs => hmax (hsubI hs)))⟩
    intro s hs
    exact mem_edge_range_of_pos G h (hmap (hsubI hs)) (hsub hs).2
  · -- With no such peak, the whole path stays on the initial spoke or at the center.
    have hcap (t : ℝ) (ht : t ∈ Icc a b) (w : V) (hwu : w ≠ u)
        (hp : 0 < coord G (H t) w) :
        coord G (H t) w ≤ coord G (H a) w :=
      le_of_not_gt (fun heq => hpeak ⟨w, hwu, t, ht, hp, heq⟩)
    rcases hstar (hmap (left_mem_Icc.mpr hab.le)) with ha | ⟨v, h, p, ha⟩
    · have hconst (t : ℝ) (ht : t ∈ Icc a b) : H t = vertex G u := by
        rcases hstar (hmap ht) with heq | ⟨w, hw, q, heq⟩
        · exact heq
        · by_cases hq : (q : ℝ) = 0
          · rw [heq, show q = ⟨0, le_rfl, zero_le_one⟩ from Subtype.ext hq, edgeChart_zero]
          · have hp : 0 < coord G (H t) w := by
              rw [heq, coord_edgeChart, edgeVector_right hw.ne]
              exact lt_of_le_of_ne q.2.1 (Ne.symm hq)
            have hz := hcap t ht w hw.ne.symm hp
            rw [ha, hcoord_center w hw.ne.symm] at hz
            exact (hp.not_ge hz).elim
      obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
      obtain ⟨U, hU, hne⟩ := hiso c hc
      obtain ⟨l, r, hl, hr, hsub⟩ :=
        exists_closed_interval (inter_mem (isOpen_Ioo.mem_nhds hc) hU)
      have hh := hsub (left_mem_Icc.mpr (hl.trans hr).le)
      exact (hne l hh.2 hl.ne
        ((hconst l (Ioo_subset_Icc_self hh.1)).trans (hconst c (Ioo_subset_Icc_self hc)).symm)).elim
    · apply strictFold_of_collision_on_edge G h hab hH ?_ he hiso
      intro s hs
      rcases hstar (hmap hs) with hhub | ⟨w, hw, q, hsq⟩
      · exact ⟨⟨0, le_rfl, zero_le_one⟩, (edgeChart_zero G h).trans hhub.symm⟩
      · by_cases hwv : w = v
        · subst w
          exact ⟨q, hsq.symm⟩
        · by_cases hq : (q : ℝ) = 0
          · exact ⟨⟨0, le_rfl, zero_le_one⟩, by
              rw [hsq, show q = ⟨0, le_rfl, zero_le_one⟩ from Subtype.ext hq,
                edgeChart_zero, edgeChart_zero]⟩
          · have hp : 0 < coord G (H s) w := by
              rw [hsq, coord_edgeChart, edgeVector_right hw.ne]
              exact lt_of_le_of_ne q.2.1 (Ne.symm hq)
            have hz := hcap s hs w hw.ne.symm hp
            rw [ha, coord_edgeChart, edgeVector_other hw.ne.symm hwv] at hz
            exact (hp.not_ge hz).elim

private theorem strictFold_of_not_locally_injective {g : Space G → Space G}
    (hg : Continuous g) (hfin : ∀ z, (g ⁻¹' {z}).Finite)
    {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ∈ Ioo 0 1)
    (hbad : ¬ ∃ U : Set (Space G), IsOpen U ∧ edgeChart G h t ∈ U ∧ InjOn g U) :
    ∃ c ∈ Ioo (0 : ℝ) 1, StrictFoldAt G (g ∘ edgePoint G h) c := by
  let H := g ∘ edgePoint G h
  have hH : Continuous H := hg.comp (continuous_edgePoint G h)
  obtain ⟨W, hW, hchart⟩ : ∃ W ∈ 𝓝 (H t),
      (∃ (a b : V) (hab : G.Adj a b), W ⊆ range (edgeChart G hab)) ∨
        ∃ a : V, W ⊆ {x | 0 < coord G x a} := by
    rcases vertex_or_interior_edge G (H t) with ⟨a, he⟩ | ⟨a, b, hab, q, hq, he⟩
    · have ha : 0 < coord G (H t) a := by simp [he, coord, vertex, vertexVector]
      exact ⟨_, (isOpen_lt continuous_const (continuous_coord G a)).mem_nhds ha, .inr ⟨a, le_rfl⟩⟩
    · have ha : 0 < coord G (H t) a := by
        rw [he, coord_edgeChart, edgeVector_left hab.ne]
        exact sub_pos.mpr hq.2
      have hb : 0 < coord G (H t) b := by
        rw [he, coord_edgeChart, edgeVector_right hab.ne]
        exact hq.1
      refine ⟨_, inter_mem
        ((isOpen_lt continuous_const (continuous_coord G a)).mem_nhds ha)
        ((isOpen_lt continuous_const (continuous_coord G b)).mem_nhds hb), .inl ⟨a, b, hab, ?_⟩⟩
      exact fun _ hx => mem_edge_range_of_pos G hab hx.1 hx.2
  obtain ⟨l, r, hl, hr, hsub⟩ := exists_closed_interval
    (inter_mem (isOpen_Ioo.mem_nhds ht) (hH.continuousAt hW))
  have hbadH : ¬ InjOn H (Icc l r) := by
    intro hinj
    refine hbad ⟨openSubarc G h l r,
      isOpen_openSubarc G h (hsub (left_mem_Icc.mpr (hl.trans hr).le)).1.1.le
        (hsub (right_mem_Icc.mpr (hl.trans hr).le)).1.2.le,
      ⟨t, ⟨hl, hr⟩, edgePoint_val G h t⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
    exact congrArg (edgePoint G h) (hinj (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) he)
  have hordered : ∃ a ∈ Icc l r, ∃ b ∈ Icc l r, a < b ∧ H a = H b := by
    by_contra! hnone
    apply hbadH
    intro a ha b hb he
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hnone a ha b hb hab he).elim
    · exact hab
    · exact (hnone b hb a ha hab he.symm).elim
  obtain ⟨a, ha, b, hb, hab, he⟩ := hordered
  have hsub' := (Icc_subset_Icc ha.1 hb.2).trans hsub
  have hiso (c : ℝ) (hc : c ∈ Ioo a b) : ∃ U ∈ 𝓝 c, ∀ s ∈ U, s ≠ c → H s ≠ H c := by
    have hcI := (hsub' (Ioo_subset_Icc_self hc)).1
    obtain ⟨U, hU, hne⟩ :=
      finite_fibre_isolation (edgePoint G h c) (hfin (g (edgePoint G h c)))
    refine ⟨Ioo 0 1 ∩ edgePoint G h ⁻¹' U,
      inter_mem (isOpen_Ioo.mem_nhds hcI) ((continuous_edgePoint G h).continuousAt hU), ?_⟩
    intro s hs hsc
    apply hne _ hs.2
    intro hs'
    exact hsc (by simpa only [coord_edgePoint G h (Ioo_subset_Icc_self hs.1),
      coord_edgePoint G h (Ioo_subset_Icc_self hcI)] using congrArg (fun x => coord G x v) hs')
  rcases hchart with ⟨u', v', h', hW'⟩ | ⟨u', hW'⟩
  · obtain ⟨c, hc, hfold⟩ := strictFold_of_collision_on_edge G h' hab hH
      (fun s hs => hW' (hsub' hs).2) he hiso
    exact ⟨c, (hsub' (Ioo_subset_Icc_self hc)).1, hfold⟩
  · obtain ⟨c, hc, hfold⟩ := strictFold_of_collision_in_star G hab hH
      (fun s hs => hW' (hsub' hs).2) he hiso
    exact ⟨c, (hsub' (Ioo_subset_Icc_self hc)).1, hfold⟩

/-- Each point is hit from each nonempty ambient open set, allowing time zero. -/
def StronglyTransitive (f : Space G → Space G) : Prop :=
  ∀ U : Set (Space G), IsOpen U → U.Nonempty → ∀ w : Space G,
    ∃ n : ℕ, ∃ x ∈ U, f^[n] x = w

variable [Fintype V]

private def HasSplit (f : Space G → Space G) (ε : ℝ) (U : Set (Space G)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ (u v : V) (h : G.Adj u v) (a b : ℝ),
    0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ ∃ L R : Set (Space G),
      L ∪ R ⊆ U ∧ Disjoint L R ∧
      openSubarc G h a b ⊆ f^[m] '' L ∧ openSubarc G h a b ⊆ f^[m] '' R ∧
      ∀ j ≤ m, ∀ x ∈ L ∪ R, ∀ y ∈ L ∪ R, dist (f^[j] x) (f^[j] y) < ε

private theorem split_of_strictFold {f : Space G → Space G} (hf : Continuous f)
    (htrans : StronglyTransitive G f) (hfin : ∀ n z, ((f^[n]) ⁻¹' {z}).Finite)
    {p : ℕ} (hp : 0 < p) {u v : V} (h : G.Adj u v)
    {c : ℝ} (hc : c ∈ Ioo 0 1) (hfold : StrictFoldAt G ((f^[p]) ∘ edgePoint G h) c)
    {ε : ℝ} (hε : 0 < ε) {u' v' : V} (h' : G.Adj u' v')
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    HasSplit G f ε (openSubarc G h' a b) := by
  obtain ⟨u₀, v₀, h₀, l, r, hl, hr, hmap, hmin⟩ := hfold
  let w := edgePoint G h c
  have hU : (openSubarc G h' a b).Nonempty := (nonempty_Ioo.mpr hab).image _
  obtain ⟨n, _, ⟨d, hd, rfl⟩, hhit⟩ :=
    htrans _ (isOpen_openSubarc G h' ha hb) hU w
  -- Appending the folding iterate works for hits from either side, including at time zero.
  let m := p + n
  obtain ⟨δ, hδ, hscale⟩ := IntervalObstruction.finite_block_scale isCompact_univ
    hf.continuousOn (mapsTo_univ f univ) hε (m + 1)
  let K := (f^[n]) ∘ edgePoint G h'
  have hK : Continuous K := (hf.iterate n).comp (continuous_edgePoint G h')
  have hKd : K d = w := hhit
  let W := openSubarc G h (max 0 l) (min 1 r)
  have hW : IsOpen W := isOpen_openSubarc G h (le_max_left _ _) (min_le_left _ _)
  have hw : w ∈ W := ⟨c, ⟨max_lt hc.1 hl, lt_min hc.2 hr⟩, rfl⟩
  obtain ⟨S, hS, hne⟩ := finite_fibre_isolation (edgePoint G h' d)
    (hfin n (f^[n] (edgePoint G h' d)))
  let B := Metric.ball (edgePoint G h' d) (δ / 3)
  let U := (Ioo a b ∩ edgePoint G h' ⁻¹' (S ∩ B)) ∩ K ⁻¹' W
  have hU' : U ∈ 𝓝 d := inter_mem
    (inter_mem (isOpen_Ioo.mem_nhds hd) ((continuous_edgePoint G h').continuousAt
      (inter_mem hS (Metric.ball_mem_nhds _ (by positivity)))))
    (hK.continuousAt (hW.mem_nhds (hKd ▸ hw)))
  obtain ⟨e, g, hed, hdg, heg⟩ := exists_closed_interval hU'
  have hI (s : ℝ) (hs : s ∈ Icc e g) : s ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans (heg hs).1.1.1.le, (heg hs).1.1.2.le.trans hb⟩
  have hdI : d ∈ Icc e g := ⟨hed.le, hdg.le⟩
  let H := (f^[m]) ∘ edgePoint G h'
  let D := fun s => coord G (H s) v₀
  have hD : Continuous D := (continuous_coord G v₀).comp
    ((hf.iterate m).comp (continuous_edgePoint G h'))
  have hH (s q : ℝ) (hsq : K s = edgePoint G h q) :
      H s = ((f^[p]) ∘ edgePoint G h) q := by
    change f^[p + n] (edgePoint G h' s) = f^[p] (edgePoint G h q)
    rw [Function.iterate_add_apply, show f^[n] (edgePoint G h' s) = _ from hsq]
  have hHmap (s : ℝ) (hs : s ∈ Icc e g) : H s ∈ range (edgeChart G h₀) := by
    obtain ⟨q, hq, hsq⟩ := (heg hs).2
    rw [hH s q hsq.symm]
    exact hmap ⟨(le_max_right _ _).trans hq.1.le, hq.2.le.trans (min_le_right _ _)⟩
  have hstrict (s : ℝ) (hs : s ∈ Icc e g) (hsd : s ≠ d) : D d < D s := by
    obtain ⟨q, hq, hsq⟩ := (heg hs).2
    have hneq : K s ≠ K d := hne _ (heg hs).1.2.1 (fun heq => hsd
      (by simpa only [coord_edgePoint G h' (hI s hs), coord_edgePoint G h' (hI d hdI)]
        using congrArg (fun x => coord G x v') heq))
    have hqc : q ≠ c := fun eq => hneq (hsq.symm.trans (eq ▸ hKd.symm))
    change coord G (H d) v₀ < coord G (H s) v₀
    rw [hH d c hKd, hH s q hsq.symm]
    exact hmin q ⟨(le_max_right _ _).trans hq.1.le, hq.2.le.trans (min_le_right _ _)⟩ hqc
  have hDmem (s : ℝ) (hs : s ∈ Icc e g) : D s ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨q, hq⟩ := hHmap s hs
    change coord G (H s) v₀ ∈ Icc (0 : ℝ) 1
    rw [← hq, coord_edgeChart, edgeVector_right h₀.ne]
    exact q.2
  have heI : e ∈ Icc e g := left_mem_Icc.mpr (hed.trans hdg).le
  have hgI : g ∈ Icc e g := right_mem_Icc.mpr (hed.trans hdg).le
  let L := edgePoint G h' '' Ico e d
  let R := edgePoint G h' '' Ioc d g
  have hLI : Ico e d ⊆ Icc e g := fun _ hs => ⟨hs.1, hs.2.le.trans hdg.le⟩
  have hRI : Ioc d g ⊆ Icc e g := fun _ hs => ⟨hed.le.trans hs.1.le, hs.2⟩
  have hbig : L ∪ R ⊆ edgePoint G h' '' Icc e g :=
    union_subset (image_mono hLI) (image_mono hRI)
  refine ⟨m, by dsimp [m]; omega, u₀, v₀, h₀, D d, min (D e) (D g),
    (hDmem d hdI).1, lt_min (hstrict e heI hed.ne) (hstrict g hgI hdg.ne'),
    (min_le_left _ _).trans (hDmem e heI).2, L, R, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbig.trans (image_mono fun s hs => (heg hs).1.1)
  · refine disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    exact (hs.2.trans ht.1).ne' (by
      simpa only [coord_edgePoint G h' (hI t (hRI ht)), coord_edgePoint G h' (hI s (hLI hs))]
        using congrArg (fun x => coord G x v') heq)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Icc (D d) (D e) := ⟨hq.1.le, hq.2.le.trans (min_le_left _ _)⟩
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' hed.le hD.continuousOn hq'
    have hsd : s < d := lt_of_le_of_ne hs.2 (fun eq => hq.1.ne (eq ▸ heq))
    exact ⟨edgePoint G h' s, ⟨s, ⟨hs.1, hsd⟩, rfl⟩,
      (edgePoint_coord G h₀ (hHmap s ⟨hs.1, hs.2.trans hdg.le⟩)).symm.trans
        (congrArg (edgePoint G h₀) heq)⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Icc (D d) (D g) := ⟨hq.1.le, hq.2.le.trans (min_le_right _ _)⟩
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hdg.le hD.continuousOn hq'
    have hds : d < s := lt_of_le_of_ne hs.1 (fun eq => hq.1.ne (eq.symm ▸ heq))
    exact ⟨edgePoint G h' s, ⟨s, ⟨hds, hs.2⟩, rfl⟩,
      (edgePoint_coord G h₀ (hHmap s ⟨hed.le.trans hs.1, hs.2⟩)).symm.trans
        (congrArg (edgePoint G h₀) heq)⟩
  · intro j hj x hx y hy
    obtain ⟨s, hs, rfl⟩ := hbig hx
    obtain ⟨t, ht, rfl⟩ := hbig hy
    have hsB := Metric.mem_ball.mp (heg hs).1.2.2
    have htB := Metric.mem_ball.mp (heg ht).1.2.2
    exact hscale j (Nat.lt_succ_of_le hj) _ (mem_univ _) _ (mem_univ _) (by
      linarith [dist_triangle_right (edgePoint G h' s) (edgePoint G h' t) (edgePoint G h' d)])

private theorem coalescing_families_of_splits {f : Space G → Space G} {ε : ℝ} (hε : 0 < ε)
    (hsplit : ∀ {u v : V} (h : G.Adj u v) {a b : ℝ}, 0 ≤ a → a < b → b ≤ 1 →
      HasSplit G f ε (openSubarc G h a b))
    (k : ℕ) {u v : V} (h : G.Adj u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ T : ℕ, ∃ x : Fin (2 ^ k) → Space G, Injective x ∧ (∀ i, x i ∈ openSubarc G h a b) ∧
      (∀ i j t, dist (f^[t] (x i)) (f^[t] (x j)) < ε) ∧
      ∀ i j, f^[T] (x i) = f^[T] (x j) := by
  classical
  induction k generalizing u v a b with
  | zero =>
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
    have : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨0, fun _ => edgePoint G h c, fun _ _ _ => Subsingleton.elim _ _,
      fun _ => mem_image_of_mem _ hc, fun _ _ _ => by simpa, fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨r, _, _, _, h', a', b', ha', hab', hb', L, R, hsub, hdis, hL, hR, hprefix⟩ :=
      hsplit h ha hab hb
    obtain ⟨T, x, hxi, hx, hclose, hterm⟩ := ih h' ha' hab' hb'
    choose left hl hlx using fun i => hL (hx i)
    choose right hr hrx using fun i => hR (hx i)
    let lift : Fin (2 ^ k) × Fin 2 → Space G :=
      fun (i, side) => if side = 0 then left i else right i
    have hLift (i : Fin (2 ^ k) × Fin 2) : f^[r] (lift i) = x i.1 := by
      by_cases hi : i.2 = 0
      · simpa [lift, hi] using hlx i.1
      · simpa [lift, hi] using hrx i.1
    have hside (i : Fin (2 ^ k) × Fin 2) : lift i ∈ if i.2 = 0 then L else R := by
      by_cases hi : i.2 = 0
      · simpa [lift, hi] using hl i.1
      · simpa [lift, hi] using hr i.1
    have hmem (i : Fin (2 ^ k) × Fin 2) : lift i ∈ L ∪ R := by
      by_cases hi : i.2 = 0
      · exact Or.inl (by simpa [hi] using hside i)
      · exact Or.inr (by simpa [hi] using hside i)
    have hinj : Injective lift := by
      intro i j he
      have hij := hxi ((hLift i).symm.trans ((congrArg (f^[r]) he).trans (hLift j)))
      refine Prod.ext hij ?_
      have hjmem : lift i ∈ if j.2 = 0 then L else R := he ▸ hside j
      by_cases hi : i.2 = 0 <;> by_cases hj : j.2 = 0
      · exact hi.trans hj.symm
      · exact (disjoint_left.mp hdis (by simpa [hi] using hside i)
          (by simpa [hj] using hjmem)).elim
      · exact (disjoint_left.mp hdis (by simpa [hj] using hjmem)
          (by simpa [hi] using hside i)).elim
      · exact (Fin.eq_one_of_ne_zero _ hi).trans (Fin.eq_one_of_ne_zero _ hj).symm
    let e : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) × Fin 2 :=
      (finCongr (pow_succ 2 k)).trans finProdFinEquiv.symm
    refine ⟨T + r, lift ∘ e, hinj.comp e.injective, fun i => hsub (hmem (e i)), ?_, ?_⟩
    · intro i j t
      by_cases ht : t ≤ r
      · exact hprefix t ht _ (hmem (e i)) _ (hmem (e j))
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge ht)
        rw [Nat.add_comm r s, Function.comp_apply, Function.comp_apply,
          Function.iterate_add_apply, Function.iterate_add_apply, hLift, hLift]
        exact hclose _ _ _
    · intro i j
      simp only [Function.comp_apply, Function.iterate_add_apply, hLift]
      exact hterm _ _

/-- Every positive iterate of a continuous strongly transitive finitely positively
expansive self-map is locally injective at every open-edge point. -/
theorem isLocallyInjective_iterate_at_openEdge {f : Space G → Space G}
    (hf : Continuous f) (htrans : StronglyTransitive G f) (hfin : FinitelyPositiveExpansive f)
    {p : ℕ} (hp : 0 < p) {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ∈ Ioo 0 1) :
    ∃ U : Set (Space G), IsOpen U ∧ edgeChart G h t ∈ U ∧ InjOn (f^[p]) U := by
  by_contra hbad
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  obtain ⟨C, hC⟩ := IntervalObstruction.uniform_fibre_bound isCompact_univ hB hε
  have hfib (r : ℕ) (z : Space G) : ((f^[r]) ⁻¹' {z}).Finite := by
    have hbound := IntervalObstruction.uniform_iterate_fibre_bound (mapsTo_univ f univ) hC r z
    exact finite_of_encard_le_coe (by simpa only [univ_inter] using hbound)
  obtain ⟨c, hc, hfold⟩ := strictFold_of_not_locally_injective G
    (hf.iterate p) (hfib p) h t ht hbad
  obtain ⟨T, x, hxi, _, hclose, hterm⟩ := coalescing_families_of_splits G hε
    (by
      intro u' v' h' a' b' ha' hab' hb'
      exact split_of_strictFold G hf htrans hfib hp h hc hfold hε h' ha' hab' hb')
    N h le_rfl zero_lt_one le_rfl
  exact IntervalObstruction.no_coalescing_witnesses hB hε N.lt_two_pow_self x hxi
    (fun _ => mem_univ _) (fun i j s _ => hclose i j s) hterm

#print axioms isLocallyInjective_iterate_at_openEdge

end

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
