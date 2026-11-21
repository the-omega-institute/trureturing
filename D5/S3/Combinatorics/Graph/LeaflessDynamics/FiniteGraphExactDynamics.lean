/- GID: D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphExactDynamics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphExactDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact positively expansive edge-walk dynamics on finite leafless graphs. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
import D5.S1.Dynamics.Shadowing.EdgeSubdivisionDynamics
import D5.S3.Combinatorics.Graph.LeaflessDynamics.LeaflessDartTour
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Subdivide each affine edge into as many cells as there are darts in its
chosen tour. The closed cell maps agree at shared endpoints and descend to
the graph. The first and last darts preserve the germs at the graph vertices.
-/

open Function Set
open SimpleGraph hiding dist

open D5.S1.Dynamics.Shadowing

namespace D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteGraphExactDynamics

open FiniteGraphAffineRealization

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}

local notation "I" => Icc (0 : ℝ) 1

private def leftEnd : I := ⟨0, le_rfl, zero_le_one⟩
private def rightEnd : I := ⟨1, zero_le_one, le_rfl⟩

private def reverseParameter (t : I) : I :=
  ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩

private theorem reverseParameter_involutive : Involutive reverseParameter := by
  intro t
  apply Subtype.ext
  change 1 - (1 - (t : ℝ)) = (t : ℝ)
  ring

private theorem isometry_reverseParameter : Isometry reverseParameter := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (1 - (s : ℝ)) (1 - (t : ℝ)) = dist (s : ℝ) (t : ℝ)
  simp only [Real.dist_eq]
  rw [show 1 - (s : ℝ) - (1 - (t : ℝ)) = t - s by ring]
  exact abs_sub_comm _ _

private theorem exists_dart (e : G.edgeSet) : ∃ d : G.Dart, d.edge = e.val := by
  rcases e with ⟨⟨u, v⟩, h⟩
  exact ⟨⟨(u, v), h⟩, rfl⟩

/-- One orientation is used as the coordinate chart for each undirected edge. -/
def orientation (e : G.edgeSet) : G.Dart := Classical.choose (exists_dart e)

@[simp] theorem orientation_edge (e : G.edgeSet) : (orientation e).edge = e.val :=
  Classical.choose_spec (exists_dart e)

private def dartChart (d : G.Dart) : I → Space G := edgeChart G d.adj

/-- The affine chart of an undirected edge, with its chosen orientation. -/
def chart (e : G.edgeSet) : I → Space G := dartChart (orientation e)

@[simp] private theorem dartChart_left (d : G.Dart) :
    dartChart d leftEnd = vertex G d.fst := edgeChart_zero G d.adj

@[simp] private theorem dartChart_right (d : G.Dart) :
    dartChart d rightEnd = vertex G d.snd := edgeChart_one G d.adj

private theorem dartChart_reverse (d : G.Dart) (t : I) :
    dartChart d.symm (reverseParameter t) = dartChart d t :=
  edgeChart_reverse G d.adj t

private theorem range_dartChart_eq {d e : G.Dart} (h : d.edge = e.edge) :
    range (dartChart d) = range (dartChart e) := by
  rcases (dart_edge_eq_iff _ _).mp h with rfl | rfl
  · rfl
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨reverseParameter t, by
        simpa only [Dart.symm_symm] using dartChart_reverse e.symm t⟩
    · rintro ⟨t, rfl⟩
      exact ⟨reverseParameter t, dartChart_reverse e t⟩

private theorem chart_cover [Nontrivial V] (hconn : G.Connected) (x : Space G) :
    ∃ e : G.edgeSet, x ∈ range (chart e) := by
  have hd : ∃ d : G.Dart, x ∈ range (dartChart d) := by
    rcases x.property with ⟨v, hv⟩ | he
    · obtain ⟨w, hw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
      let d : G.Dart := ⟨(v, w), hw⟩
      exact ⟨d, leftEnd, (dartChart_left d).trans (Subtype.ext hv)⟩
    · obtain ⟨⟨⟨u, v⟩, huv⟩, t, ht⟩ := mem_iUnion.mp he
      exact ⟨⟨(u, v), huv⟩, t, Subtype.ext ht⟩
  obtain ⟨d, hd⟩ := hd
  let e : G.edgeSet := ⟨d.edge, d.edge_mem⟩
  refine ⟨e, ?_⟩
  rw [chart, range_dartChart_eq (orientation_edge e : (orientation e).edge = d.edge)]
  exact hd

/-- The data and endpoint conditions of an actual nonbacktracking all-edge tour. -/
structure EdgeTour (a : G.Dart) where
  walk : G.Walk a.fst a.snd
  notNil : ¬walk.Nil
  length_ge_two : 2 ≤ walk.length
  first : walk.firstDart notNil = a
  last : walk.lastDart notNil = a
  chain : walk.edges.IsChain (· ≠ ·)
  covers : walk.edgeSet = G.edgeSet

/-- A choice of one all-edge tour for each oriented source chart. -/
abbrev Tours (G : SimpleGraph V) := ∀ e : G.edgeSet, EdgeTour (orientation e)

/-- Choose the tours supplied by the combinatorial leafless-graph theorem. -/
def chooseTours (hconn : G.Connected) (hleaf : ∀ v, (G.neighborSet v).ncard ≠ 1) : Tours G :=
  fun e => Classical.choice (by
    obtain ⟨w, hn, hl, hf, ht, hc, he⟩ :=
      D5.S3.Combinatorics.Graph.LeaflessDynamics.LeaflessDartTour.exists_nonbacktracking_all_edge_tour
        hconn hleaf (orientation e)
    exact ⟨⟨w, hn, hl, hf, ht, hc, he⟩⟩)

variable (T : Tours G)

/-- The length of the chosen tour is the number of closed cells on the source edge. -/
def cellCount (e : G.edgeSet) : ℕ := (T e).walk.length

/-- The finite family of closed cells, indexed by source edge and tour position. -/
abbrev Cell := Σ e : G.edgeSet, Fin (cellCount T e)

/-- The dart traversed on a given closed cell. -/
def targetDart (c : Cell T) : G.Dart :=
  (T c.1).walk.darts[c.2.val]'(by simpa only [Walk.length_darts, cellCount] using c.2.isLt)

private theorem targetDart_first (e : G.edgeSet) (i : Fin (cellCount T e))
    (hi : i.val = 0) : targetDart T ⟨e, i⟩ = orientation e := by
  have hp : 0 < (T e).walk.darts.length := by
    rw [Walk.length_darts]
    exact Walk.not_nil_iff_lt_length.mp (T e).notNil
  rw [← (T e).first, Walk.firstDart_eq (T e).notNil hp]
  simp only [targetDart, hi]

private theorem targetDart_last (e : G.edgeSet) (i : Fin (cellCount T e))
    (hi : i.val + 1 = cellCount T e) : targetDart T ⟨e, i⟩ = orientation e := by
  have hp : 0 < (T e).walk.darts.length := by
    rw [Walk.length_darts]
    exact Walk.not_nil_iff_lt_length.mp (T e).notNil
  have hi' : i.val = (T e).walk.darts.length - 1 := by
    rw [Walk.length_darts]
    change i.val + 1 = (T e).walk.length at hi
    omega
  rw [← (T e).last, Walk.lastDart_eq (T e).notNil hp]
  simp only [targetDart, hi']

private theorem targetDart_step (e : G.edgeSet) (i j : Fin (cellCount T e))
    (h : i.val + 1 = j.val) :
    G.DartAdj (targetDart T ⟨e, i⟩) (targetDart T ⟨e, j⟩) ∧
      (targetDart T ⟨e, i⟩).edge ≠ (targetDart T ⟨e, j⟩).edge := by
  have hd : i.val + 1 < (T e).walk.darts.length := by
    rw [h, Walk.length_darts]
    exact j.isLt
  have he : i.val + 1 < (T e).walk.edges.length := by
    rw [h, Walk.length_edges]
    exact j.isLt
  constructor
  · have hc := (T e).walk.isChain_dartAdj_darts.getElem i.val hd
    simpa only [targetDart, h] using hc
  · have hc := (T e).chain.getElem i.val he
    rw [Walk.getElem_edges_eq_edge_getElem_darts, Walk.getElem_edges_eq_edge_getElem_darts] at hc
    simpa only [targetDart, h] using hc

private theorem cellCount_ge_three (e : G.edgeSet) : 3 ≤ cellCount T e := by
  have htwo : 2 ≤ cellCount T e := (T e).length_ge_two
  by_contra! h
  let i : Fin (cellCount T e) := ⟨0, by omega⟩
  let j : Fin (cellCount T e) := ⟨1, by omega⟩
  have hlast : j.val + 1 = cellCount T e := by
    change 1 + 1 = cellCount T e
    omega
  have he := (targetDart_first T e i rfl).trans (targetDart_last T e j hlast).symm
  exact (targetDart_step T e i j rfl).2 (congrArg Dart.edge he)

private theorem cellCount_pos (e : G.edgeSet) : (0 : ℝ) < cellCount T e :=
  Nat.cast_pos.mpr (by have := cellCount_ge_three T e; omega)

/-- The affine inclusion of a closed cell in its source edge parameter. -/
def subdivisionParameter (c : Cell T) (t : I) : I := by
  have hi : (c.2.val : ℝ) + 1 ≤ cellCount T c.1 := by
    exact_mod_cast Nat.succ_le_of_lt c.2.isLt
  have hm := cellCount_pos T c.1
  exact ⟨((c.2.val : ℝ) + t) / cellCount T c.1,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) t.2.1) hm.le,
    (div_le_iff₀ hm).mpr (by linarith [t.2.2])⟩

private theorem continuous_subdivisionParameter (c : Cell T) :
    Continuous (subdivisionParameter T c) :=
  ((continuous_const.add continuous_subtype_val).div_const _).subtype_mk _

private theorem subdivision_cover (e : G.edgeSet) (u : I) :
    ∃ i : Fin (cellCount T e), ∃ t : I, subdivisionParameter T ⟨e, i⟩ t = u := by
  have hm := cellCount_pos T e
  by_cases hu : (u : ℝ) = 1
  · have hmNat : 0 < cellCount T e := Nat.cast_pos.mp hm
    let i : Fin (cellCount T e) := ⟨cellCount T e - 1, by omega⟩
    have hiNat : i.val + 1 = cellCount T e := by
      change cellCount T e - 1 + 1 = cellCount T e
      omega
    have hi : (i.val : ℝ) + 1 = cellCount T e := by
      exact_mod_cast hiNat
    refine ⟨i, rightEnd, Subtype.ext ?_⟩
    change ((i.val : ℝ) + 1) / cellCount T e = (u : ℝ)
    rw [hi, hu, div_self hm.ne']
  · let v := (cellCount T e : ℝ) * u.val
    have hv₀ : 0 ≤ v := mul_nonneg hm.le u.2.1
    have hv₁ : v < cellCount T e := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left (lt_of_le_of_ne u.2.2 hu) hm
    let i : Fin (cellCount T e) := ⟨⌊v⌋₊, (Nat.floor_lt hv₀).mpr hv₁⟩
    have hfrac : v - (⌊v⌋₊ : ℕ) ≤ 1 := by linarith [Nat.lt_floor_add_one v]
    let t : I := ⟨v - (i.val : ℝ), sub_nonneg.mpr (Nat.floor_le hv₀), hfrac⟩
    refine ⟨i, t, Subtype.ext ?_⟩
    change ((i.val : ℝ) + (v - (i.val : ℝ))) / cellCount T e = (u : ℝ)
    rw [add_sub_cancel, show v = _ from rfl, mul_div_cancel_left₀ _ hm.ne']

private theorem subdivision_left {e : G.edgeSet} {i : Fin (cellCount T e)} {t : I}
    (h : subdivisionParameter T ⟨e, i⟩ t = leftEnd) : i.val = 0 ∧ t = leftEnd := by
  have hm := cellCount_pos T e
  have hs := congrArg Subtype.val h
  change ((i.val : ℝ) + t.val) / cellCount T e = 0 at hs
  rw [div_eq_iff hm.ne', zero_mul] at hs
  have hi : (i.val : ℝ) = 0 := by linarith [t.2.1, Nat.cast_nonneg (α := ℝ) i.val]
  exact ⟨Nat.cast_eq_zero.mp hi, Subtype.ext (by change t.val = 0; linarith)⟩

private theorem subdivision_right {e : G.edgeSet} {i : Fin (cellCount T e)} {t : I}
    (h : subdivisionParameter T ⟨e, i⟩ t = rightEnd) :
    i.val + 1 = cellCount T e ∧ t = rightEnd := by
  have hm := cellCount_pos T e
  have hs := congrArg Subtype.val h
  change ((i.val : ℝ) + t.val) / cellCount T e = 1 at hs
  rw [div_eq_iff hm.ne', one_mul] at hs
  have hi : (i.val : ℝ) + 1 ≤ cellCount T e := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hEq : (i.val : ℝ) + 1 = cellCount T e := by linarith [t.2.2]
  exact ⟨by exact_mod_cast hEq, Subtype.ext (by change t.val = 1; linarith)⟩

private theorem subdivision_adjacent {e : G.edgeSet} {i j : Fin (cellCount T e)} {s t : I}
    (hij : i.val < j.val)
    (h : subdivisionParameter T ⟨e, i⟩ s = subdivisionParameter T ⟨e, j⟩ t) :
    i.val + 1 = j.val ∧ s = rightEnd ∧ t = leftEnd := by
  have hs := congrArg Subtype.val h
  change ((i.val : ℝ) + s.val) / cellCount T e =
    ((j.val : ℝ) + t.val) / cellCount T e at hs
  have hs := (div_left_inj' (cellCount_pos T e).ne').mp hs
  have hle : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
  have heq : (i.val : ℝ) + 1 = j.val := by linarith [s.2.2, t.2.1]
  exact ⟨by exact_mod_cast heq, Subtype.ext (by change s.val = 1; linarith [s.2.2, t.2.1]),
    Subtype.ext (by change t.val = 0; linarith [s.2.2, t.2.1])⟩

private theorem subdivision_injective (c : Cell T) : Injective (subdivisionParameter T c) := by
  intro s t h
  apply Subtype.ext
  have hs := congrArg Subtype.val h
  change ((c.2.val : ℝ) + s.val) / cellCount T c.1 =
    ((c.2.val : ℝ) + t.val) / cellCount T c.1 at hs
  exact add_left_cancel ((div_left_inj' (cellCount_pos T c.1).ne').mp hs)

/-- The source of a closed cell, parametrized on the unit interval. -/
def source (c : Cell T) (t : I) : Space G := chart c.1 (subdivisionParameter T c t)

private theorem continuous_source (c : Cell T) : Continuous (source T c) :=
  (continuous_edgeChart G (orientation c.1).adj).comp (continuous_subdivisionParameter T c)

/-- The target of a closed cell runs through the whole designated dart. -/
def target (c : Cell T) : I → Space G := dartChart (targetDart T c)

private theorem continuous_target (c : Cell T) : Continuous (target T c) :=
  continuous_edgeChart G (targetDart T c).adj

private def endpoint (atEnd : Bool) : I := if atEnd then rightEnd else leftEnd

private def outgoingDart (d : G.Dart) (atEnd : Bool) : G.Dart :=
  if atEnd then d.symm else d

private def outgoingParameter (atEnd : Bool) (t : I) : I :=
  if atEnd then reverseParameter t else t

@[simp] private theorem outgoingDart_edge (d : G.Dart) (atEnd : Bool) :
    (outgoingDart d atEnd).edge = d.edge := by
  cases atEnd <;> simp [outgoingDart]

private theorem dartChart_endpoint (d : G.Dart) (atEnd : Bool) :
    dartChart d (endpoint atEnd) = vertex G (outgoingDart d atEnd).fst := by
  cases atEnd <;> simp [endpoint, outgoingDart]

private theorem dartChart_outgoing (d : G.Dart) (atEnd : Bool) (t : I) :
    dartChart (outgoingDart d atEnd) (outgoingParameter atEnd t) = dartChart d t := by
  cases atEnd
  · rfl
  · exact dartChart_reverse d t

private theorem vertex_injective : Injective (vertex G) := by
  intro u v h
  by_contra huv
  have he := congrArg (fun x => coord G x u) h
  change vertexVector u u = vertexVector v u at he
  simp [vertexVector, huv] at he

private theorem chart_endpoint_of_distinct {e f : G.edgeSet} {s t : I}
    (hne : e ≠ f) (h : chart e s = chart f t) : ∃ b, s = endpoint b := by
  by_cases hs₀ : s.val = 0
  · exact ⟨false, Subtype.ext hs₀⟩
  by_cases hs₁ : s.val = 1
  · exact ⟨true, Subtype.ext hs₁⟩
  have hv := congrArg Subtype.val h
  change edgeVector (orientation e).fst (orientation e).snd s =
    edgeVector (orientation f).fst (orientation f).snd t at hv
  have hend := endpoints_of_interior_eq (orientation e).fst_ne_snd
    (lt_of_le_of_ne s.2.1 (Ne.symm hs₀)) (lt_of_le_of_ne s.2.2 hs₁) hv
  apply (hne (Subtype.ext ?_)).elim
  rw [← orientation_edge e, ← orientation_edge f]
  exact (dart_edge_eq_mk'_iff').mpr hend

private theorem targetDart_of_graph_endpoint (c : Cell T) (t : I) (b : Bool)
    (h : subdivisionParameter T c t = endpoint b) :
    t = endpoint b ∧ targetDart T c = orientation c.1 := by
  rcases c with ⟨e, i⟩
  cases b
  · obtain ⟨hi, ht⟩ := subdivision_left T h
    exact ⟨ht, targetDart_first T e i hi⟩
  · obtain ⟨hi, ht⟩ := subdivision_right T h
    exact ⟨ht, targetDart_last T e i hi⟩

private theorem distinct_cells_meet (c d : Cell T) {s t : I}
    (hne : c ≠ d) (h : source T c s = source T d t) :
    ∃ a b, s = endpoint a ∧ t = endpoint b ∧
      (outgoingDart (targetDart T c) a).fst = (outgoingDart (targetDart T d) b).fst ∧
      (targetDart T c).edge ≠ (targetDart T d).edge := by
  rcases c with ⟨e, i⟩
  rcases d with ⟨f, j⟩
  by_cases hef : e = f
  · subst f
    have hparam := (isometry_edgeChart G (orientation e).adj).injective h
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · obtain ⟨hstep, hs, ht⟩ := subdivision_adjacent T hij hparam
      obtain ⟨hadj, hed⟩ := targetDart_step T e i j hstep
      exact ⟨true, false, hs, ht, hadj, hed⟩
    · exact (hne (congrArg (fun k : Fin (cellCount T e) => (⟨e, k⟩ : Cell T))
        (Fin.ext hij))).elim
    · obtain ⟨hstep, ht, hs⟩ := subdivision_adjacent T hij hparam.symm
      obtain ⟨hadj, hed⟩ := targetDart_step T e j i hstep
      exact ⟨false, true, hs, ht, Eq.symm hadj, Ne.symm hed⟩
  · change chart e (subdivisionParameter T ⟨e, i⟩ s) =
      chart f (subdivisionParameter T ⟨f, j⟩ t) at h
    obtain ⟨a, ha⟩ := chart_endpoint_of_distinct hef h
    obtain ⟨b, hb⟩ := chart_endpoint_of_distinct (Ne.symm hef) h.symm
    obtain ⟨hs, hd⟩ := targetDart_of_graph_endpoint T ⟨e, i⟩ s a ha
    obtain ⟨ht, hd'⟩ := targetDart_of_graph_endpoint T ⟨f, j⟩ t b hb
    rw [ha, hb] at h
    simp only [chart, dartChart_endpoint] at h
    refine ⟨a, b, hs, ht, ?_, ?_⟩
    · rw [hd, hd']
      exact vertex_injective h
    · rw [hd, hd', orientation_edge, orientation_edge]
      exact fun he => hef (Subtype.ext he)

private theorem target_eq_of_source_eq (c d : Cell T) {s t : I}
    (h : source T c s = source T d t) : target T c s = target T d t := by
  by_cases hcd : c = d
  · subst d
    have hp := (isometry_edgeChart G (orientation c.1).adj).injective h
    rw [subdivision_injective T c hp]
  · obtain ⟨a, b, rfl, rfl, hab, _⟩ := distinct_cells_meet T c d hcd h
    change dartChart (targetDart T c) (endpoint a) = dartChart (targetDart T d) (endpoint b)
    rw [dartChart_endpoint, dartChart_endpoint, hab]

section Map

variable [Nontrivial V] (hconn : G.Connected)

private abbrev CellDomain := Σ _ : Cell T, I

include hconn in
private theorem source_surjective :
    Surjective (fun a : CellDomain T => source T a.1 a.2) := by
  intro x
  obtain ⟨e, u, rfl⟩ := chart_cover hconn x
  obtain ⟨i, t, ht⟩ := subdivision_cover T e u
  exact ⟨⟨⟨e, i⟩, t⟩, congrArg (chart e) ht⟩

/-- The continuous edge-walk selfmap obtained by descending the closed cell maps. -/
def edgeWalkMap (x : Space G) : Space G :=
  let a := Classical.choose (source_surjective T hconn x)
  target T a.1 a.2

/-- The selfmap follows the designated dart on the entire closed cell. -/
theorem edgeWalkMap_source (c : Cell T) (t : I) :
    edgeWalkMap T hconn (source T c t) = target T c t := by
  exact target_eq_of_source_eq T _ c (Classical.choose_spec (source_surjective T hconn (source T c t)))

theorem continuous_edgeWalkMap : Continuous (edgeWalkMap T hconn) := by
  let q : CellDomain T → Space G := fun a => source T a.1 a.2
  have hq : Continuous q := continuous_sigma (continuous_source T)
  have hquot : Topology.IsQuotientMap q :=
    hq.isClosedMap.isQuotientMap hq (source_surjective T hconn)
  have ht : Continuous (fun a : CellDomain T => target T a.1 a.2) :=
    continuous_sigma (continuous_target T)
  apply hquot.continuous_iff.mpr
  exact ht.congr fun a => (edgeWalkMap_source T hconn a.1 a.2).symm

private theorem tour_visits (e : G.edgeSet) (d : G.Dart) :
    ∃ i : Fin (cellCount T e), (targetDart T ⟨e, i⟩).edge = d.edge := by
  have hm : d.edge ∈ (T e).walk.edgeSet := (T e).covers.symm ▸ d.edge_mem
  change d.edge ∈ (T e).walk.edges at hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  let ii : Fin (cellCount T e) := ⟨i, by simpa only [Walk.length_edges, cellCount] using hi⟩
  refine ⟨ii, ?_⟩
  rw [Walk.getElem_edges_eq_edge_getElem_darts] at he
  exact he

/-- Each source edge covers the full graph in one step. -/
theorem edgeWalkMap_image_chart (e : G.edgeSet) :
    edgeWalkMap T hconn '' range (chart e) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨f, hx⟩ := chart_cover hconn x
  obtain ⟨i, hi⟩ := tour_visits T e (orientation f)
  have htarget : x ∈ range (target T ⟨e, i⟩) := by
    change x ∈ range (dartChart (targetDart T ⟨e, i⟩))
    rw [range_dartChart_eq hi]
    exact hx
  obtain ⟨t, ht⟩ := htarget
  exact ⟨source T ⟨e, i⟩ t, ⟨subdivisionParameter T ⟨e, i⟩ t, rfl⟩,
    (edgeWalkMap_source T hconn _ _).trans ht⟩

private theorem dist_subdivisionParameter (c : Cell T) (s t : I) :
    dist (subdivisionParameter T c s) (subdivisionParameter T c t) =
      |(s : ℝ) - t| / cellCount T c.1 := by
  change dist (((c.2.val : ℝ) + s) / cellCount T c.1)
    (((c.2.val : ℝ) + t) / cellCount T c.1) = _
  rw [Real.dist_eq, ← sub_div,
    show (c.2.val : ℝ) + s - ((c.2.val : ℝ) + t) = (s : ℝ) - t by ring,
    abs_div, abs_of_pos (cellCount_pos T c.1)]

private theorem lipschitz_subdivisionParameter (c : Cell T) :
    LipschitzWith (1 / 2) (subdivisionParameter T c) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_subdivisionParameter, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two]
  change _ ≤ (1 / 2 : ℝ) * dist (s : ℝ) (t : ℝ)
  rw [Real.dist_eq, div_le_iff₀ (cellCount_pos T c.1)]
  have hm : (2 : ℝ) ≤ cellCount T c.1 := by
    exact_mod_cast (show 2 ≤ cellCount T c.1 from (T c.1).length_ge_two)
  calc
    |(s : ℝ) - t| = (1 / 2 : ℝ) * |(s : ℝ) - t| * 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (abs_nonneg _))

private theorem inverse_branch (e : G.edgeSet) (u : I) :
    ∃ (f : G.edgeSet) (h : I → I), u ∈ range h ∧ LipschitzWith (1 / 2) h ∧
      edgeWalkMap T hconn ∘ chart e ∘ h = chart f := by
  obtain ⟨i, t, ht⟩ := subdivision_cover T e u
  let c : Cell T := ⟨e, i⟩
  let d := targetDart T c
  let f : G.edgeSet := ⟨d.edge, d.edge_mem⟩
  have hed : d.edge = (orientation f).edge := (orientation_edge f).symm
  rcases (dart_edge_eq_iff _ _).mp hed with hd | hd
  · refine ⟨f, subdivisionParameter T c, ⟨t, ht⟩, lipschitz_subdivisionParameter T c, ?_⟩
    funext v
    change edgeWalkMap T hconn (source T c v) = dartChart (orientation f) v
    rw [edgeWalkMap_source]
    exact congrArg (fun a => dartChart a v) hd
  · refine ⟨f, subdivisionParameter T c ∘ reverseParameter,
      ⟨reverseParameter t, ?_⟩, ?_, ?_⟩
    · simpa only [comp_apply, reverseParameter_involutive t] using ht
    · simpa only [mul_one] using
        (lipschitz_subdivisionParameter T c).comp isometry_reverseParameter.lipschitzWith
    · funext v
      change edgeWalkMap T hconn (source T c (reverseParameter v)) = dartChart (orientation f) v
      rw [edgeWalkMap_source]
      exact (congrArg (fun a => dartChart a (reverseParameter v)) hd).trans
        (dartChart_reverse (orientation f) v)

/-- A contracting inverse branch through every point yields topological exactness. -/
theorem topologicallyExact_edgeWalkMap :
    ExactPendantObstruction.TopologicallyExact (edgeWalkMap T hconn) :=
  EdgeSubdivisionDynamics.topologicallyExact_of_inverse_charts chart (chart_cover hconn)
    (fun e => (isometry_edgeChart G (orientation e).adj).lipschitzWith)
    (inverse_branch T hconn) (edgeWalkMap_image_chart T hconn)

private theorem dist_source (c : Cell T) (s t : I) :
    dist (source T c s) (source T c t) = |(s : ℝ) - t| / cellCount T c.1 :=
  ((isometry_edgeChart G (orientation c.1).adj).dist_eq _ _).trans
    (dist_subdivisionParameter T c s t)

private theorem dist_target (c : Cell T) (s t : I) :
    dist (target T c s) (target T c t) = |(s : ℝ) - t| :=
  dist_edgeChart G (targetDart T c).adj s t

private theorem expands_on_cell (c : Cell T) (s t : I) :
    3 * dist (source T c s) (source T c t) ≤
      dist (edgeWalkMap T hconn (source T c s)) (edgeWalkMap T hconn (source T c t)) := by
  rw [edgeWalkMap_source, edgeWalkMap_source, dist_source, dist_target]
  have hm : (3 : ℝ) ≤ cellCount T c.1 := by exact_mod_cast cellCount_ge_three T c.1
  calc
    3 * (|(s : ℝ) - t| / cellCount T c.1) ≤
        (cellCount T c.1 : ℝ) * (|(s : ℝ) - t| / cellCount T c.1) :=
      mul_le_mul_of_nonneg_right hm (div_nonneg (abs_nonneg _) (cellCount_pos T c.1).le)
    _ = |(s : ℝ) - t| := mul_div_cancel₀ _ (cellCount_pos T c.1).ne'

private theorem dist_dartChart_germs {d e : G.Dart} (hbase : d.fst = e.fst)
    (hed : d.edge ≠ e.edge) (s t : I) :
    dist (dartChart d s) (dartChart e t) = max (s : ℝ) (t : ℝ) := by
  rcases d with ⟨⟨v, a⟩, hva⟩
  rcases e with ⟨⟨w, b⟩, hwb⟩
  change v = w at hbase
  subst w
  have hab : a ≠ b := by
    intro h
    subst b
    exact hed rfl
  exact dist_edgeChart_incident G hva hwb hab s t

private theorem dist_target_endpoint (c : Cell T) (b : Bool) (t : I) :
    dist (target T c t) (target T c (endpoint b)) = (outgoingParameter b t : ℝ) := by
  rw [dist_target]
  cases b
  · change |(t : ℝ) - 0| = t
    rw [sub_zero, abs_of_nonneg t.2.1]
  · change |(t : ℝ) - 1| = 1 - (t : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr t.2.2)]
    ring

private theorem expands_on_meeting_cells (c d : Cell T) {s₀ t₀ : I}
    (h : source T c s₀ = source T d t₀) (s t : I) :
    (3 / 2 : ℝ) * dist (source T c s) (source T d t) ≤
      dist (edgeWalkMap T hconn (source T c s)) (edgeWalkMap T hconn (source T d t)) := by
  by_cases hcd : c = d
  · subst d
    exact (mul_le_mul_of_nonneg_right (by norm_num) dist_nonneg).trans
      (expands_on_cell T hconn c s t)
  obtain ⟨a, b, rfl, rfl, hbase, hed⟩ := distinct_cells_meet T c d hcd h
  let F := edgeWalkMap T hconn
  let x := source T c s
  let y := source T d t
  let z := source T c (endpoint a)
  have hx := expands_on_cell T hconn c s (endpoint a)
  have hy := expands_on_cell T hconn d t (endpoint b)
  rw [edgeWalkMap_source, edgeWalkMap_source, dist_target_endpoint] at hx hy
  have hgap : dist (F x) (F y) =
      max (outgoingParameter a s : ℝ) (outgoingParameter b t : ℝ) := by
    change dist (edgeWalkMap T hconn (source T c s))
      (edgeWalkMap T hconn (source T d t)) = _
    rw [edgeWalkMap_source, edgeWalkMap_source]
    change dist (dartChart (targetDart T c) s) (dartChart (targetDart T d) t) = _
    rw [← dartChart_outgoing (targetDart T c) a s, ← dartChart_outgoing (targetDart T d) b t]
    exact dist_dartChart_germs hbase (by simpa only [outgoingDart_edge] using hed) _ _
  change 3 * dist x z ≤ (outgoingParameter a s : ℝ) at hx
  rw [← h] at hy
  change 3 * dist y z ≤ (outgoingParameter b t : ℝ) at hy
  change (3 / 2 : ℝ) * dist x y ≤ dist (F x) (F y)
  have hx' := hx.trans (le_max_left (outgoingParameter a s : ℝ) (outgoingParameter b t : ℝ))
  have hy' := hy.trans (le_max_right (outgoingParameter a s : ℝ) (outgoingParameter b t : ℝ))
  rw [hgap]
  linarith [dist_triangle_right x y z]

/-- A uniform positive radius has singleton forward Bowen sets. -/
theorem forwardBowenBound_edgeWalkMap :
    ∃ ε > 0, ForwardBowenBound (edgeWalkMap T hconn) univ ε 1 := by
  refine EdgeSubdivisionDynamics.forwardBowenBound_one_of_compact_cells
    (fun c : Cell T => range (source T c)) (fun c => isCompact_range (continuous_source T c))
    ?_ (by norm_num : (1 : ℝ) < 3 / 2) ?_
  · intro x
    obtain ⟨a, ha⟩ := source_surjective T hconn x
    exact ⟨a.1, a.2, ha⟩
  · intro c d hmeet
    obtain ⟨z, ⟨s₀, hs₀⟩, ⟨t₀, ht₀⟩⟩ := hmeet
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact expands_on_meeting_cells T hconn c d (hs₀.trans ht₀.symm) s t

end Map

/-- On a finite connected nontrivial graph without leaves, the explicit
edge-walk map is continuous, topologically exact, and positively expansive. -/
theorem exists_exact_edgeWalkMap [Nontrivial V] (hconn : G.Connected)
    (hleaf : ∀ v, (G.neighborSet v).ncard ≠ 1) :
    ∃ f : Space G → Space G, Continuous f ∧ ExactPendantObstruction.TopologicallyExact f ∧
      ∃ ε > 0, ForwardBowenBound f univ ε 1 := by
  let T := chooseTours hconn hleaf
  exact ⟨edgeWalkMap T hconn, continuous_edgeWalkMap T hconn,
    topologicallyExact_edgeWalkMap T hconn, forwardBowenBound_edgeWalkMap T hconn⟩

/-- Finite connected nontrivial graphs admit continuous exact finitely positively
expansive dynamics precisely when no vertex has degree one. -/
theorem exists_exact_finitelyPositiveExpansive_iff [Nontrivial V] [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (∃ f : Space G → Space G, Continuous f ∧ ExactPendantObstruction.TopologicallyExact f ∧
      FinitelyPositiveExpansive f) ↔ ∀ v, G.degree v ≠ 1 := by
  constructor
  · rintro ⟨f, hf, hex, hF⟩ v hv
    exact (ExactPendantObstruction.not_finitelyPositiveExpansive
      (pendantArcOfDegreeOne G v hv) hf hex) hF
  · intro hleaf
    have hncard : ∀ v, (G.neighborSet v).ncard ≠ 1 := by
      simpa only [ncard_neighborSet] using hleaf
    obtain ⟨f, hf, hex, ε, hε, hb⟩ := exists_exact_edgeWalkMap hconn hncard
    exact ⟨f, hf, hex, ε, hε, 1, le_rfl, hb⟩

#print axioms exists_exact_edgeWalkMap
#print axioms exists_exact_finitelyPositiveExpansive_iff

end

end D5.S3.Combinatorics.Graph.LeaflessDynamics.FiniteGraphExactDynamics
