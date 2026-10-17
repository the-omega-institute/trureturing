/- GID: D5/S3/Geometry/Hyperideal/FlatPathAllocation
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatPathAllocation
   mirror-E: none(waiver:actual-flat-pi-multigraph)
   anchors: []
   utility: none
   digest: Multiplicity-preserving flat pi graph and allocation to actual face components. -/

import D5.S3.Geometry.Hyperideal.FlatComponentBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.Hyperideal.FlatPathAllocation

attribute [local instance] Classical.propDecidable

open D5.S3.Geometry.Hyperideal.FlatComponentBudget
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)

private theorem at_most_two_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hd : ∀ v, G.degree v ≤ 2) (v a b c : V)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) : c = a ∨ c = b := by
  classical
  by_contra h
  push_neg at h
  have hsub : ({a,b,c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simpa using ‹G.Adj v _›
  have hh := Finset.card_le_card hsub
  have hh' : 3 ≤ G.degree v := by
    simpa [hab, h.1.symm, h.2.symm] using hh
  have := hd v
  omega

/-- A leaf in a finite connected graph of maximum degree two starts a
simple path covering the entire connected graph. -/
private theorem spanning_path_of_leaf {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hconn : G.Connected) (hd : ∀ v, G.degree v ≤ 2) (u : V) (hu : G.degree u = 1) :
    ∃ v, ∃ w : G.Walk u v, w.IsPath ∧ ∀ z, z ∈ w.support := by
  classical
  let L : Set ℕ := {n | ∃ v, ∃ w : G.Walk u v, w.IsPath ∧ w.length = n}
  have hL : L.Finite := (Set.finite_lt_nat (Fintype.card V)).subset (by
    rintro n ⟨v,w,hw,rfl⟩
    exact hw.length_lt)
  obtain ⟨n, ⟨⟨v,w,hw,rfl⟩, hmax⟩⟩ := hL.exists_maximal
    ⟨0, ⟨u, SimpleGraph.Walk.nil, by simp⟩⟩
  have hwmax : ∀ v' (w' : G.Walk u v'), w'.IsPath → w'.length ≤ w.length := by
    intro v' w' hw'
    have hh := hmax ⟨v',w',hw',rfl⟩
    omega
  have hnil : ¬ w.Nil := by
    obtain ⟨a,ha,_⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
    have hh := hwmax a ha.toWalk ha.isPath_toWalk
    intro hn
    rw [hn.length_eq_zero] at hh
    simp at hh
  have hclosed : ∀ z ∈ w.support, ∀ y, G.Adj z y → y ∈ w.support := by
    intro z hz y hzy
    by_contra hy
    obtain ⟨i,hi,hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    by_cases hi0 : i = 0
    · have hzu : z = u := by simpa [hi0] using hi.symm
      have hzyu : G.Adj u y := hzu ▸ hzy
      obtain ⟨a,ha,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
      have heq : y = w.getVert 1 :=
        (hunique y hzyu).trans (hunique _ (by
          simpa using w.adj_getVert_succ (i := 0) (by
            simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hnil))).symm
      exact hy (heq ▸ w.getVert_mem_support 1)
    by_cases hiel : i = w.length
    · have hzv : z = v := by simpa [hiel] using hi.symm
      have hzyv : G.Adj v y := hzv ▸ hzy
      have hh := hwmax y (w.concat hzyv) (hw.concat hy hzyv)
      simp only [SimpleGraph.Walk.length_concat] at hh
      omega
    have him : i-1 < w.length := by omega
    have hip : i < w.length := by omega
    have ha : G.Adj z (w.getVert (i-1)) := by
      have hh := (w.adj_getVert_succ him).symm
      simpa [show i-1+1=i by omega, hi] using hh
    have hb : G.Adj z (w.getVert (i+1)) := by simpa [hi] using w.adj_getVert_succ hip
    have hab : w.getVert (i-1) ≠ w.getVert (i+1) := by
      intro h
      have hh := hw.getVert_injOn (by simp; omega) (by simp; omega) h
      omega
    rcases at_most_two_neighbors G hd z _ _ y ha hb hzy hab with h | h
    · exact hy (h ▸ w.getVert_mem_support _)
    · exact hy (h ▸ w.getVert_mem_support _)
  refine ⟨v,w,hw,?_⟩
  intro z
  obtain ⟨q⟩ := hconn.preconnected u z
  have hwalk : ∀ {a b} (q : G.Walk a b), a ∈ w.support → b ∈ w.support := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a b c hab q ih =>
      intro ha
      exact ih (hclosed a ha b hab)
  exact hwalk q w.start_mem_support

private theorem connected_leaf_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hd : ∀ v, 1 ≤ G.degree v ∧ G.degree v ≤ 2) :
    (Finset.univ.filter (fun v => G.degree v = 1)).card =
      if ∃ v, G.degree v = 1 then 2 else 0 := by
  classical
  let L := (Finset.univ.filter (fun v => G.degree v = 1)).card
  have hpoint : ∀ v, G.degree v + (if G.degree v = 1 then 1 else 0) = 2 := by
    intro v
    have := hd v
    split_ifs <;> omega
  have hidentity : (∑ v, G.degree v)+L = 2*Fintype.card V := by
    have hh := congrArg (fun f : V → ℕ => ∑ v, f v) (funext hpoint)
    simpa [Finset.sum_add_distrib,L,mul_comm] using hh
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hbound : Fintype.card V ≤ G.edgeFinset.card+1 := by
    simpa [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet,SimpleGraph.edgeFinset] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hLle : L ≤ 2 := by omega
  by_cases h : ∃ v, G.degree v = 1
  · have hLpos : 0 < L := Finset.card_pos.mpr (by
      obtain ⟨v,hv⟩ := h
      exact ⟨v,by simp [hv]⟩)
    simp only [if_pos h]
    change L = 2
    omega
  · simp only [if_neg h]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact h ⟨v,(Finset.mem_filter.mp hv).2⟩

private theorem component_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.degree v = G.degree v.val := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree,← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact {
    toFun := fun w => ⟨w.val.val,w.property⟩
    invFun := fun w => ⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.property w.property⟩,w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem component_path_iff_leaf {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hd : ∀ v, 1 ≤ G.degree v ∧ G.degree v ≤ 2)
    (C : G.ConnectedComponent) :
    (∃ u v : C, ∃ w : C.toSimpleGraph.Walk u v,
      w.IsPath ∧ (∀ z, z ∈ w.support) ∧ C.toSimpleGraph.degree u = 1 ∧
      C.toSimpleGraph.degree v = 1 ∧ u ≠ v) ↔
    ∃ u : C, G.degree u.val = 1 := by
  classical
  constructor
  · rintro ⟨u,v,w,hw,hcover,hu,hv,hne⟩
    exact ⟨u,by simpa [component_degree] using hu⟩
  · rintro ⟨u,hu⟩
    have hbounds : ∀ v : C, 1 ≤ C.toSimpleGraph.degree v ∧ C.toSimpleGraph.degree v ≤ 2 := by
      intro v
      simpa only [component_degree] using hd v.val
    have huleaf : C.toSimpleGraph.degree u = 1 := by simpa only [component_degree] using hu
    obtain ⟨v,w,hw,hcover⟩ := spanning_path_of_leaf C.toSimpleGraph
      C.connected_toSimpleGraph (fun v => (hbounds v).2) u huleaf
    have hnil : ¬ w.Nil := by
      obtain ⟨a,ha,_⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp huleaf
      intro h
      have heq := hcover a
      rw [SimpleGraph.Walk.nil_iff_support_eq.mp h] at heq
      have heq' : a = u := by simpa using heq
      exact ha.ne heq'.symm
    have hL := connected_leaf_count C.toSimpleGraph C.connected_toSimpleGraph hbounds
    have hhas : ∃ v : C, C.toSimpleGraph.degree v = 1 := ⟨u,huleaf⟩
    rw [if_pos hhas] at hL
    have hid : (∑ z : C, C.toSimpleGraph.degree z) + 2 = 2*Fintype.card C := by
      have hp : ∀ z : C, C.toSimpleGraph.degree z +
          (if C.toSimpleGraph.degree z = 1 then 1 else 0) = 2 := by
        intro z
        have hh := hbounds z
        split_ifs <;> omega
      have hh := congrArg (fun f : C → ℕ => ∑ z, f z) (funext hp)
      simpa [Finset.sum_add_distrib,hL,mul_comm] using hh
    have hcard : C.toSimpleGraph.edgeFinset.card+1 = Fintype.card C := by
      have hh := C.toSimpleGraph.sum_degrees_eq_twice_card_edges
      omega
    have htree : C.toSimpleGraph.IsTree := SimpleGraph.isTree_iff_connected_and_card.mpr
      ⟨C.connected_toSimpleGraph,by simpa [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet,SimpleGraph.edgeFinset] using hcard⟩
    have hv : C.toSimpleGraph.degree v = 1 := by
      apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      refine ⟨w.penultimate,(w.adj_penultimate hnil).symm,?_⟩
      intro z hz
      exact htree.isAcyclic.eq_penultimate_of_adj_end hw hz (hcover z)
    exact ⟨u,v,w,hw,hcover,huleaf,hv,hw.nil_iff_eq.not.mp hnil⟩

private def IsPathGraphComponent {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : G.ConnectedComponent) : Prop := by
  classical
  exact ∃ u v : C, ∃ w : C.toSimpleGraph.Walk u v,
    w.IsPath ∧ (∀ z, z ∈ w.support) ∧ C.toSimpleGraph.degree u = 1 ∧
      C.toSimpleGraph.degree v = 1 ∧ u ≠ v

private theorem total_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hd : ∀ v, 1 ≤ G.degree v ∧ G.degree v ≤ 2) :
    (Finset.univ.filter (fun v => G.degree v = 1)).card =
      2*Nat.card {C : G.ConnectedComponent // IsPathGraphComponent G C} := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hlocal : ∀ C : G.ConnectedComponent,
      ((Finset.univ.filter (fun v : V => G.degree v = 1)).filter
        (fun v => G.connectedComponentMk v = C)).card =
      if IsPathGraphComponent G C then 2 else 0 := by
    intro C
    have hbound : ∀ v : C, 1 ≤ C.toSimpleGraph.degree v ∧ C.toSimpleGraph.degree v ≤ 2 := by
      intro v
      simpa only [component_degree] using hd v.val
    have hcount := connected_leaf_count C.toSimpleGraph C.connected_toSimpleGraph hbound
    have hcard : ((Finset.univ.filter (fun v : V => G.degree v = 1)).filter
        (fun v => G.connectedComponentMk v = C)).card =
        (Finset.univ.filter (fun v : C => C.toSimpleGraph.degree v = 1)).card := by
      apply Finset.card_bij (fun v hv =>
        (⟨v,(Finset.mem_filter.mp hv).2⟩ : C))
      · intro v hv
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and,component_degree] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      · intro v hv w hw h
        exact congrArg Subtype.val h
      · intro v hv
        refine ⟨v.val,?_,by rfl⟩
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,component_degree] at hv ⊢
        exact ⟨hv,v.property⟩
    rw [hcard,hcount]
    have heq : (∃ v : C, C.toSimpleGraph.degree v = 1) ↔ IsPathGraphComponent G C := by
      change (∃ v : C, C.toSimpleGraph.degree v = 1) ↔
        (∃ u v : C, ∃ w : C.toSimpleGraph.Walk u v,
          w.IsPath ∧ (∀ z, z ∈ w.support) ∧ C.toSimpleGraph.degree u = 1 ∧
          C.toSimpleGraph.degree v = 1 ∧ u ≠ v)
      rw [component_path_iff_leaf G hd C]
      simp only [component_degree]
    simp only [heq]
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun v : V => G.degree v = 1))
    (Finset.univ : Finset G.ConnectedComponent) G.connectedComponentMk
  simp only [Finset.mem_univ,Finset.filter_true] at hh
  rw [← hh]
  simp_rw [hlocal]
  rw [show (∑ C : G.ConnectedComponent, if IsPathGraphComponent G C then 2 else 0) =
      2 * (Finset.univ.filter (IsPathGraphComponent G)).card by
        rw [Finset.sum_ite]
        simp [mul_comm]]
  congr 1
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

variable {T : Type*} [Fintype T]

private noncomputable instance edgeFintype (p : RawFacePairing T) : Fintype p.GlobalEdge := by
  classical
  unfold RawFacePairing.GlobalEdge
  exact Fintype.ofFinite _

private noncomputable instance edgeDecidableEq (p : RawFacePairing T) : DecidableEq p.GlobalEdge :=
  Classical.decEq _

abbrev FlatBlock (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) := {t // Flat p ell t}

def selected (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : FlatBlock p ell) : Fin 3 :=
  Classical.choose t.property

def slot (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (t : FlatBlock p ell) (b : Fin 2) : Fin 6 :=
  if b = 0 then (selected p ell t).castAdd 3 else (selected p ell t).natAdd 3

def endLabel (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (d : FlatBlock p ell × Fin 2) : p.GlobalEdge := p.edgeLabel d.1.val (slot p ell d.1 d.2)

abbrev PiVertex (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :=
  {e // 0 < m p ell (flats p ell) e}

private noncomputable instance flatFintype (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :
    Fintype (FlatBlock p ell) := by
  classical
  exact Fintype.ofFinite _

private noncomputable instance piFintype (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :
    Fintype (PiVertex p ell) := by
  classical
  exact Fintype.ofFinite _

abbrev SubdivisionVertex (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :=
  PiVertex p ell ⊕ (FlatBlock p ell × Fin 2)

/-- Each original flat-block edge is replaced by its own three-edge path.
The two private dart vertices distinguish parallel edges and the ends of a loop. -/
def subdivision (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :
    SimpleGraph (SubdivisionVertex p ell) where
  Adj u v := match u,v with
    | Sum.inl e, Sum.inl f => False
    | Sum.inl e, Sum.inr d => e.val = endLabel p ell d
    | Sum.inr d, Sum.inl e => e.val = endLabel p ell d
    | Sum.inr d, Sum.inr d' => d.1 = d'.1 ∧ d.2 ≠ d'.2
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [and_comm, ne_comm]⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

private theorem slot_injective (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (t : FlatBlock p ell) : Function.Injective (slot p ell t) := by
  intro b c h
  fin_cases b <;> fin_cases c <;> simp_all [slot, Fin.ext_iff]
  all_goals
    have hk := (selected p ell t).isLt
    omega

private theorem pi_iff_slot (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (t : FlatBlock p ell) (q : Fin 6) :
    angle p ell (t.val,q) = Real.pi ↔ ∃ b : Fin 2, slot p ell t b = q := by
  have hx : ∀ q, 1 < coordinates p ell t.val q :=
    fun q => Real.one_lt_cosh.mpr (ne_of_gt (hell _))
  have hpat := ((positive_classification (coordinates p ell t.val) hx).2.2
    (selected p ell t)).2.mp (Classical.choose_spec t.property)
  change D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.extendedAngle _ q = _ ↔ _
  rw [hpat]
  constructor
  · intro h
    split_ifs at h with hp
    · rcases hp with h | h
      · exact ⟨0, by simpa [slot] using h.symm⟩
      · exact ⟨1, by simpa [slot] using h.symm⟩
    · exact (Real.pi_ne_zero h.symm).elim
  · rintro ⟨b,rfl⟩
    fin_cases b <;> simp [slot]

def dartFiber (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :
    Finset (FlatBlock p ell × Fin 2) := by
  classical
  exact Finset.univ.filter (fun d => endLabel p ell d = e)

private theorem dartFiber_card (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (e : p.GlobalEdge) :
    (dartFiber p ell e).card = m p ell (flats p ell) e := by
  classical
  apply Finset.card_bij (fun d _ => (d.1.val,slot p ell d.1 d.2))
  · intro d hd
    have he := (Finset.mem_filter.mp hd).2
    simp only [piOccurrences, flatOccurrences, fiber, Finset.mem_filter, Finset.mem_univ,
      true_and, flats]
    exact ⟨⟨he, by simp [d.1.property]⟩,(pi_iff_slot p ell hell d.1 _).mpr ⟨d.2,rfl⟩⟩
  · intro d hd d' hd' heq
    have ht : d.1 = d'.1 := Subtype.ext (congrArg Prod.fst heq)
    apply Prod.ext ht
    have hs := congrArg Prod.snd heq
    rw [← ht] at hs
    exact slot_injective p ell d.1 hs
  · intro i hi
    have hangle := (Finset.mem_filter.mp hi).2
    have hflat := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hlabel := (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp hi).1).1).2
    let t : FlatBlock p ell := ⟨i.1,by simpa [flats] using hflat⟩
    obtain ⟨b,hb⟩ := (pi_iff_slot p ell hell t i.2).mp hangle
    refine ⟨(t,b),?_,?_⟩
    · simp only [dartFiber,Finset.mem_filter,Finset.mem_univ,true_and]
      change p.edgeLabel i.1 (slot p ell t b) = e
      simpa [hb,label] using hlabel
    · exact Prod.ext rfl hb

private theorem endLabel_positive (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (d : FlatBlock p ell × Fin 2) :
    0 < m p ell (flats p ell) (endLabel p ell d) := by
  rw [← dartFiber_card p ell hell]
  exact Finset.card_pos.mpr ⟨d,by simp [dartFiber]⟩

private theorem subdivision_degree_vertex (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (e : PiVertex p ell) :
    (subdivision p ell).degree (Sum.inl e) = m p ell (flats p ell) e.val := by
  classical
  have hn : (subdivision p ell).neighborFinset (Sum.inl e) =
      (dartFiber p ell e.val).image Sum.inr := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v with
    | inl v => simp [subdivision]
    | inr d => simp [subdivision,dartFiber,eq_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    Finset.card_image_of_injective _ Sum.inr_injective, dartFiber_card p ell hell]

private theorem subdivision_degree_dart (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (d : FlatBlock p ell × Fin 2) :
    (subdivision p ell).degree (Sum.inr d) = 2 := by
  classical
  let e : PiVertex p ell := ⟨endLabel p ell d,endLabel_positive p ell hell d⟩
  let d' : FlatBlock p ell × Fin 2 := (d.1,1-d.2)
  have hn : (subdivision p ell).neighborFinset (Sum.inr d) = {Sum.inl e,Sum.inr d'} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v with
    | inl v =>
      simp [subdivision,e,Subtype.ext_iff]
    | inr v =>
      rcases v with ⟨t,b⟩
      rcases d with ⟨u,c⟩
      fin_cases b <;> fin_cases c <;>
        simp [subdivision,d',Prod.ext_iff,eq_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hn]
  simp

private theorem subdivision_degree_bounds (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) :
    ∀ v, 1 ≤ (subdivision p ell).degree v ∧ (subdivision p ell).degree v ≤ 2 := by
  classical
  intro v
  cases v with
  | inl e =>
    rw [subdivision_degree_vertex p ell hell]
    refine ⟨e.property,?_⟩
    exact m_le_two p ell hsum (flats p ell) e.val
  | inr d => rw [subdivision_degree_dart p ell hell]; omega

def flatFaceSetoid (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :
    Setoid (FlatBlock p ell) where
  r t u := Relation.EqvGen (FaceStep p ell) t.val u.val
  iseqv := ⟨fun _ => .refl _,fun h => .symm _ _ h,fun h h' => .trans _ _ _ h h'⟩

abbrev FlatFaceComponent (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) :=
  Quotient (flatFaceSetoid p ell)

def faceClass (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : FlatBlock p ell) :
    FlatFaceComponent p ell := Quotient.mk _ t

def PathComponent (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : (subdivision p ell).ConnectedComponent) : Prop :=
  IsPathGraphComponent (subdivision p ell) C

def flatCount (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : ℕ := (flats p ell).card
def piVertexCount (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : ℕ := Nat.card (PiVertex p ell)
def faceComponentCount (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : ℕ :=
  Nat.card (FlatFaceComponent p ell)
def pathCount (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : ℕ :=
  Nat.card {C : (subdivision p ell).ConnectedComponent // PathComponent p ell C}

private theorem common_end_class (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (d d' : FlatBlock p ell × Fin 2) (he : endLabel p ell d = endLabel p ell d') :
    faceClass p ell d.1 = faceClass p ell d'.1 := by
  classical
  by_cases hdd : d = d'
  · simp [hdd]
  have hmem : d ∈ dartFiber p ell (endLabel p ell d) := by simp [dartFiber]
  have hmem' : d' ∈ dartFiber p ell (endLabel p ell d) := by simpa [dartFiber] using he.symm
  have hsub : ({d,d'} : Finset _) ⊆ dartFiber p ell (endLabel p ell d) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmem
    · exact Finset.mem_singleton.mp hx ▸ hmem'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hdd,dartFiber_card p ell hell] at hcard
  have hle := m_le_two p ell hsum (flats p ell) (endLabel p ell d)
  have hm : m p ell (flats p ell) (endLabel p ell d) = 2 := by omega
  have hs := saturated_support p ell hell hsum (endLabel p ell d) hm
    (d.1.val,slot p ell d.1 d.2) (d'.1.val,slot p ell d'.1 d'.2) rfl he.symm
  exact Quotient.sound (s := flatFaceSetoid p ell) hs.2.2.2

private def representative (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (e : PiVertex p ell) : FlatBlock p ell × Fin 2 :=
  Classical.choose (Finset.card_pos.mp (by
    rw [dartFiber_card p ell hell]
    exact e.property : 0 < (dartFiber p ell e.val).card))

private theorem representative_end (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (e : PiVertex p ell) :
    endLabel p ell (representative p ell hell e) = e.val := by
  have hpos : 0 < (dartFiber p ell e.val).card := by
    rw [dartFiber_card p ell hell]
    exact e.property
  have hmem : representative p ell hell e ∈ dartFiber p ell e.val := Classical.choose_spec
    (Finset.card_pos.mp hpos)
  exact (Finset.mem_filter.mp hmem).2

private def vertexClass (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) : SubdivisionVertex p ell → FlatFaceComponent p ell
  | Sum.inl e => faceClass p ell (representative p ell hell e).1
  | Sum.inr d => faceClass p ell d.1

private theorem vertexClass_adj (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (u v : SubdivisionVertex p ell) (h : (subdivision p ell).Adj u v) :
    vertexClass p ell hell u = vertexClass p ell hell v := by
  cases u with
  | inl e =>
    cases v with
    | inl f => exact h.elim
    | inr d =>
      exact common_end_class p ell hell hsum _ d
        ((representative_end p ell hell e).trans h)
  | inr d =>
    cases v with
    | inl e =>
      exact (common_end_class p ell hell hsum _ d
        ((representative_end p ell hell e).trans h)).symm
    | inr d' => exact congrArg (faceClass p ell) h.1

private def componentClass (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) :
    (subdivision p ell).ConnectedComponent → FlatFaceComponent p ell :=
  SimpleGraph.ConnectedComponent.lift (vertexClass p ell hell) (by
    intro u v w hw
    clear hw
    induction w with
    | nil => rfl
    | @cons u v w huv q ih => exact (vertexClass_adj p ell hell hsum _ _ huv).trans ih)

private theorem allocation_surjective (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (hdegree : ∀ e, 6 ≤ degree p e) :
    Function.Surjective (fun C : {C : (subdivision p ell).ConnectedComponent //
      PathComponent p ell C} => componentClass p ell hell hsum C.val) := by
  classical
  intro c
  induction c using Quotient.inductionOn with
  | h t =>
    obtain ⟨e,hmG,hmC,_,_⟩ := component_exposed_label p ell hell hsum hdegree t.val t.property
    let v : PiVertex p ell := ⟨e,by omega⟩
    let C := (subdivision p ell).connectedComponentMk (Sum.inl v)
    have hpath : PathComponent p ell C := by
      apply (component_path_iff_leaf (subdivision p ell)
        (subdivision_degree_bounds p ell hell hsum) C).mpr
      refine ⟨⟨Sum.inl v,rfl⟩,?_⟩
      exact (subdivision_degree_vertex p ell hell v).trans hmG
    refine ⟨⟨C,hpath⟩,?_⟩
    have hpos : 0 < (piOccurrences p ell (component p ell t.val) e).card := by
      change 0 < m p ell (component p ell t.val) e
      omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
    have ha := (Finset.mem_filter.mp hi).2
    have hCi := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hie := (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp hi).1).1).2
    have hcomp := (Finset.mem_filter.mp hCi).2
    let u : FlatBlock p ell := ⟨i.1,hcomp.2.1⟩
    obtain ⟨b,hb⟩ := (pi_iff_slot p ell hell u i.2).mp ha
    have he : endLabel p ell (u,b) = e := by simpa [endLabel,hb,label,u] using hie
    change faceClass p ell (representative p ell hell v).1 = faceClass p ell t
    calc
      _ = faceClass p ell u := common_end_class p ell hell hsum _ (u,b)
        ((representative_end p ell hell v).trans he.symm)
      _ = _ := Quotient.sound (s := flatFaceSetoid p ell) hcomp.2.2.symm

private theorem graph_count (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) :
    piVertexCount p ell = flatCount p ell + pathCount p ell := by
  classical
  let G := subdivision p ell
  let L := (Finset.univ.filter (fun v => G.degree v = 1)).card
  have hf : Fintype.card (FlatBlock p ell) = flatCount p ell := by
    simp [FlatBlock,flatCount,flats,Fintype.card_subtype]
  have hm : (∑ e : p.GlobalEdge, m p ell (flats p ell) e) =
      2*flatCount p ell := by
    have hh := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (FlatBlock p ell × Fin 2))
      (Finset.univ : Finset p.GlobalEdge) (endLabel p ell)
    simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ] at hh
    have hh' : ∑ e : p.GlobalEdge, (dartFiber p ell e).card =
        Fintype.card (FlatBlock p ell × Fin 2) := hh
    simpa [dartFiber_card p ell hell,Fintype.card_prod,hf,mul_comm] using hh'
  have hm' : (∑ e : PiVertex p ell, m p ell (flats p ell) e.val) =
      2*flatCount p ell := by
    rw [← Finset.sum_subtype (Finset.univ.filter
      (fun e => 0 < m p ell (flats p ell) e)) (by simp)]
    rw [Finset.sum_filter]
    convert hm using 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with h
    · rfl
    · have hz : m p ell (flats p ell) e = 0 := by omega
      exact hz.symm
  have hsumdeg : ∑ v, G.degree v = 6*flatCount p ell := by
    rw [Fintype.sum_sum_type]
    simp only [G,subdivision_degree_vertex p ell hell,subdivision_degree_dart p ell hell]
    rw [hm']
    simp [Fintype.card_prod,hf]
    omega
  have hcard : Fintype.card (SubdivisionVertex p ell) =
      piVertexCount p ell+2*flatCount p ell := by
    simp [SubdivisionVertex,Fintype.card_sum,Fintype.card_prod,hf,
      piVertexCount,Nat.card_eq_fintype_card,mul_comm]
  have hdeficit : (∑ v, G.degree v)+L = 2*Fintype.card (SubdivisionVertex p ell) := by
    have hp : ∀ v, G.degree v+(if G.degree v = 1 then 1 else 0) = 2 := by
      intro v
      have hh : 1 ≤ G.degree v ∧ G.degree v ≤ 2 := subdivision_degree_bounds p ell hell hsum v
      split_ifs <;> omega
    have hh := congrArg (fun f : SubdivisionVertex p ell → ℕ => ∑ v, f v) (funext hp)
    simpa [Finset.sum_add_distrib,L,mul_comm] using hh
  have hpaths : L = 2*pathCount p ell := total_leaves G
    (subdivision_degree_bounds p ell hell hsum)
  rw [hsumdeg,hcard,hpaths] at hdeficit
  omega

/-- Complete counting and endpoint conclusion on the original face-generated
edge quotient and its one common positive generalized length field. -/
theorem complete_flat_counting (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (hdegree : ∀ e, 6 ≤ degree p e) (hF : (flats p ell).Nonempty) :
    piVertexCount p ell = flatCount p ell + pathCount p ell ∧
    faceComponentCount p ell ≤ pathCount p ell ∧
    1 ≤ faceComponentCount p ell ∧
    flatCount p ell ≤ piVertexCount p ell-faceComponentCount p ell ∧
    piVertexCount p ell-faceComponentCount p ell ≤ Nat.card p.GlobalEdge-faceComponentCount p ell ∧
    ∀ t : T, Flat p ell t → ∃ e₀ e₁ : p.GlobalEdge, e₀ ≠ e₁ ∧
      Endpoint p ell (component p ell t) e₀ ∧ Endpoint p ell (component p ell t) e₁ := by
  classical
  have hcount := graph_count p ell hell hsum
  have halloc : faceComponentCount p ell ≤ pathCount p ell :=
    Nat.card_le_card_of_surjective _ (allocation_surjective p ell hell hsum hdegree)
  have hcpos : 1 ≤ faceComponentCount p ell := by
    obtain ⟨t,ht⟩ := hF
    have ht' : Flat p ell t := by simpa [flats] using ht
    letI : Nonempty (FlatFaceComponent p ell) := ⟨faceClass p ell ⟨t,ht'⟩⟩
    exact Nat.card_pos
  have hv : piVertexCount p ell ≤ Nat.card p.GlobalEdge :=
    Nat.card_le_card_of_injective (fun e : PiVertex p ell => e.val) Subtype.val_injective
  refine ⟨hcount,halloc,hcpos,by omega,by omega,?_⟩
  intro t ht
  exact component_endpoints p ell hell hsum hdegree t ht

#print axioms complete_flat_counting

end D5.S3.Geometry.Hyperideal.FlatPathAllocation
