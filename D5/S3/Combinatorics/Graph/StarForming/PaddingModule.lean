/- GID: D5/S3/Combinatorics/Graph/StarForming/PaddingModule
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PaddingModule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual arbitrary-size Heawood padding modules with strict independent compensation. -/

import D5.S3.Combinatorics.Graph.StarForming.FourPortCore
import D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts

/-! The local module of CUBIC_EQUALITY_PADDING_RINGS, at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The cut core and broken Heawood block are disjoint actual
vertex sets. Both remaining ring ports are unrestricted in the upper bound. -/
namespace D5.S3.Combinatorics.Graph.StarForming.PaddingModule
open StarFormingDissociationRefutation
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Vertex (I : Type) := Fin 14 ⊕ (I × Fin 20)

def adjacency (e : Equiv.Perm I) (mark : I) : Vertex I → Vertex I → Prop
  | .inl v,.inl w => HeawoodPorts.graph.Adj v w
  | .inr x,.inr y => (FourPortCore.graph e mark).Adj x y
  | .inl v,.inr y => y.1=mark ∧ ((v=0 ∧ y.2=13) ∨ (v=8 ∧ y.2=12))
  | .inr x,.inl w => x.1=mark ∧ ((w=0 ∧ x.2=13) ∨ (w=8 ∧ x.2=12))

def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (Vertex I) where
  Adj := adjacency e mark
  symm := ⟨by
    intro x y h
    cases x with
    | inl v => cases y with
      | inl w => exact HeawoodPorts.graph.adj_symm h
      | inr y => exact h
    | inr x => cases y with
      | inl w => exact h
      | inr y => exact (FourPortCore.graph e mark).adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl v => exact HeawoodPorts.graph.irrefl h
    | inr x => exact (FourPortCore.graph e mark).irrefl h⟩

instance (e : Equiv.Perm I) (mark : I) : DecidableRel (graph e mark).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [graph,adjacency] <;> infer_instance

/-- Restriction to the disjoint actual components preserves dissociation. -/
theorem restrictions (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph e mark) 2 D) :
    IsKIndependent HeawoodPorts.graph 2 D.toLeft ∧
      IsKIndependent (FourPortCore.graph e mark) 2 D.toRight := by
  have h := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
  constructor
  · apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro v hv a ha b hb hva hvb
    have he := h (.inl v) (by simpa using hv) (.inl a) (by simpa using ha)
      (.inl b) (by simpa using hb) hva hvb
    exact Sum.inl.inj he
  · apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro v hv a ha b hb hva hvb
    have he := h (.inr v) (by simpa using hv) (.inr a) (by simpa using ha)
      (.inr b) (by simpa using hb) hva hvb
    exact Sum.inr.inj he

private theorem saturated_omits (e : Equiv.Perm I) (mark : I)
    (D : Finset (Vertex I)) (hD : IsKIndependent (graph e mark) 2 D)
    (h8 : D.toLeft.card=8) : Disjoint D.toRight (FourPortCore.pair mark false) := by
  have hf := (HeawoodPorts.facts D.toLeft (restrictions e mark D hD).1).2 h8
  have h := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
  have hmiss (p : Fin 14) (x : Fin 20) (hp : p ∈ D.toLeft)
      (hc : DegreeCapacity.selectedDegree HeawoodPorts.graph D.toLeft p=1)
      (hedge : (graph e mark).Adj (.inl p) (.inr (mark,x))) : (mark,x) ∉ D.toRight := by
    intro hx
    have hpos : (D.toLeft.filter (HeawoodPorts.graph.Adj p)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < DegreeCapacity.selectedDegree HeawoodPorts.graph D.toLeft p
      omega
    obtain ⟨a,ha⟩ := hpos
    have he := h (.inl p) (by simpa using hp) (.inl a)
      (by simpa using (Finset.mem_filter.mp ha).1) (.inr (mark,x)) (by simpa using hx)
      (Finset.mem_filter.mp ha).2 hedge
    cases he
  have h12 := hmiss 8 12 hf.2.1 hf.2.2.2 (by simp [graph,adjacency])
  have h13 := hmiss 0 13 hf.1 hf.2.2.1 (by simp [graph,adjacency])
  apply Finset.disjoint_left.mpr
  intro x hx hp
  simp only [FourPortCore.pair, Bool.false_eq_true, ↓reduceIte,
    Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact h12 hx
  · exact h13 hx

/-- Each saturated Heawood eight-set pays its own strictly lost core vertex;
neither remaining open ring port is restricted. -/
theorem beta_cap (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 7+12*Fintype.card I := by
  have hr := restrictions e mark D hD
  have hb := (HeawoodPorts.facts D.toLeft hr.1).1
  have hc := FourPortCore.card_bound e mark D.toRight hr.2
  have hs := Finset.card_toLeft_add_card_toRight (u := D)
  by_cases h8 : D.toLeft.card=8
  · have hstrict := FourPortCore.omitted_pair_strict e mark D.toRight hr.2 false
      (saturated_omits e mark D hD h8)
    omega
  · omega

def forming : Finset (Vertex I) := HeawoodParameters.selectedSet.disjSum EqualityCore.S
def independent : Finset (Vertex I) :=
  ({0,1,2,3,4,5,6} : Finset (Fin 14)).disjSum EqualityCore.D

private theorem forming_original (e : Equiv.Perm I) :
    IsMinimalStarForming (HeawoodParameters.graph ⊕g EqualityCore.graph e) 2 forming := by
  apply (minimalStarForming_sum_iff _ _ _ _).mpr
  simp only [forming,Finset.toLeft_disjSum,Finset.toRight_disjSum]
  refine ⟨?_,EqualityCore.S_minimal e⟩
  apply (regular_minimal_iff _ _).mp
  simpa [HeawoodParameters.graph,HeawoodParameters.selectedSet] using Cubic.fano_minimal

private theorem forming_edge_agreement (e : Equiv.Perm I) (mark : I)
    (x y : Vertex I) (h : x ∈ forming ∨ y ∈ forming) :
    (HeawoodParameters.graph ⊕g EqualityCore.graph e).Adj x y ↔ (graph e mark).Adj x y := by
  cases x with
  | inl v => cases y with
    | inl w =>
      have hh : ∀ v w : Fin 14, Cubic.fanoSelected v ∨ Cubic.fanoSelected w →
          (Cubic.FanoAdj v w ↔ Cubic.BrokenAdj v w) := by
        unfold Cubic.FanoAdj Cubic.BrokenAdj Cubic.fanoSelected
          Cubic.brokenNeighbors Cubic.fanoNeighbors
        decide +kernel
      exact hh v w (by simpa [forming,HeawoodParameters.selectedSet] using h)
    | inr y =>
      have hv : v≠0 ∧ v≠8 ∨ y.2.val<12 := by
        rcases h with h | h
        · left
          have hs : Cubic.fanoSelected v := by simpa [forming,HeawoodParameters.selectedSet] using h
          constructor <;> intro he <;> subst v <;> simp [Cubic.fanoSelected] at hs
        · right; simpa [forming,EqualityCore.S,EqualityCore.selected] using h
      simp only [SimpleGraph.sum_adj, Bool.false_eq_true] 
      change False ↔ y.1=mark ∧ ((v=0 ∧ y.2=13) ∨ (v=8 ∧ y.2=12))
      rcases hv with ⟨h0,h8⟩ | hy
      · simp [h0,h8]
      · constructor
        · exact False.elim
        · rintro ⟨_,(⟨_,hy'⟩ | ⟨_,hy'⟩)⟩ <;> rw [hy'] at hy <;> norm_num at hy
  | inr x => cases y with
    | inl w =>
      have hx : x.2.val<12 ∨ w≠0 ∧ w≠8 := by
        rcases h with h | h
        · left; simpa [forming,EqualityCore.S,EqualityCore.selected] using h
        · right
          have hs : Cubic.fanoSelected w := by simpa [forming,HeawoodParameters.selectedSet] using h
          constructor <;> intro he <;> subst w <;> simp [Cubic.fanoSelected] at hs
      simp only [SimpleGraph.sum_adj, Bool.false_eq_true] 
      change False ↔ x.1=mark ∧ ((w=0 ∧ x.2=13) ∨ (w=8 ∧ x.2=12))
      rcases hx with hx | ⟨h0,h8⟩
      · constructor
        · exact False.elim
        · rintro ⟨_,(⟨_,hx'⟩ | ⟨_,hx'⟩)⟩ <;> rw [hx'] at hx <;> norm_num at hx
      · simp [h0,h8]
    | inr y =>
      have hs : x.2.val<12 ∨ y.2.val<12 := by
        simpa [forming,EqualityCore.S,EqualityCore.selected] using h
      have hn : ¬ FourPortCore.cut mark x y := by
        rintro ⟨_,_,(⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩)⟩ <;>
          rcases hs with hs | hs
        all_goals simp_all <;> omega
      change _ ↔ _ ∧ ¬ FourPortCore.cut mark x y
      exact (and_iff_left hn).symm

/-- Every modified edge is outside the full original selection, so all
covering and deletion tests survive on this actual open module. -/
theorem forming_minimal (e : Equiv.Perm I) (mark : I) :
    IsMinimalStarForming (graph e mark) 2 forming := by
  apply (regular_minimal_iff _ _).mp
  exact Cubic.minimal_rewiring_forward _ _ _ (forming_edge_agreement e mark)
    ((regular_minimal_iff _ _).mpr (forming_original e))

theorem forming_card : (forming : Finset (Vertex I)).card=8+12*Fintype.card I := by
  rw [forming,Finset.card_disjSum,EqualityCore.selected_card]
  have hh : HeawoodParameters.selectedSet.card=8 := by decide +kernel
  rw [hh]

def neighbors (e : Equiv.Perm I) (mark : I) : Vertex I → Finset (Vertex I)
  | .inl v => (Cubic.brokenNeighbors v).toFinset.map Function.Embedding.inl ∪
      (if v=0 then {Sum.inr (mark,13)} else
       if v=8 then {Sum.inr (mark,12)} else ∅)
  | .inr x => ((EqualityCore.neighbors e x).filter (fun y => ¬ FourPortCore.cut mark x y)).map
      Function.Embedding.inr ∪
      (if x=(mark,12) then {Sum.inl 8} else
       if x=(mark,13) then {Sum.inl 0} else ∅)

set_option maxHeartbeats 1200000 in
theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : Vertex I) :
    y ∈ neighbors e mark x ↔ (graph e mark).Adj x y := by
  cases x with
  | inl v => cases y with
    | inl w =>
      simp [neighbors,graph,adjacency,HeawoodPorts.graph,Cubic.BrokenAdj] <;>
        split_ifs <;> simp_all
    | inr y =>
      by_cases h0 : v=0 <;> by_cases h8 : v=8 <;>
        simp [neighbors,graph,adjacency,h0,h8,Prod.ext_iff,eq_comm]
  | inr x => cases y with
    | inl w =>
      by_cases h12 : x=(mark,12) <;> by_cases h13 : x=(mark,13) <;>
        simp_all [neighbors,graph,adjacency,Prod.ext_iff,eq_comm] <;>
          split_ifs <;> simp_all <;> tauto
    | inr y => simp [neighbors,graph,adjacency,FourPortCore.graph,
        EqualityCore.mem_neighbors] <;> split_ifs <;> simp_all

def leftPort (mark : I) : Vertex I := .inr (mark,14)
def rightPort (mark : I) : Vertex I := .inr (mark,15)

/-- The two remaining cut endpoints have degree two and every other actual
vertex has degree three. -/
theorem degree (e : Equiv.Perm I) (mark : I) (x : Vertex I) :
    DegreeCapacity.degree (graph e mark) x =
      if x=leftPort mark ∨ x=rightPort mark then 2 else 3 := by
  have he : Finset.univ.filter ((graph e mark).Adj x)=neighbors e mark x := by
    ext y; simp [mem_neighbors]
  change (Finset.univ.filter _).card=_
  rw [he]
  cases x with
  | inl v =>
    fin_cases v <;> simp [neighbors,Cubic.brokenNeighbors,Cubic.fanoNeighbors,
      leftPort,rightPort]
  | inr x =>
    rcases x with ⟨i,v⟩
    by_cases hi : i=mark
    · subst i
      fin_cases v <;> simp [neighbors,EqualityCore.neighbors,FourPortCore.cut,
        leftPort,rightPort,Finset.filter_insert,Finset.filter_singleton]
    · fin_cases v <;> simp [neighbors,EqualityCore.neighbors,FourPortCore.cut,
        leftPort,rightPort,hi,Finset.filter_insert,Finset.filter_singleton]

def color : Vertex I → Bool
  | .inl v => decide (7 ≤ v.val)
  | .inr x => EqualityCore.color x.2

/-- The actual point/line coloring agrees with the periodic core coloring
across both new attachment edges. -/
theorem proper_color (e : Equiv.Perm I) (mark : I) (x y : Vertex I)
    (h : (graph e mark).Adj x y) : color x ≠ color y := by
  cases x with
  | inl v => cases y with
    | inl w =>
      have hh : ∀ v w : Fin 14, HeawoodPorts.graph.Adj v w →
          decide (7 ≤ v.val) ≠ decide (7 ≤ w.val) := by decide +kernel
      exact hh v w h
    | inr y =>
      rcases h with ⟨hm,(⟨rfl,hy⟩ | ⟨rfl,hy⟩)⟩ <;>
        simp [color,EqualityCore.color,hy]
  | inr x => cases y with
    | inl w =>
      rcases h with ⟨hm,(⟨rfl,hx⟩ | ⟨rfl,hx⟩)⟩ <;>
        simp [color,EqualityCore.color,hx]
    | inr y =>
      have h' : (EqualityCore.graph e).Adj x y := h.1
      rcases h' with ⟨_,h'⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩
      · have hh : ∀ v w : Fin 20, EqualityCore.internal v w →
            EqualityCore.color v ≠ EqualityCore.color w := by decide +kernel
        exact hh _ _ h'
      all_goals simp [color,EqualityCore.color,hx,hy]

theorem bipartite (e : Equiv.Perm I) (mark : I) : (graph e mark).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => if color x then (1 : Fin 2) else 0) ?_⟩
  intro x y h he
  have hn := proper_color e mark x y h
  cases hx : color x <;> cases hy : color y <;> simp_all

private theorem independent_edge (e : Equiv.Perm I) (mark : I)
    (x y : Vertex I) (hx : x ∈ independent) (hy : y ∈ independent)
    (h : (graph e mark).Adj x y) :
    (HeawoodPorts.graph ⊕g EqualityCore.graph e).Adj x y := by
  cases x with
  | inl v => cases y with
    | inl w => exact h
    | inr y =>
      rcases h with ⟨_,(⟨rfl,hy'⟩ | ⟨rfl,hy'⟩)⟩ <;>
        simp_all [independent,EqualityCore.D,EqualityCore.dissociation]
  | inr x => cases y with
    | inl w =>
      rcases h with ⟨_,(⟨rfl,hx'⟩ | ⟨rfl,hx'⟩)⟩ <;>
        simp_all [independent,EqualityCore.D,EqualityCore.dissociation]
    | inr y => exact h.1

/-- The original all-points and periodic matching witness attains the cap. -/
theorem independent_valid (e : Equiv.Perm I) (mark : I) :
    IsKIndependent (graph e mark) 2 independent := by
  have hs : IsKIndependent (HeawoodPorts.graph ⊕g EqualityCore.graph e) 2 independent := by
    apply (independent_sum_iff _ _ _ _).mpr
    simp only [independent,Finset.toLeft_disjSum,Finset.toRight_disjSum]
    exact ⟨by decide +kernel,EqualityCore.D_valid e⟩
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hs
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro v hv a ha b hb hva hvb
  exact hh v hv a ha b hb (independent_edge e mark v a hv ha hva)
    (independent_edge e mark v b hv hb hvb)

theorem independent_card : (independent : Finset (Vertex I)).card=7+12*Fintype.card I := by
  rw [independent,Finset.card_disjSum,EqualityCore.dissociation_card]
  congr 1

end D5.S3.Combinatorics.Graph.StarForming.PaddingModule
