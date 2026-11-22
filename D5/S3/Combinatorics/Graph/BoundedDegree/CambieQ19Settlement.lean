/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: The cycle with two pendant paths and a bridged triangle in Question 1.9. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! The support and tree configurations for the fixed graph in the counterexample to
Question 1.9 of Cambie, Jooken and Wagner (arXiv:2508.20593v2). -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open SimpleGraph
open scoped BigOperators

/-- The actual tree subgraphs of order k. The vertices are part of each subgraph. -/
abbrev SubtreesOfOrder {V : Type} (G : SimpleGraph V) (k : ℕ) :=
  {H : G.Subgraph // H.coe.IsTree ∧ Nat.card H.verts = k}

/-- The source's subtree count. -/
noncomputable def subtreeCount {V : Type} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (SubtreesOfOrder G k)

/-- The source's total number of subtrees. -/
noncomputable def totalSubtreeCount {V : Type} (G : SimpleGraph V) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (Nat.card V), subtreeCount G k

/-- The source's sum of orders of subtrees. -/
noncomputable def totalSubtreeOrder {V : Type} (G : SimpleGraph V) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (Nat.card V), k * subtreeCount G k

/-- The subtree mean over the exact rationals. -/
noncomputable def meanSubtreeOrder {V : Type} (G : SimpleGraph V) : ℚ :=
  (totalSubtreeOrder G : ℚ) / (totalSubtreeCount G : ℚ)

/-- Vertex sets whose induced graph is connected. -/
abbrev ConnectedSets {V : Type} (G : SimpleGraph V) :=
  {S : Set V // (G.induce S).Connected}

/-- The mean order of a connected induced vertex set. -/
noncomputable def meanConnectedOrder {V : Type} [Finite V] (G : SimpleGraph V) : ℚ := by
  letI : Fintype (ConnectedSets G) := Fintype.ofFinite _
  exact (↑(∑ S : ConnectedSets G, Nat.card S.val) : ℚ) /
    (Nat.card (ConnectedSets G) : ℚ)

/-- Question 1.9 for every finite simple connected graph. -/
def claim : Prop :=
  ∀ (V : Type) (finiteV : Finite V) (G : SimpleGraph V),
    G.Connected → @meanConnectedOrder V finiteV G ≤ meanSubtreeOrder G

/-- Join two disjoint graphs by one edge between the specified vertices. -/
private def joinAt {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B) :
    SimpleGraph (A ⊕ B) :=
  (G ⊕g H) ⊔ edge (Sum.inl a) (Sum.inr b)

private theorem joinAt_inl {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (x y : A) : (joinAt G H a b).Adj (.inl x) (.inl y) ↔ G.Adj x y := by
  simp [joinAt, sup_adj, edge_adj]

private theorem joinAt_inr {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (x y : B) : (joinAt G H a b).Adj (.inr x) (.inr y) ↔ H.Adj x y := by
  simp [joinAt, sup_adj, edge_adj]

private theorem joinAt_cross {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (x : A) (y : B) : (joinAt G H a b).Adj (.inl x) (.inr y) ↔ x = a ∧ y = b := by
  simp [joinAt, sup_adj, edge_adj]

private theorem joinAt_connected {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (hG : G.Connected) (hH : H.Connected) (a : A) (b : B) :
    (joinAt G H a b).Connected := by
  let left : G →g joinAt G H a b :=
    ⟨Sum.inl, fun h => (joinAt_inl G H a b _ _).mpr h⟩
  let right : H →g joinAt G H a b :=
    ⟨Sum.inr, fun h => (joinAt_inr G H a b _ _).mpr h⟩
  have cross : (joinAt G H a b).Reachable (.inl a) (.inr b) :=
    ((joinAt_cross G H a b a b).mpr ⟨rfl, rfl⟩).reachable

  haveI : Nonempty (A ⊕ B) := ⟨.inl a⟩
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y => exact (hG x y).map left
    | inr y => exact ((hG x a).map left).trans (cross.trans ((hH b y).map right))
  | inr x =>
    cases y with
    | inl y => exact ((hH x b).map right).trans (cross.symm.trans ((hG a y).map left))
    | inr y => exact (hH x y).map right

/-- The vertices of the core, followed by the two paths and the triangle. -/
abbrev Vertex := ((Fin 5000 ⊕ Fin 500) ⊕ Fin 500) ⊕ Fin 3

private abbrev core (x : Fin 5000) : Vertex := .inl (.inl (.inl x))
private abbrev firstPath (x : Fin 500) : Vertex := .inl (.inl (.inr x))
private abbrev secondPath (x : Fin 500) : Vertex := .inl (.inr x)
private abbrev triangle (x : Fin 3) : Vertex := .inr x

/-- The actual 5,000-cycle with two 500-vertex pendant paths and a bridged triangle. -/
def G₅₀₀ : SimpleGraph Vertex :=
  joinAt
    (joinAt (joinAt (cycleGraph 5000) (pathGraph 500) 0 0)
      (pathGraph 500) (.inl 1000) 0)
    (cycleGraph 3) (.inl (.inl 500)) 0

/-- All four blocks belong to the same connected graph. -/
theorem G₅₀₀_connected : G₅₀₀.Connected :=
  joinAt_connected
    (joinAt_connected
      (joinAt_connected (connected_cycleGraph_add_one (n := 4999))
        (connected_pathGraph_add_one 499) 0 0)
      (connected_pathGraph_add_one 499) (.inl 1000) 0)
    (connected_cycleGraph_add_one (n := 2)) (.inl (.inl 500)) 0

#print axioms G₅₀₀_connected


section Join

variable {A B : Type}

private theorem left_preconnected {K : SimpleGraph (A ⊕ B)}
    (h : K.Preconnected)
    (hu : ∀ x y x' y', K.Adj (.inl x) (.inr y) → K.Adj (.inl x') (.inr y') → x = x') :
    (K.comap Sum.inl).Preconnected := by
  classical
  intro u v
  let a := if hex : ∃ x y, K.Adj (.inl x) (.inr y) then hex.choose else u
  let f : A ⊕ B → A := Sum.elim id (fun _ => a)
  have ha (x : A) (y : B) (hxy : K.Adj (.inl x) (.inr y)) : x = a := by
    have hex : ∃ x y, K.Adj (.inl x) (.inr y) := ⟨x, y, hxy⟩
    obtain ⟨y', hy'⟩ := hex.choose_spec
    simpa only [a, dite_eq_left hex] using hu x y hex.choose y' hxy hy'
  have hf {x y} (hxy : K.Adj x y) : (K.comap Sum.inl).Reachable (f x) (f y) := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact (show (K.comap Sum.inl).Adj x y from hxy).reachable
      | inr y =>
        change (K.comap Sum.inl).Reachable x a
        rw [ha x y hxy]
    | inr x =>
      cases y with
      | inl y =>
        change (K.comap Sum.inl).Reachable a y
        rw [ha y x hxy.symm]
      | inr y => exact .rfl
  rw [reachable_iff_reflTransGen]
  exact (reachable_iff_reflTransGen ..).mp (h (.inl u) (.inl v)) |>.lift' f
    (fun _ _ hxy => (reachable_iff_reflTransGen ..).mp (hf hxy))

private theorem right_preconnected {K : SimpleGraph (A ⊕ B)}
    (h : K.Preconnected)
    (hu : ∀ x y x' y', K.Adj (.inl x) (.inr y) → K.Adj (.inl x') (.inr y') → y = y') :
    (K.comap Sum.inr).Preconnected := by
  let L := K.comap (Equiv.sumComm B A)
  have hIso : L ≃g K := ⟨Equiv.sumComm B A, Iff.rfl⟩
  have hL : L.Preconnected := fun x y => hIso.reachable_iff.mp (h _ _)
  exact left_preconnected hL (fun x y x' y' hxy hxy' =>
    hu y x y' x' hxy.symm hxy'.symm)

private theorem cross_exists {K : SimpleGraph (A ⊕ B)} {x : A} {y : B}
    (h : K.Reachable (.inl x) (.inr y)) : ∃ u v, K.Adj (.inl u) (.inr v) := by
  obtain ⟨p⟩ := h
  obtain ⟨d, _, hd₁, hd₂⟩ := p.exists_boundary_dart (Set.range Sum.inl) (by simp) (by simp)
  obtain ⟨u, hu⟩ := hd₁
  have hr : d.snd ∈ Set.range Sum.inr := by
    cases he : d.snd with
    | inl w => exact (hd₂ ⟨w, he.symm⟩).elim
    | inr w => exact ⟨w, rfl⟩
  obtain ⟨v, hv⟩ := hr
  exact ⟨u, v, hu ▸ hv ▸ d.adj⟩

private theorem connected_of_sides {K : SimpleGraph (A ⊕ B)}
    (hn : Nonempty (A ⊕ B))
    (hl : (K.comap Sum.inl).Preconnected) (hr : (K.comap Sum.inr).Preconnected)
    (hc : A → B → ∃ u v, K.Adj (.inl u) (.inr v)) :
    K.Connected := by
  let left : K.comap Sum.inl →g K := ⟨Sum.inl, id⟩
  let right : K.comap Sum.inr →g K := ⟨Sum.inr, id⟩
  have cross (x : A) (y : B) : K.Reachable (.inl x) (.inr y) := by
    obtain ⟨u, v, huv⟩ := hc x y
    exact ((hl x u).map left).trans (huv.reachable.trans ((hr v y).map right))
  exact ⟨fun x y => by
    rcases x with x | x <;> rcases y with y | y
    · exact (hl x y).map left
    · exact cross x y
    · exact (cross y x).symm
    · exact (hr x y).map right⟩

private abbrev leftSet (S : Set (A ⊕ B)) : Set A := Sum.inl ⁻¹' S
private abbrev rightSet (S : Set (A ⊕ B)) : Set B := Sum.inr ⁻¹' S

private abbrev splitGraph (K : SimpleGraph (A ⊕ B)) (S : Set (A ⊕ B)) :
    SimpleGraph (leftSet S ⊕ rightSet S) :=
  (K.induce S).comap (Equiv.subtypeSum (p := (· ∈ S))).symm

private def splitIso (K : SimpleGraph (A ⊕ B)) (S : Set (A ⊕ B)) :
    splitGraph K S ≃g K.induce S :=
  ⟨(Equiv.subtypeSum (p := (· ∈ S))).symm, Iff.rfl⟩

private theorem splitGraph_inl (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (S : Set (A ⊕ B)) :
    (splitGraph (joinAt G H a b) S).comap Sum.inl = G.induce (leftSet S) := by
  ext x y
  exact joinAt_inl G H a b x y

private theorem splitGraph_inr (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (S : Set (A ⊕ B)) :
    (splitGraph (joinAt G H a b) S).comap Sum.inr = H.induce (rightSet S) := by
  ext x y
  exact joinAt_inr G H a b x y

private theorem splitGraph_cross (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B)
    (S : Set (A ⊕ B)) (x : leftSet S) (y : rightSet S) :
    (splitGraph (joinAt G H a b) S).Adj (.inl x) (.inr y) ↔ x.val = a ∧ y.val = b :=
  joinAt_cross G H a b x y

private theorem joinAt_induce_connected {G : SimpleGraph A} {H : SimpleGraph B}
    (a : A) (b : B) (S : Set (A ⊕ B)) :
    ((joinAt G H a b).induce S).Connected ↔
      S.Nonempty ∧ (G.induce (leftSet S)).Preconnected ∧ (H.induce (rightSet S)).Preconnected ∧
      ((leftSet S).Nonempty → (rightSet S).Nonempty → a ∈ leftSet S ∧ b ∈ rightSet S) := by
  rw [← (splitIso (joinAt G H a b) S).connected_iff]
  let K := splitGraph (joinAt G H a b) S
  have cross (x : leftSet S) (y : rightSet S) :
      K.Adj (.inl x) (.inr y) ↔ x.val = a ∧ y.val = b :=
    splitGraph_cross G H a b S x y
  constructor
  · intro h
    refine ⟨Set.nonempty_coe_sort.mp (Nonempty.map (splitIso (joinAt G H a b) S) h.nonempty),
      ?_, ?_, ?_⟩
    · rw [← splitGraph_inl G H a b S]
      exact left_preconnected h.preconnected fun x y x' y' hxy hxy' =>
        Subtype.ext ((cross x y).mp hxy |>.1.trans ((cross x' y').mp hxy' |>.1.symm))
    · rw [← splitGraph_inr G H a b S]
      exact right_preconnected h.preconnected fun x y x' y' hxy hxy' =>
        Subtype.ext ((cross x y).mp hxy |>.2.trans ((cross x' y').mp hxy' |>.2.symm))
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨u, v, huv⟩ := cross_exists (h (.inl ⟨x, hx⟩) (.inr ⟨y, hy⟩))
      obtain ⟨hu, hv⟩ := (cross u v).mp huv
      exact ⟨hu ▸ u.2, hv ▸ v.2⟩
  · rintro ⟨⟨x, hx⟩, hl, hr, h⟩
    apply connected_of_sides ⟨Equiv.subtypeSum ⟨x, hx⟩⟩
    · rwa [splitGraph_inl G H a b S]
    · rwa [splitGraph_inr G H a b S]
    · intro u v
      obtain ⟨ha, hb⟩ := h ⟨u, u.2⟩ ⟨v, v.2⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (cross _ _).mpr ⟨rfl, rfl⟩⟩

end Join
end D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
