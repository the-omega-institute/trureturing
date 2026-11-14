/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.claim; result=D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.result; claim=D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate.claim
   digest: Exact finite local certificates and ambient graph deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import D5.S3.Combinatorics.Graph.StarForming.FiniteMasks

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/SubcubicCertificate.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The local certificate domains and original embedding hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Subcubic

open Regular

set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 128

theorem minimal_of_deletion_failures {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hforms : Forms adjacency selection)
    (hfail : ∀ deleted, selection deleted → ∃ outside,
      ¬ (selection outside ∧ outside ≠ deleted) ∧
      ¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) :
    Minimal adjacency selection := by
  refine ⟨hforms, ?_⟩
  intro smaller hsubset hexists hsmaller
  obtain ⟨deleted, hselected, hmissing⟩ := hexists
  obtain ⟨outside, houtside, hfailure⟩ := hfail deleted hselected
  have hkeep : ∀ vertex, smaller vertex → selection vertex ∧ vertex ≠ deleted := by
    intro vertex hvertex
    refine ⟨hsubset vertex hvertex, ?_⟩
    intro heq
    exact hmissing (heq ▸ hvertex)
  have hnot : ¬ smaller outside := fun hvertex => houtside (hkeep outside hvertex)
  apply hfailure
  rcases hsmaller outside hnot with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨first, second, hkeep first hf, hkeep second hs, hne, ha, hb⟩
  · exact Or.inr ⟨center, leaf, hkeep center hc, hkeep leaf hl, ha, hb⟩

def neighbors (vertex : Fin 12) : List (Fin 12) :=
  match vertex.val with
  | 0 => [11]
  | 1 => [7,8,9]
  | 2 => [9,10,11]
  | 3 => [6,8,10]
  | 4 => [7,10]
  | 5 => [7,11]
  | 6 => [3]
  | 7 => [1,4,5]
  | 8 => [1,3]
  | 9 => [1,2]
  | 10 => [2,3,4]
  | _ => [0,2,5]

def Adj (first second : Fin 12) : Prop := second ∈ neighbors first

instance : DecidableRel Adj := fun a b =>
  inferInstanceAs (Decidable (b ∈ neighbors a))

def selected (vertex : Fin 12) : Prop := vertex ∈ ([0,1,4,5,6,7,8,9] : List (Fin 12))

instance (vertex : Fin 12) : Decidable (selected vertex) :=
  inferInstanceAs (Decidable (vertex ∈ ([0,1,4,5,6,7,8,9] : List (Fin 12))))

def failure (vertex : Fin 12) : Fin 12 :=
  match vertex.val with
  | 1 => 2
  | 4 => 10
  | 5 => 11
  | 7 => 10
  | 8 => 3
  | 9 => 2
  | _ => vertex

theorem adjacency_simple :
    (∀ vertex : Fin 12, ¬ Adj vertex vertex) ∧
    (∀ first second : Fin 12, Adj first second ↔ Adj second first) := by
  unfold Adj neighbors
  decide +kernel

theorem base_forms : Forms Adj selected := by
  unfold Forms TwoAt Adj selected neighbors
  decide +kernel

theorem base_deletion_failures : ∀ deleted : Fin 12, selected deleted →
    ¬ (selected (failure deleted) ∧ failure deleted ≠ deleted) ∧
    ¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ deleted) (failure deleted) := by
  unfold TwoAt Adj selected failure neighbors
  decide +kernel

theorem base_minimal : Minimal Adj selected := by
  apply minimal_of_deletion_failures Adj selected base_forms
  intro deleted hselected
  exact ⟨failure deleted, base_deletion_failures deleted hselected⟩

set_option synthInstance.maxSize 2048 in
set_option maxSynthPendingDepth 64 in
theorem forced_certificates :
    (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 1) →
      (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 1) outside ↔ outside = 2)) ∧
    (∀ outside : Fin 12, ¬ (selected outside ∧ outside ≠ 7) →
      (¬ TwoAt Adj (fun vertex => selected vertex ∧ vertex ≠ 7) outside ↔ outside = 10)) := by
  unfold TwoAt Adj selected neighbors
  decide +kernel

theorem selected_card :
    ((List.finRange 12).filter (fun vertex => decide (selected vertex))).length = 8 := by
  decide +kernel

def membership (mask : Fin 4096) (vertex : Fin 12) : Bool :=
  mask.val.testBit vertex.val

def card (mask : Fin 4096) : Nat :=
  ((List.finRange 12).filter (membership mask)).length

def Dissociation (mask : Fin 4096) : Prop :=
  ∀ vertex : Fin 12, membership mask vertex = true →
    ((neighbors vertex).filter (membership mask)).length ≤ 1

theorem exchange_collision :
    (∀ vertex : Fin 12, membership 1909 vertex = true ↔
      (selected vertex ∧ vertex ≠ 1 ∧ vertex ≠ 7) ∨ vertex = 2 ∨ vertex = 10) ∧
    card 1909 = 8 ∧ ¬ Dissociation 1909 := by
  unfold Dissociation card membership neighbors selected
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dissociation_port_cap : ∀ mask : Fin 4096, Dissociation mask →
    card mask ≤ 6 + if membership mask 0 || membership mask 6 then 1 else 0 := by
  unfold Dissociation card membership neighbors
  decide +kernel

def portWitness (first second : Bool) : Fin 4096 :=
  match first, second with
  | false, false => 828
  | false, true => 3442
  | true, false => 829
  | true, true => 375

theorem port_attainment (first second : Bool) :
    membership (portWitness first second) 0 = first ∧
    membership (portWitness first second) 6 = second ∧
    Dissociation (portWitness first second) ∧
    card (portWitness first second) = 6 + (if first || second then 1 else 0) ∧
    (∀ port ∈ ([0,6] : List (Fin 12)),
      membership (portWitness first second) port = true →
      ((neighbors port).filter (membership (portWitness first second))).length = 0) := by
  cases first <;> cases second <;>
    unfold portWitness Dissociation card membership neighbors <;> decide +kernel


open StarFormingDissociationRefutation

/-- The original twelve-vertex simple graph with ports zero and six. -/
def graph : SimpleGraph (Fin 12) where
  Adj := Adj
  symm := ⟨fun a b h => (adjacency_simple.2 a b).mp h⟩
  loopless := ⟨adjacency_simple.1⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (b ∈ neighbors a))

def selectedSet : Finset (Fin 12) := Finset.univ.filter selected

def maskSet (mask : Fin 4096) : Finset (Fin 12) :=
  Finset.univ.filter (fun v => membership mask v = true)

/-- Supplier mask dissociation is exactly the canonical selected-degree predicate. -/
theorem mask_dissociation_iff (mask : Fin 4096) :
    Dissociation mask ↔ IsKIndependent graph 2 (maskSet mask) := by
  have hc (v : Fin 12) : ((neighbors v).filter (membership mask)).length =
      ((maskSet mask).filter (graph.Adj v)).card := by
    have hn : (neighbors v).Nodup := by
      have hh : ∀ w : Fin 12, (neighbors w).Nodup := by decide +kernel
      exact hh v
    rw [← List.toFinset_card_of_nodup (hn.filter (membership mask))]
    congr 1
    ext w
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,maskSet,
      Finset.mem_univ,true_and]
    change (w ∈ neighbors v ∧ membership mask w = true) ↔
      (membership mask w = true ∧ w ∈ neighbors v)
    exact and_comm
  constructor
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc] at hh
    omega
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc]
    omega

/-- Every actual dissociation set is covered by the original port-state cap. -/
theorem beta_graph : beta graph 2 = 7 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask S
    have he : maskSet mask = S := by
      ext v
      simp [maskSet,membership,hm]
    have hi : Dissociation mask := (mask_dissociation_iff mask).mpr
      (he.symm ▸ (Finset.mem_filter.mp hS).2)
    have hc : card mask = S.card := by
      rw [card,FiniteMasks.list_count]
      exact congrArg Finset.card he
    have hb := dissociation_port_cap mask hi
    rw [hc] at hb
    split_ifs at hb <;> omega
  · let mask := portWitness true false
    have hi : IsKIndependent graph 2 (maskSet mask) :=
      (mask_dissociation_iff mask).mp (port_attainment true false).2.2.1
    have hc : (maskSet mask).card = 7 := by
      have hh := (port_attainment true false).2.2.2.1
      rw [card,FiniteMasks.list_count] at hh
      simpa [mask,maskSet] using hh
    rw [← hc]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

/-- The source's eight-set attains a canonical minimal selection. -/
theorem selectedSet_minimal : IsMinimalStarForming graph 2 selectedSet := by
  apply (regular_minimal_iff graph selectedSet).mp
  simpa [selectedSet,graph] using base_minimal

/-- The actual canonical selected set has eight vertices. -/
theorem selectedSet_card : selectedSet.card = 8 := by
  have hh := selected_card
  rw [FiniteMasks.list_count] at hh
  simpa [selectedSet] using hh

/-- This twelve-vertex bipartite subcubic graph has a genuine positive gap. -/
theorem graph_gap : beta graph 2 < SF graph 2 := by
  classical
  have hs : selectedSet.card ≤ SF graph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,selectedSet_minimal⟩)
  rw [selectedSet_card] at hs
  rw [beta_graph]
  omega

/-- The two graph-class hypotheses are checked on the original adjacency. -/
theorem graph_bipartite_subcubic : graph.Colorable 2 ∧
    ∀ v, (Finset.univ.filter (graph.Adj v)).card ≤ 3 := by
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 6 then (0 : Fin 2) else 1) ?_⟩
    change ∀ a b : Fin 12, Adj a b →
      (if a.val < 6 then (0 : Fin 2) else 1) ≠ (if b.val < 6 then 0 else 1)
    decide +kernel
  · change ∀ v : Fin 12, (Finset.univ.filter (Adj v)).card ≤ 3
    decide +kernel

/-- The proposed universal subcubic equality, and independent replacement by
both forced deletion certificates, are the two refuted assertions. -/
def claim : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Colorable 2 → (∀ v, (Finset.univ.filter (G.Adj v)).card ≤ 3) → beta G 2 = SF G 2) ∨
  (∃ x y : Fin 12,
    Regular.Failure Adj selected 1 x ∧ Regular.Failure Adj selected 7 y ∧
    IsKIndependent graph 2 ((selectedSet.erase 1).erase 7 ∪ {x,y}))

/-- The graph gap and the forced-certificate collision refute both assertions. -/
theorem result : ¬ claim := by
  rintro (h | ⟨x,y,hx,hy,hi⟩)
  · have he := h 12 graph graph_bipartite_subcubic.1 graph_bipartite_subcubic.2
    exact (Nat.ne_of_lt graph_gap) he
  · have hxe : x = 2 := (forced_certificates.1 x (by
      intro hs; exact hx.1 hs.1)).mp hx.2
    have hye : y = 10 := (forced_certificates.2 y (by
      intro hs; exact hy.1 hs.1)).mp hy.2
    subst x
    subst y
    have he : maskSet 1909 = (selectedSet.erase 1).erase 7 ∪ {2,10} := by
      ext v
      simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_union,Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton,
        selectedSet]
      have hh := exchange_collision.1 v
      tauto
    exact exchange_collision.2.2 ((mask_dissociation_iff 1909).mpr (he.symm ▸ hi))

end D5.S3.Combinatorics.Graph.StarForming.Subcubic
