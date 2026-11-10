/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicExact
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.ambient_core_cap; instance=D5/S3/Combinatorics/Graph/StarForming/SubcubicExact.dense_core_certificate
   digest: Exact finite local certificates and ambient graph deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicCertificate

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/SubcubicExact.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The local certificate domains and original embedding hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Subcubic

open Regular

theorem supported_deletion {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted : Vertex)
    (hforms : Forms adjacency selection)
    (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted)
    (hadjacent : ∀ outside, ¬ selection outside → adjacency outside deleted →
      TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside)
    (hreplacement : ∀ center, selection center → adjacency center deleted →
      ∃ leaf, (selection leaf ∧ leaf ≠ deleted) ∧ adjacency center leaf) :
    Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) := by
  classical
  intro outside houtside
  by_cases hequal : outside = deleted
  · exact hequal ▸ hnew
  have hold : ¬ selection outside := fun hselected => houtside ⟨hselected, hequal⟩
  by_cases hadj : adjacency outside deleted
  · exact hadjacent outside hold hadj
  rcases hforms outside hold with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · have hfirst : first ≠ deleted := fun heq => hadj (heq ▸ ha)
    have hsecond : second ≠ deleted := fun heq => hadj (heq ▸ hb)
    exact Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hne, ha, hb⟩
  · have hcenter : center ≠ deleted := fun heq => hadj (heq ▸ ha)
    by_cases hleaf : leaf = deleted
    · obtain ⟨replacement, hr, hedge⟩ := hreplacement center hc (hleaf ▸ hb)
      exact Or.inr ⟨center, replacement, ⟨hc, hcenter⟩, hr, ha, hedge⟩
    · exact Or.inr ⟨center, leaf, ⟨hc, hcenter⟩, ⟨hl, hleaf⟩, ha, hb⟩

def coreLabel (vertex : Fin 10) : Fin 12 :=
  ⟨if vertex.val < 5 then vertex.val + 1 else vertex.val + 2, by split <;> omega⟩

def CoreAdj (first second : Fin 10) : Prop := Adj (coreLabel first) (coreLabel second)

def attachment (vertex : Fin 10) : Prop := coreLabel vertex = 3 ∨ coreLabel vertex = 11

def coreSelected (mask : Fin 1024) (vertex : Fin 10) : Prop := mask.val.testBit vertex.val = true

def coreCard (mask : Fin 1024) : Nat :=
  ((List.finRange 10).filter (fun vertex => mask.val.testBit vertex.val)).length

def SafeCore (mask : Fin 1024) (deleted : Fin 10) : Prop :=
  coreSelected mask deleted ∧ ¬ attachment deleted ∧
  TwoAt CoreAdj (fun vertex => coreSelected mask vertex ∧ vertex ≠ deleted) deleted ∧
  (∀ center, coreSelected mask center → CoreAdj center deleted →
    ∃ leaf, (coreSelected mask leaf ∧ leaf ≠ deleted) ∧ CoreAdj center leaf) ∧
  (∀ outside, ¬ coreSelected mask outside → CoreAdj outside deleted →
    TwoAt CoreAdj (fun vertex => coreSelected mask vertex ∧ vertex ≠ deleted) outside)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
set_option maxSynthPendingDepth 128 in
theorem dense_core_certificate : ∀ mask : Fin 1024, 7 ≤ coreCard mask →
    ∃ deleted, SafeCore mask deleted := by
  unfold SafeCore TwoAt CoreAdj Adj neighbors attachment coreLabel coreSelected coreCard
  decide +kernel

theorem lift_core_star {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (embedding : Fin 10 → Vertex) (mask : Fin 1024)
    (hinjective : ∀ first second, embedding first = embedding second → first = second)
    (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second)
    (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex)
    (deleted outside : Fin 10)
    (hstar : TwoAt CoreAdj (fun vertex => coreSelected mask vertex ∧ vertex ≠ deleted) outside) :
    TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside) := by
  have hkeep : ∀ vertex, coreSelected mask vertex ∧ vertex ≠ deleted →
      selection (embedding vertex) ∧ embedding vertex ≠ embedding deleted := by
    intro vertex hvertex
    exact ⟨(hselection vertex).mpr hvertex.1, fun heq => hvertex.2 (hinjective _ _ heq)⟩
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ | ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨embedding first, embedding second, hkeep first hf, hkeep second hs,
      fun heq => hne (hinjective _ _ heq), (hedges _ _).mpr ha, (hedges _ _).mpr hb⟩
  · exact Or.inr ⟨embedding center, embedding leaf, hkeep center hc, hkeep leaf hl,
      (hedges _ _).mpr ha, (hedges _ _).mpr hb⟩

theorem ambient_core_cap {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (embedding : Fin 10 → Vertex) (mask : Fin 1024)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hinjective : ∀ first second, embedding first = embedding second → first = second)
    (hedges : ∀ first second, adjacency (embedding first) (embedding second) ↔ CoreAdj first second)
    (hselection : ∀ vertex, selection (embedding vertex) ↔ coreSelected mask vertex)
    (hclosed : ∀ vertex, ¬ attachment vertex → ∀ outside, adjacency (embedding vertex) outside →
      ∃ other, outside = embedding other)
    (hminimal : Minimal adjacency selection) : coreCard mask ≤ 6 := by
  classical
  by_cases hcap : coreCard mask ≤ 6
  · exact hcap
  apply False.elim
  obtain ⟨deleted, hselected, hnonport, hnew, hreplace, hadjacent⟩ :=
    dense_core_certificate mask (by omega)
  have hglobal : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) := by
    apply supported_deletion adjacency selection (embedding deleted) hminimal.1
    · exact lift_core_star adjacency selection embedding mask hinjective hedges hselection deleted deleted hnew
    · intro outside houtside hedge
      obtain ⟨localOutside, rfl⟩ := hclosed deleted hnonport outside (hsymmetric _ _ hedge)
      apply lift_core_star adjacency selection embedding mask hinjective hedges hselection deleted localOutside
      apply hadjacent localOutside
      · exact fun hlocal => houtside ((hselection _).mpr hlocal)
      · exact (hedges _ _).mp hedge
    · intro center hc hedge
      obtain ⟨localCenter, rfl⟩ := hclosed deleted hnonport center (hsymmetric _ _ hedge)
      obtain ⟨leaf, hl, hedgeLeaf⟩ := hreplace localCenter ((hselection _).mp hc) ((hedges _ _).mp hedge)
      exact ⟨embedding leaf, ⟨(hselection _).mpr hl.1,
        fun heq => hl.2 (hinjective _ _ heq)⟩, (hedges _ _).mpr hedgeLeaf⟩
  exact hminimal.2 _ (fun _ hvertex => hvertex.1)
    ⟨embedding deleted, (hselection _).mpr hselected, fun hvertex => hvertex.2 rfl⟩ hglobal


open StarFormingDissociationRefutation

/-- The core embedding covers every nonport label exactly once. -/
theorem core_label_properties :
    Function.Injective coreLabel ∧
    (∀ w : Fin 12, w = 0 ∨ w = 6 ∨ ∃ v : Fin 10, coreLabel v = w) ∧
    (∀ v : Fin 10, ¬ attachment v → ∀ w : Fin 12, Adj (coreLabel v) w →
      ∃ other, w = coreLabel other) := by
  unfold Function.Injective attachment coreLabel Adj neighbors
  decide +kernel

/-- The exact ambient core cap now bounds every actual finite selection. -/
theorem minimal_card_bound (S : Finset (Fin 12))
    (hS : IsMinimalStarForming graph 2 S) : S.card ≤ 8 := by
  classical
  let C : Finset (Fin 10) := Finset.univ.filter (fun v => coreLabel v ∈ S)
  obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask C
  have hselection (v : Fin 10) : (coreLabel v ∈ S) ↔ coreSelected mask v := by
    simpa only [coreSelected,C,Finset.mem_filter,Finset.mem_univ,true_and] using (hm v).symm
  have hb := ambient_core_cap graph.Adj (· ∈ S) coreLabel mask
    (fun _ _ h => graph.adj_symm h) core_label_properties.1
    (fun _ _ => Iff.rfl) hselection core_label_properties.2.2
    ((regular_minimal_iff graph S).mpr hS)
  have hc : coreCard mask = C.card := by
    rw [coreCard,FiniteMasks.list_count]
    congr 1
    ext v
    simp [hm]
  rw [hc] at hb
  have hsub : S ⊆ C.image coreLabel ∪ {0,6} := by
    intro w hw
    rcases core_label_properties.2.1 w with rfl | rfl | ⟨v,rfl⟩
    · simp
    · simp
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,by simp [C,hw],rfl⟩)
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hi := Finset.card_image_le (s := C) (f := coreLabel)
  have hp : ({0,6} : Finset (Fin 12)).card = 2 := by decide +kernel
  omega

/-- The original eight-set attains the full canonical upper maximum. -/
theorem sf_graph : SF graph 2 = 8 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    exact minimal_card_bound S (Finset.mem_filter.mp hS).2
  · have hs : selectedSet.card ≤ SF graph 2 :=
      Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,selectedSet_minimal⟩)
    simpa only [selectedSet_card] using hs

end D5.S3.Combinatorics.Graph.StarForming.Subcubic
