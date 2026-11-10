/- GID: D5/S3/Combinatorics/Graph/StarForming/Composition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Composition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact H0 port composition with original local deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.Amplification
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Adapted from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/Composition.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces and reuse of existing H₀ data.
The original proof bodies and all arbitrary-interface/empty-index domains are retained.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Composition

open Amplification

theorem forms_erase_of_local_replacement {V : Type*} (G : SimpleGraph V)
    (S tile : Set V) (deleted : V) (hdeleted : deleted ∈ tile)
    (hforms : Forms G S)
    (hinside : ∀ x ∈ tile, x ∉ S \ {deleted} → TwoAt G (S \ {deleted}) x)
    (hnooutside : ∀ x, x ∉ tile → ¬ G.Adj x deleted)
    (hreplace : ∀ center ∈ S, G.Adj center deleted →
      ∀ x, x ∉ tile → G.Adj x center →
        ∃ leaf ∈ S \ {deleted}, G.Adj center leaf) :
    Forms G (S \ {deleted}) := by
  intro x hx
  by_cases hxtile : x ∈ tile
  · exact hinside x hxtile hx
  · have hxs : x ∉ S := by
      intro hxs
      apply hx
      refine ⟨hxs, ?_⟩
      intro heq
      exact hxtile ((Set.mem_singleton_iff.mp heq).symm ▸ hdeleted)
    have hkeep {neighbor : V} (hs : neighbor ∈ S) (hadj : G.Adj x neighbor) :
        neighbor ∈ S \ {deleted} := by
      refine ⟨hs, ?_⟩
      intro heq
      exact hnooutside x hxtile ((Set.mem_singleton_iff.mp heq) ▸ hadj)
    rcases hforms x hxs with ⟨first, hf, second, hs, hne, hadjf, hadjs⟩ |
      ⟨center, hc, hadjc, leaf, hl, hadjl⟩
    · exact Or.inl ⟨first, hkeep hf hadjf, second, hkeep hs hadjs, hne, hadjf, hadjs⟩
    · have hcenter := hkeep hc hadjc
      by_cases heq : leaf = deleted
      · obtain ⟨replacement, hr, hadjr⟩ := hreplace center hc (heq ▸ hadjl) x hxtile hadjc
        exact Or.inr ⟨center, hcenter, hadjc, replacement, hr, hadjr⟩
      · exact Or.inr ⟨center, hcenter, hadjc, leaf,
          ⟨hl, by simpa only [Set.mem_singleton_iff] using heq⟩, hadjl⟩

def HasLocalDeletion (selection : Finset (Fin 10)) : Prop :=
  ∃ deleted ∈ selection, Unported deleted ∧
    Forms base (↑(selection.erase deleted) : Set (Fin 10)) ∧
    ∀ port, (port = 0 ∨ port = 5) → port ∈ selection → base.Adj port deleted →
      ∃ leaf ∈ selection.erase deleted, base.Adj port leaf

def HasIsolatedNonport (selection : Finset (Fin 10)) : Prop :=
  ∃ vertex : Fin 10, Unported vertex ∧ vertex ∉ selection ∧
    ∀ neighbor ∈ selection, ¬ base.Adj vertex neighbor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
set_option maxSynthPendingDepth 64 in
theorem local_dense_certificate (selection : Finset (Fin 10)) (hcard : 7 ≤ selection.card) :
    HasIsolatedNonport selection ∨ HasLocalDeletion selection := by
  have certificate : ∀ selection ∈ ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).powerset,
      7 ≤ selection.card → HasIsolatedNonport selection ∨ HasLocalDeletion selection := by
    simp only [← Finset.insert_empty, Finset.powerset_insert,
      Finset.powerset_empty, Finset.forall_mem_union, Finset.forall_mem_image,
      Finset.forall_mem_insert, Finset.forall_mem_empty_iff, and_true]
    repeat' apply And.intro
    all_goals unfold HasIsolatedNonport HasLocalDeletion Unported Forms TwoAt
    all_goals decide +kernel
  apply certificate selection _ hcard
  have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by decide +kernel
  rw [← huniv]
  exact Finset.mem_powerset.mpr (Finset.subset_univ selection)

noncomputable def blockSelection {I : Type*} (S : Set (I × Fin 10))
    (block : I) : Finset (Fin 10) := by
  classical
  exact Finset.univ.filter (fun label => (block, label) ∈ S)

theorem family_block_upper {I : Type*} (interfaces : I → I → Prop)
    (S : Set (I × Fin 10)) (hminimal : Minimal (family interfaces) S)
    (block : I) : (blockSelection S block).card ≤ 6 := by
  classical
  let selection := blockSelection S block
  have hmem (label : Fin 10) : label ∈ selection ↔ (block, label) ∈ S := by
    simp [selection, blockSelection]
  by_contra hlarge
  have hcard : 7 ≤ selection.card := by
    change 7 ≤ (blockSelection S block).card
    omega
  rcases local_dense_certificate selection hcard with hisolated | hdelete
  · obtain ⟨vertex, hu, hout, hno⟩ := hisolated
    have houtside : (block, vertex) ∉ S := fun hs => hout ((hmem vertex).mpr hs)
    have hnoselected : ∀ neighbor ∈ S,
        ¬ (family interfaces).Adj (block, vertex) neighbor := by
      rintro ⟨other, label⟩ hs hadj
      obtain ⟨heq, hb⟩ := (adj_unported interfaces _ _ hu).mp hadj
      change block = other at heq
      apply hno label
      · apply (hmem label).mpr
        exact heq.symm ▸ hs
      · exact hb
    rcases hminimal.1 _ houtside with ⟨first, hf, _, _, _, hadj, _⟩ |
      ⟨center, hc, hadj, _⟩
    · exact hnoselected first hf hadj
    · exact hnoselected center hc hadj
  · obtain ⟨deleted, hd, hu, hlocal, hports⟩ := hdelete
    let removed : I × Fin 10 := (block, deleted)
    have hremoved : removed ∈ S := (hmem deleted).mp hd
    have lift_mem (label : Fin 10) (hl : label ∈ selection.erase deleted) :
        (block, label) ∈ S \ {removed} := by
      obtain ⟨hne, hselected⟩ := Finset.mem_erase.mp hl
      refine ⟨(hmem label).mp hselected, ?_⟩
      intro heq
      exact hne (congrArg Prod.snd (Set.mem_singleton_iff.mp heq))
    have hlift : ∀ label, TwoAt base (↑(selection.erase deleted) : Set (Fin 10)) label →
        TwoAt (family interfaces) (S \ {removed}) (block, label) := by
      intro label htwo
      rcases htwo with ⟨first, hf, second, hs, hne, hadjf, hadjs⟩ |
        ⟨center, hc, hadj, leaf, hl, hadjl⟩
      · exact Or.inl ⟨(block, first), lift_mem first hf, (block, second), lift_mem second hs,
          (fun heq => hne (congrArg Prod.snd heq)),
          Or.inl ⟨rfl, hadjf⟩, Or.inl ⟨rfl, hadjs⟩⟩
      · exact Or.inr ⟨(block, center), lift_mem center hc, Or.inl ⟨rfl, hadj⟩,
          (block, leaf), lift_mem leaf hl, Or.inl ⟨rfl, hadjl⟩⟩
    have hnew : Forms (family interfaces) (S \ {removed}) := by
      apply forms_erase_of_local_replacement (family interfaces) S
        {vertex | vertex.1 = block} removed rfl hminimal.1
      · rintro ⟨other, label⟩ heq hout
        change other = block at heq
        subst other
        apply hlift
        apply hlocal label
        exact fun hin => hout (lift_mem label hin)
      · intro x hx hadj
        have hback := (adj_unported interfaces removed x hu).mp
          ((family interfaces).adj_symm hadj)
        exact hx hback.1.symm
      · rintro ⟨other, port⟩ hc hadj x hx hadjx
        obtain ⟨heq, hb⟩ := (adj_unported interfaces removed (other, port) hu).mp
          ((family interfaces).adj_symm hadj)
        change block = other at heq
        have hport : port = 0 ∨ port = 5 := by
          by_contra hnot
          have hup : Unported port := ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
          have hsame := (adj_unported interfaces (other, port) x hup).mp
            ((family interfaces).adj_symm hadjx)
          exact hx (hsame.1.symm.trans heq.symm)
        obtain ⟨leaf, hl, hbase⟩ := hports port hport
          ((hmem port).mpr (heq.symm ▸ hc)) (base.adj_symm hb)
        refine ⟨(block, leaf), lift_mem leaf hl, Or.inl ⟨heq.symm, hbase⟩⟩
    apply hminimal.2 (S \ {removed}) _ hnew
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
    intro heq
    have hnot : removed ∉ S \ {removed} := by simp
    exact hnot (heq.symm ▸ hremoved)

end D5.S3.Combinatorics.Graph.StarForming.Composition
