/- GID: D5/S3/Combinatorics/Graph/StarForming/Amplification
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Amplification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact H0 port composition with original local deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
import D5.S3.Combinatorics.Graph.StarForming.Foundations.LocalFormation
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases

/-!
Adapted from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/Amplification.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces and reuse of existing H₀ data.
The original proof bodies and all arbitrary-interface/empty-index domains are retained.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Amplification

/-- Reuse the canonical H₀ data; no second counterexample is constructed. -/
abbrev baseEdges := D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation.edges
abbrev base := D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation.counterGraph
abbrev selected := D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation.selected

def failure (vertex : Fin 10) : Fin 10 :=
  if vertex = 0 then 9 else if vertex = 1 then 8 else
  if vertex = 5 then 4 else if vertex = 6 then 3 else vertex

def Unported (vertex : Fin 10) : Prop := vertex ≠ 0 ∧ vertex ≠ 5

def family {I : Type*} (interfaces : I → I → Prop) : SimpleGraph (I × Fin 10) where
  Adj first second :=
    (first.1 = second.1 ∧ base.Adj first.2 second.2) ∨
    (first.2 = 5 ∧ second.2 = 0 ∧ interfaces first.1 second.1) ∨
    (first.2 = 0 ∧ second.2 = 5 ∧ interfaces second.1 first.1)
  symm := ⟨by
    intro first second hadj
    rcases hadj with ⟨heq, hb⟩ | ⟨hf, hs, hi⟩ | ⟨hf, hs, hi⟩
    · exact Or.inl ⟨heq.symm, base.adj_symm hb⟩
    · exact Or.inr (Or.inr ⟨hs, hf, hi⟩)
    · exact Or.inr (Or.inl ⟨hs, hf, hi⟩)⟩
  loopless := ⟨by
    intro vertex hadj
    rcases hadj with ⟨_, hb⟩ | ⟨hf, hs, _⟩ | ⟨hf, hs, _⟩
    · exact base.irrefl hb
    · have : (5 : Fin 10) = 0 := hf.symm.trans hs
      exact (by decide : (5 : Fin 10) ≠ 0) this
    · have : (0 : Fin 10) = 5 := hf.symm.trans hs
      exact (by decide : (0 : Fin 10) ≠ 5) this⟩

def chosen {I : Type*} : Set (I × Fin 10) := {vertex | vertex.2 ∈ selected}

theorem adj_unported {I : Type*} (interfaces : I → I → Prop)
    (first second : I × Fin 10) (hu : Unported first.2) :
    (family interfaces).Adj first second ↔
      first.1 = second.1 ∧ base.Adj first.2 second.2 := by
  change (_ ∨ _ ∨ _) ↔ _
  simp only [hu.1, hu.2, false_and, or_false]

theorem failure_unported (vertex : Fin 10) (hs : vertex ∈ selected) :
    Unported (failure vertex) := by
  fin_cases vertex <;> simp [selected, failure, Unported] at hs ⊢

theorem base_failure (vertex : Fin 10) (hs : vertex ∈ selected) :
    failure vertex ∉ selected.erase vertex ∧
    (∀ first ∈ selected.erase vertex, ∀ second ∈ selected.erase vertex,
      base.Adj (failure vertex) first → base.Adj (failure vertex) second →
      first = second) ∧
    (∀ center ∈ selected.erase vertex, base.Adj (failure vertex) center →
      Unported center ∧ ∀ leaf ∈ selected.erase vertex, ¬ base.Adj center leaf) := by
  fin_cases vertex <;> simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hs
  all_goals try contradiction
  all_goals simp only [Unported]
  all_goals decide +kernel

theorem family_forms {I : Type*} (interfaces : I → I → Prop) :
    Forms (family interfaces) (chosen : Set (I × Fin 10)) := by
  rintro ⟨block, vertex⟩ hout
  have base_forms : ∀ vertex : Fin 10, vertex ∉ selected →
      ∃ first ∈ selected, ∃ second ∈ selected,
        first ≠ second ∧ base.Adj vertex first ∧ base.Adj vertex second := by
    intro vertex
    fin_cases vertex <;> decide +kernel
  obtain ⟨first, hf, second, hs, hfs, hadjf, hadjs⟩ := base_forms vertex hout
  exact Or.inl ⟨(block, first), hf, (block, second), hs,
    (fun heq => hfs (congrArg Prod.snd heq)),
    Or.inl ⟨rfl, hadjf⟩, Or.inl ⟨rfl, hadjs⟩⟩

theorem family_deletion_failure {I : Type*} (interfaces : I → I → Prop)
    (block : I) (vertex : Fin 10) (hs : vertex ∈ selected) :
    (block, failure vertex) ∉ (chosen : Set (I × Fin 10)) \ {(block, vertex)} ∧
    ¬ TwoAt (family interfaces) (chosen \ {(block, vertex)}) (block, failure vertex) := by
  obtain ⟨hout, hunique, hcenters⟩ := base_failure vertex hs
  have hlocal : ∀ neighbor ∈ (chosen : Set (I × Fin 10)) \ {(block, vertex)},
      (family interfaces).Adj (block, failure vertex) neighbor →
      neighbor.1 = block ∧ neighbor.2 ∈ selected.erase vertex ∧
        base.Adj (failure vertex) neighbor.2 := by
    rintro ⟨other, label⟩ ⟨hselected, hne⟩ hadj
    obtain ⟨heq, hb⟩ := (adj_unported interfaces _ _ (failure_unported vertex hs)).mp hadj
    have hlabel : label ≠ vertex := by
      intro hlabel
      apply hne
      simp only [Set.mem_singleton_iff]
      exact Prod.ext heq.symm hlabel
    exact ⟨heq.symm, Finset.mem_erase.mpr ⟨hlabel, hselected⟩, hb⟩
  constructor
  · rintro ⟨hselected, hne⟩
    apply hout
    apply Finset.mem_erase.mpr
    refine ⟨?_, hselected⟩
    intro heq
    apply hne
    simp only [Set.mem_singleton_iff]
    exact Prod.ext rfl heq
  · rintro (⟨first, hf, second, hsecond, hne, hadjf, hadjs⟩ |
      ⟨center, hc, hadjc, leaf, hl, hadjl⟩)
    · obtain ⟨hblockf, hself, hbasef⟩ := hlocal first hf hadjf
      obtain ⟨hblocks, hsels, hbases⟩ := hlocal second hsecond hadjs
      exact hne (Prod.ext (hblockf.trans hblocks.symm)
        (hunique first.2 hself second.2 hsels hbasef hbases))
    · obtain ⟨hblock, hsel, hb⟩ := hlocal center hc hadjc
      obtain ⟨hu, hno⟩ := hcenters center.2 hsel hb
      obtain ⟨heq, hbaseleaf⟩ := (adj_unported interfaces center leaf hu).mp hadjl
      have hleaf : leaf.2 ∈ selected.erase vertex := by
        apply Finset.mem_erase.mpr
        refine ⟨?_, hl.1⟩
        intro heqlabel
        apply hl.2
        simp only [Set.mem_singleton_iff]
        exact Prod.ext (heq.symm.trans hblock) heqlabel
      exact hno leaf.2 hleaf hbaseleaf

theorem family_minimal {I : Type*} (interfaces : I → I → Prop) :
    Minimal (family interfaces) (chosen : Set (I × Fin 10)) := by
  apply minimal_of_deletion_failures _ _ (family_forms interfaces)
  rintro ⟨block, vertex⟩ hs
  exact ⟨(block, failure vertex), family_deletion_failure interfaces block vertex hs⟩

theorem chosen_card {I : Type*} [Fintype I] [DecidableEq I] :
    ((Finset.univ : Finset I).product selected).card = 6 * Fintype.card I := by
  rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ]
  have hs : selected.card = 6 := by decide +kernel
  rw [hs, Nat.mul_comm]

theorem family_bipartite {I : Type*} (interfaces : I → I → Prop) :
    (family interfaces).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun vertex => if vertex.2.val < 5 then 0 else 1) ?_⟩
  intro first second hadj
  rcases hadj with ⟨_, hb⟩ | ⟨hf, hs, _⟩ | ⟨hf, hs, _⟩
  · have hbase : ∀ first second : Fin 10, base.Adj first second →
        (if first.val < 5 then (0 : Fin 2) else 1) ≠
          (if second.val < 5 then 0 else 1) := by
      intro first second
      fin_cases first <;> fin_cases second <;> decide +kernel
    exact hbase _ _ hb
  · simp [hf, hs]
  · simp [hf, hs]

def cycleGraph (copies : ℕ) : SimpleGraph (Fin copies × Fin 10) :=
  family (fun first second => (first.val + 1) % copies = second.val)

def cycleSelected (copies : ℕ) : Finset (Fin copies × Fin 10) :=
  Finset.univ.product selected

theorem cycle_minimal_card (copies : ℕ) :
    Minimal (cycleGraph copies) (↑(cycleSelected copies) : Set (Fin copies × Fin 10)) ∧
    (cycleSelected copies).card = 6 * copies ∧
    (cycleGraph copies).Colorable 2 := by
  have hchosen : (↑(cycleSelected copies) : Set (Fin copies × Fin 10)) = chosen := by
    ext vertex
    simp [cycleSelected, Finset.product_eq_sprod, chosen]
  refine ⟨?_, ?_, family_bipartite _⟩
  · rw [hchosen]
    exact family_minimal _
  · simpa only [cycleSelected, Fintype.card_fin] using
      (chosen_card (I := Fin copies))

end D5.S3.Combinatorics.Graph.StarForming.Amplification
