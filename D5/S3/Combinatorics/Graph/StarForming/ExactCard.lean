/- GID: D5/S3/Combinatorics/Graph/StarForming/ExactCard
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ExactCard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact H0 port composition with original local deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.Composition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Adapted from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/ExactCard.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces and reuse of existing H₀ data.
The original proof bodies and all arbitrary-interface/empty-index domains are retained.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Composition

open Amplification

theorem card_eq_sum_blocks {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset (I × Fin 10)) :
    S.card = ∑ block : I, (blockSelection (↑S : Set (I × Fin 10)) block).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := Finset.univ) (by intro vertex hv; exact Finset.mem_univ vertex.1)]
  apply Finset.sum_congr rfl
  intro block hblock
  apply Finset.card_bij (fun vertex _ => vertex.2)
  · intro vertex hv
    obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hv
    simp only [blockSelection, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe]
    exact heq ▸ hs
  · intro first hf second hs heq
    exact Prod.ext ((Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hs).2.symm) heq
  · intro label hl
    have hselected : (block, label) ∈ S := by
      simpa only [blockSelection, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_coe] using hl
    exact ⟨(block, label), Finset.mem_filter.mpr ⟨hselected, rfl⟩, rfl⟩

theorem family_card_upper {I : Type*} [Fintype I] [DecidableEq I]
    (interfaces : I → I → Prop) (S : Finset (I × Fin 10))
    (hminimal : Minimal (family interfaces) (↑S : Set (I × Fin 10))) :
    S.card ≤ 6 * Fintype.card I := by
  classical
  rw [card_eq_sum_blocks]
  calc
    ∑ block : I, (blockSelection (↑S : Set (I × Fin 10)) block).card ≤ ∑ _ : I, 6 :=
      Finset.sum_le_sum (fun block _ => family_block_upper interfaces _ hminimal block)
    _ = 6 * Fintype.card I := by simp [Nat.mul_comm]

theorem exact_composition_card {I : Type*} [Fintype I] [DecidableEq I]
    (interfaces : I → I → Prop) :
    (∀ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) →
      S.card ≤ 6 * Fintype.card I) ∧
    (∃ S : Finset (I × Fin 10), Minimal (family interfaces) (↑S : Set (I × Fin 10)) ∧
      S.card = 6 * Fintype.card I) := by
  classical
  refine ⟨family_card_upper interfaces, ?_⟩
  refine ⟨Finset.univ.product selected, ?_, chosen_card⟩
  have hchosen : (↑((Finset.univ : Finset I).product selected) : Set (I × Fin 10)) = chosen := by
    ext vertex
    simp [Finset.product_eq_sprod, chosen]
  rw [hchosen]
  exact family_minimal interfaces

end D5.S3.Combinatorics.Graph.StarForming.Composition
