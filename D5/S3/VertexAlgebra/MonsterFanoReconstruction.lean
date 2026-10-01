/- GID: D5/S3/VertexAlgebra/MonsterFanoReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterFanoReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reconstruct symmetric-difference complement closure from seven-point pair incidence. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterFanoReconstruction

open Finset
open scoped symmDiff

theorem block_intersection_le_one
    (blocks : Finset (Finset (Fin 7)))
    (hpair : ∀ i j : Fin 7, i ≠ j →
      ∃! A : Finset (Fin 7), A ∈ blocks ∧ i ∈ A ∧ j ∈ A)
    {A B : Finset (Fin 7)} (hA : A ∈ blocks) (hB : B ∈ blocks) (hne : A ≠ B) :
    (A ∩ B).card ≤ 1 := by
  classical
  by_contra hbound
  obtain ⟨left, hleft, right, hright, hdistinct⟩ :=
    one_lt_card.mp (Nat.lt_of_not_ge hbound)
  obtain ⟨line, _, unique⟩ := hpair left right hdistinct
  have hAline : A = line :=
    unique A ⟨hA, (mem_inter.mp hleft).1, (mem_inter.mp hright).1⟩
  have hBline : B = line :=
    unique B ⟨hB, (mem_inter.mp hleft).2, (mem_inter.mp hright).2⟩
  exact hne (hAline.trans hBline.symm)

theorem complement_symmDiff_mem
    (blocks : Finset (Finset (Fin 7)))
    (hcard : ∀ A ∈ blocks, A.card = 3)
    (hpair : ∀ i j : Fin 7, i ≠ j →
      ∃! A : Finset (Fin 7), A ∈ blocks ∧ i ∈ A ∧ j ∈ A)
    {A B : Finset (Fin 7)} (hA : A ∈ blocks) (hB : B ∈ blocks) (hne : A ≠ B) :
    (Finset.univ \ (A ∆ B)) ∈ blocks := by
  have pair_unique : ∀ {C D : Finset (Fin 7)}, C ∈ blocks → D ∈ blocks →
      ∀ {left right : Fin 7}, left ≠ right →
      left ∈ C → right ∈ C → left ∈ D → right ∈ D → C = D := by
    intro C D hC hD left right hlr hlC hrC hlD hrD
    obtain ⟨line, _, unique⟩ := hpair left right hlr
    exact (unique C ⟨hC, hlC, hrC⟩).trans (unique D ⟨hD, hlD, hrD⟩).symm
  have meet : ∀ {C D : Finset (Fin 7)}, C ∈ blocks → D ∈ blocks →
      ¬ Disjoint C D := by
    intro C D hC hD hdis
    have houtcard : (univ \ (C ∪ D)).card = 1 := by
      rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdis,
        hcard C hC, hcard D hD]
      decide
    obtain ⟨outside, hout⟩ := card_eq_one.mp houtcard
    have cross : ∀ {left right : Fin 7}, left ∈ C → right ∈ D →
        ∀ {line : Finset (Fin 7)}, line ∈ blocks → left ∈ line → right ∈ line →
        outside ∈ line := by
      intro left right hl hr line hline hll hrl
      have hlD : left ∉ D := disjoint_left.mp hdis hl
      have hrC : right ∉ C := fun hc => disjoint_left.mp hdis hc hr
      have hnC : line ≠ C := fun heq => hrC (heq ▸ hrl)
      have hnD : line ≠ D := fun heq => hlD (heq ▸ hll)
      by_contra houtline
      have hsub : line ⊆ {left, right} := by
        intro point hp
        by_cases hpC : point ∈ C
        · have heq : point = left :=
            card_le_one.mp (block_intersection_le_one blocks hpair hline hC hnC)
            point (mem_inter.mpr ⟨hp, hpC⟩) left (mem_inter.mpr ⟨hll, hl⟩)
          simp [heq]
        · by_cases hpD : point ∈ D
          · have heq : point = right :=
              card_le_one.mp (block_intersection_le_one blocks hpair hline hD hnD)
              point (mem_inter.mpr ⟨hp, hpD⟩) right (mem_inter.mpr ⟨hrl, hr⟩)
            simp [heq]
          · have hpout : point ∈ univ \ (C ∪ D) :=
              mem_sdiff.mpr ⟨mem_univ _, fun hu => (mem_union.mp hu).elim hpC hpD⟩
            rw [hout, mem_singleton] at hpout
            exact False.elim (houtline (hpout ▸ hp))
      have hbound := card_le_card hsub
      have htwo : ({left, right} : Finset (Fin 7)).card ≤ 2 := by
        exact (card_insert_le _ _).trans (by simp)
      have hthree := hcard line hline
      omega
    obtain ⟨left, hl⟩ := card_pos.mp (show 0 < C.card by rw [hcard C hC]; decide)
    obtain ⟨right, hr, other, ho, hro⟩ :=
      one_lt_card.mp (show 1 < D.card by rw [hcard D hD]; decide)
    have hlr : left ≠ right := fun heq => disjoint_left.mp hdis hl (heq ▸ hr)
    have hlo : left ≠ other := fun heq => disjoint_left.mp hdis hl (heq ▸ ho)
    obtain ⟨line, ⟨hline, hll, hrl⟩, _⟩ := hpair left right hlr
    obtain ⟨otherLine, ⟨hotherLine, hloLine, hooLine⟩, _⟩ := hpair left other hlo
    have houtline := cross hl hr hline hll hrl
    have houtother := cross hl ho hotherLine hloLine hooLine
    have hlout : left ≠ outside := by
      intro heq
      have : left ∈ univ \ (C ∪ D) := by rw [hout]; simp [heq]
      exact (mem_sdiff.mp this).2 (mem_union.mpr (Or.inl hl))
    have hlines := pair_unique hline hotherLine hlout hll houtline hloLine houtother
    have hoLine : other ∈ line := hlines.symm ▸ hooLine
    have hlineD := pair_unique hline hD hro hrl hoLine hr ho
    exact disjoint_left.mp hdis hl (hlineD ▸ hll)
  have inter_one : ∀ {C D : Finset (Fin 7)}, C ∈ blocks → D ∈ blocks →
      C ≠ D → (C ∩ D).card = 1 := by
    intro C D hC hD hCD
    have hpos : 0 < (C ∩ D).card := by
      apply card_pos.mpr
      exact nonempty_iff_ne_empty.mpr (fun heq =>
        meet hC hD (disjoint_iff_inter_eq_empty.mpr heq))
    have hle := block_intersection_le_one blocks hpair hC hD hCD
    omega
  have hAB := inter_one hA hB hne
  have houtcard : (univ \ (A ∪ B)).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_union, hcard A hA, hcard B hB, hAB]
    decide
  obtain ⟨left, right, hlr, hout⟩ := card_eq_two.mp houtcard
  have hlout : left ∈ univ \ (A ∪ B) := by rw [hout]; simp
  have hrout : right ∈ univ \ (A ∪ B) := by rw [hout]; simp
  have hlA : left ∉ A := fun hl => (mem_sdiff.mp hlout).2 (mem_union.mpr (Or.inl hl))
  have hlB : left ∉ B := fun hl => (mem_sdiff.mp hlout).2 (mem_union.mpr (Or.inr hl))
  obtain ⟨line, ⟨hline, hll, hrl⟩, _⟩ := hpair left right hlr
  have hnA : line ≠ A := fun heq => hlA (heq ▸ hll)
  have hnB : line ≠ B := fun heq => hlB (heq ▸ hll)
  have houtsub : univ \ (A ∪ B) ⊆ line := by
    rw [hout]
    intro point hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hll
    · exact hrl
  have hrest : (line \ (univ \ (A ∪ B))).card = 1 := by
    rw [card_sdiff_of_subset houtsub, hcard line hline, houtcard]
  obtain ⟨centerA, hcenterA⟩ :=
    card_pos.mp (show 0 < (line ∩ A).card by rw [inter_one hline hA hnA]; decide)
  obtain ⟨centerB, hcenterB⟩ :=
    card_pos.mp (show 0 < (line ∩ B).card by rw [inter_one hline hB hnB]; decide)
  have hcenterArest : centerA ∈ line \ (univ \ (A ∪ B)) := by
    refine mem_sdiff.mpr ⟨(mem_inter.mp hcenterA).1, ?_⟩
    exact fun hp => (mem_sdiff.mp hp).2 (mem_union.mpr (Or.inl (mem_inter.mp hcenterA).2))
  have hcenterBrest : centerB ∈ line \ (univ \ (A ∪ B)) := by
    refine mem_sdiff.mpr ⟨(mem_inter.mp hcenterB).1, ?_⟩
    exact fun hp => (mem_sdiff.mp hp).2 (mem_union.mpr (Or.inr (mem_inter.mp hcenterB).2))
  have hcenters : centerA = centerB :=
    card_le_one.mp (le_of_eq hrest) centerA hcenterArest centerB hcenterBrest
  have hcenterAB : centerA ∈ A ∩ B :=
    mem_inter.mpr ⟨(mem_inter.mp hcenterA).2, hcenters ▸ (mem_inter.mp hcenterB).2⟩
  have hintersub : A ∩ B ⊆ line := by
    intro point hp
    have heq := card_le_one.mp (le_of_eq hAB) point hp centerA hcenterAB
    exact heq ▸ (mem_inter.mp hcenterA).1
  have hsplit : univ \ (A ∆ B) = (univ \ (A ∪ B)) ∪ (A ∩ B) := by
    ext point
    simp only [mem_sdiff, mem_univ, true_and, mem_symmDiff, mem_union, mem_inter]
    tauto
  have hdis : Disjoint (univ \ (A ∪ B)) (A ∩ B) := by
    apply disjoint_left.mpr
    intro point hp hi
    exact (mem_sdiff.mp hp).2 (mem_union.mpr (Or.inl (mem_inter.mp hi).1))
  have htargetcard : (univ \ (A ∆ B)).card = 3 := by
    rw [hsplit, card_union_of_disjoint hdis, houtcard, hAB]
  have htargetsub : univ \ (A ∆ B) ⊆ line := by
    rw [hsplit]
    exact union_subset houtsub hintersub
  have heq : univ \ (A ∆ B) = line :=
    eq_of_subset_of_card_le htargetsub (by rw [htargetcard, hcard line hline])
  exact heq ▸ hline

#print axioms block_intersection_le_one
#print axioms complement_symmDiff_mem

end D5.S3.VertexAlgebra.MonsterFanoReconstruction
