/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGain
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Auxiliary lattice lemmas for the capped-gain Bellman lift. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGain.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Causal

/-!
# Auxiliary lattice lemmas for the capped-gain Bellman lift

These declarations formalize two ingredients of the new research proof.
They do NOT yet constitute an end-to-end Lean formalization of rank eight.
-/

namespace Erdos7

variable {ι : Type*} [DecidableEq ι]

/-- An increment across two fixed nested label sets is increasing in the
eligible set. This is the monotonicity required for the depth gain G. -/
theorem Supermodular.nested_increment_increasing
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    Increasing (fun S ↦ F (S ∩ J) - F (S ∩ I)) := by
  intro A B hAB
  have hinter : (A ∩ J) ∩ (B ∩ I) = A ∩ I := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨ha, _⟩, _, hi⟩
      exact ⟨ha, hi⟩
    · rintro ⟨ha, hi⟩
      exact ⟨⟨ha, hIJ hi⟩, hAB ha, hi⟩
  have hunion : (A ∩ J) ∪ (B ∩ I) ⊆ B ∩ J := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_inter.mpr ⟨hAB (Finset.mem_inter.mp h).1,
        (Finset.mem_inter.mp h).2⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
        hIJ (Finset.mem_inter.mp h).2⟩
  have hs := hF (A ∩ J) (B ∩ I)
  rw [hinter] at hs
  have hm := hInc hunion
  linarith

/-- The maximum of two supermodular functions is supermodular when their
difference is increasing. The difference hypothesis is essential. -/
theorem supermodular_max_of_increasing_difference
    {F G : Finset ι → ℚ} (hF : Supermodular F) (hG : Supermodular G)
    (hDiff : Increasing (fun S ↦ G S - F S)) :
    Supermodular (fun S ↦ max (F S) (G S)) := by
  intro A B
  change max (F A) (G A) + max (F B) (G B) ≤
    max (F (A ∩ B)) (G (A ∩ B)) + max (F (A ∪ B)) (G (A ∪ B))
  rcases le_total (F A) (G A) with ha | ha
  · rcases le_total (F B) (G B) with hb | hb
    · rw [max_eq_right ha, max_eq_right hb]
      exact (hG A B).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
    · rw [max_eq_right ha, max_eq_left hb]
      have hD := hDiff (Finset.inter_subset_right : A ∩ B ⊆ B)
      have hS := hG A B
      have hM : G A + F B ≤ F (A ∩ B) + G (A ∪ B) := by linarith
      exact hM.trans (add_le_add (le_max_left _ _) (le_max_right _ _))
  · rcases le_total (F B) (G B) with hb | hb
    · rw [max_eq_left ha, max_eq_right hb]
      have hD := hDiff (Finset.inter_subset_left : A ∩ B ⊆ A)
      have hS := hG A B
      have hM : F A + G B ≤ F (A ∩ B) + G (A ∪ B) := by linarith
      exact hM.trans (add_le_add (le_max_left _ _) (le_max_right _ _))
    · rw [max_eq_left ha, max_eq_left hb]
      exact (hF A B).trans (add_le_add (le_max_left _ _) (le_max_left _ _))

end Erdos7

#print axioms Erdos7.Supermodular.nested_increment_increasing
#print axioms Erdos7.supermodular_max_of_increasing_difference
