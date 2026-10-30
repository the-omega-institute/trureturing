/- GID: D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CharacteristicTwoNonFano
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/LinearAlgebra/FiniteDimensional/Lemmas]
   utility: none
   digest: Characteristic-two opposite-intersection geometry for arbitrary finite-dimensional subspaces. -/

/-
admission_basis: escape-witness
The opposite-intersection estimate is the characteristic-two geometric core
of the unrestricted seven-subspace rank-cone certificate.  It makes no
independence, equal-dimension, or nonzero-subspace assumption.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

open Module Submodule

namespace D5.S3.Combinatorics.Matroids.CharacteristicTwoNonFano

universe u v

section

variable {F : Type u} [Field F] [CharP F 2]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

private lemma char_two_add_self (x : V) : x + x = 0 := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_smul F x, htwo, zero_smul]

private lemma opposite_sum_inclusion
    (A B C Z : Submodule F V) :
    (A ⊔ Z) ⊓ (B ⊔ C) ≤ ((A ⊔ B) ⊓ (C ⊔ Z)) ⊔ ((A ⊔ C) ⊓ (B ⊔ Z)) := by
  intro y hy
  rcases Submodule.mem_sup.mp hy.1 with ⟨a, ha, z, hz, hayz⟩
  rcases Submodule.mem_sup.mp hy.2 with ⟨b, hb, c, hc, hbcy⟩
  have habcz : a + b = c + z := by
    calc
      a + b = (a + b) + (c + z) + (c + z) := by rw [char_two_add_self]
      _ = (a + z) + (b + c) + (c + z) := by abel
      _ = (a + z) + (a + z) + (c + z) := by rw [hbcy, ← hayz]
      _ = c + z := by rw [char_two_add_self]; simp
  have hacbz : a + c = b + z := by
    calc
      a + c = (a + c) + (b + z) + (b + z) := by rw [char_two_add_self]
      _ = (a + z) + (b + c) + (b + z) := by abel
      _ = (a + z) + (a + z) + (b + z) := by rw [hbcy, ← hayz]
      _ = b + z := by rw [char_two_add_self]; simp
  have hab : a + b ∈ (A ⊔ B) ⊓ (C ⊔ Z) := by
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩
    · rw [← habcz]
      exact Submodule.mem_sup.mpr ⟨c, hc, z, hz, rfl⟩
  have hac : a + c ∈ (A ⊔ C) ⊓ (B ⊔ Z) := by
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨a, ha, c, hc, rfl⟩
    · rw [← hacbz]
      exact Submodule.mem_sup.mpr ⟨b, hb, z, hz, rfl⟩
  rw [← hbcy]
  have hab' : a + b ∈
      ((A ⊔ B) ⊓ (C ⊔ Z)) ⊔ ((A ⊔ C) ⊓ (B ⊔ Z)) := mem_sup_left hab
  have hac' : a + c ∈
      ((A ⊔ B) ⊓ (C ⊔ Z)) ⊔ ((A ⊔ C) ⊓ (B ⊔ Z)) := mem_sup_right hac
  convert add_mem hab' hac' using 1 <;> abel

private lemma finrank_opposite_le_deficiency
    (A B C Z : Submodule F V)
    (hT : (A ⊔ B) ⊔ (C ⊔ Z) = A ⊔ B ⊔ C ⊔ Z)
    (O : Submodule F V) (hO : O = (A ⊔ B) ⊓ (C ⊔ Z)) :
    finrank F O ≤ finrank F A + finrank F B + finrank F C + finrank F Z -
      finrank F (A ⊔ B ⊔ C ⊔ Z) := by
  subst O
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (C ⊔ Z)
  have hAB := Submodule.finrank_add_le_finrank_add_finrank A B
  have hCZ := Submodule.finrank_add_le_finrank_add_finrank C Z
  rw [hT] at hdim
  omega

/-! The arbitrary-dimensional characteristic-two opposite-intersection bound. -/
theorem finrank_opposite_sum_le_two_deficiency
    (A B C Z : Submodule F V) :
    finrank F (((A ⊔ B) ⊓ (C ⊔ Z)) ⊔
      ((A ⊔ C) ⊓ (B ⊔ Z)) ⊔
      ((A ⊔ Z) ⊓ (B ⊔ C))) ≤
      2 * (finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z)) := by
  let OW : Submodule F V := (A ⊔ B) ⊓ (C ⊔ Z)
  let OX : Submodule F V := (A ⊔ C) ⊓ (B ⊔ Z)
  let OY : Submodule F V := (A ⊔ Z) ⊓ (B ⊔ C)
  have hOW : finrank F OW ≤
      finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z) := by
    apply finrank_opposite_le_deficiency A B C Z
    · simp [sup_assoc, sup_left_comm, sup_comm]
    · rfl
  have hOX : finrank F OX ≤
      finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z) := by
    have h := finrank_opposite_le_deficiency A C B Z
      (by simp [sup_assoc, sup_left_comm, sup_comm]) OX rfl
    simpa [add_left_comm, add_comm, sup_assoc, sup_left_comm, sup_comm] using h
  have hOY : OY ≤ OW ⊔ OX := by
    dsimp [OW, OX, OY]
    exact opposite_sum_inclusion A B C Z
  have hdim := Submodule.finrank_add_le_finrank_add_finrank OW OX
  have hsum : finrank F (OW ⊔ OX) ≤ finrank F OW + finrank F OX := hdim
  have hsum' : finrank F (OW ⊔ OX ⊔ OY) ≤
      finrank F OW + finrank F OX := by
    exact (Submodule.finrank_mono (sup_le le_rfl hOY)).trans hsum
  dsimp [OW, OX, OY] at hsum'
  omega

end

end D5.S3.Combinatorics.Matroids.CharacteristicTwoNonFano
