/- GID: D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CharacteristicTwoNonFano
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/LinearAlgebra/FiniteDimensional/Lemmas]
   utility: none
   digest: Characteristic-two opposite-intersection geometry in arbitrary finite dimensions. -/

/-
admission_basis: escape-witness
The opposite-intersection estimate is the characteristic-two geometric core
of the unrestricted seven-subspace rank-cone certificate.  It makes no
independence, equal-dimension, or nonzero-subspace assumption.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel

/-! # Characteristic-two opposite intersections

The three opposite intersections of four arbitrary subspaces have total span
dimension at most twice their relation deficiency.
-/

public section

open Module Submodule

namespace D5.S3.Combinatorics.Matroids.CharacteristicTwoNonFano

universe u v

section

variable {F : Type u} [Field F] [CharP F 2]
variable {V : Type v} [AddCommGroup V] [Module F V]

private lemma char_two_add_self {F : Type u} [Field F] [CharP F 2]
    {V : Type v} [AddCommGroup V] [Module F V] (x : V) : x + x = 0 := by
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
      a + b = (a + b) + (c + z) + (c + z) := by
        rw [add_assoc, char_two_add_self (F := F), add_zero]
      _ = (a + z) + (b + c) + (c + z) := by abel
      _ = (a + z) + (a + z) + (c + z) := by rw [hbcy, ← hayz]
      _ = c + z := by rw [char_two_add_self (F := F), zero_add]
  have hacbz : a + c = b + z := by
    calc
      a + c = (a + c) + (b + z) + (b + z) := by
        rw [add_assoc, char_two_add_self (F := F), add_zero]
      _ = (a + z) + (b + c) + (b + z) := by abel
      _ = (a + z) + (a + z) + (b + z) := by rw [hbcy, ← hayz]
      _ = b + z := by rw [char_two_add_self (F := F), zero_add]
  have hab : a + b ∈ (A ⊔ B) ⊓ (C ⊔ Z) := by
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩
    · rw [habcz]
      exact Submodule.mem_sup.mpr ⟨c, hc, z, hz, rfl⟩
  have hac : a + c ∈ (A ⊔ C) ⊓ (B ⊔ Z) := by
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup.mpr ⟨a, ha, c, hc, rfl⟩
    · rw [hacbz]
      exact Submodule.mem_sup.mpr ⟨b, hb, z, hz, rfl⟩
  rw [← hbcy]
  have hab' : a + b ∈
      ((A ⊔ B) ⊓ (C ⊔ Z)) ⊔ ((A ⊔ C) ⊓ (B ⊔ Z)) := mem_sup_left hab
  have hac' : a + c ∈
      ((A ⊔ B) ⊓ (C ⊔ Z)) ⊔ ((A ⊔ C) ⊓ (B ⊔ Z)) := mem_sup_right hac
  have hcancel : (a + b) + (a + c) = b + c := by
    calc
      (a + b) + (a + c) = (a + a) + (b + c) := by abel
      _ = b + c := by rw [char_two_add_self (F := F), zero_add]
  simpa only [hcancel] using add_mem hab' hac'

variable [FiniteDimensional F V]

omit [CharP F 2] in
private lemma finrank_opposite_le_deficiency
    (A B C Z : Submodule F V)
    (hT : (A ⊔ B) ⊔ (C ⊔ Z) = A ⊔ B ⊔ C ⊔ Z)
    (O : Submodule F V) (hO : O = (A ⊔ B) ⊓ (C ⊔ Z)) :
    finrank F O ≤ finrank F A + finrank F B + finrank F C + finrank F Z -
      finrank F (A ⊔ B ⊔ C ⊔ Z : Submodule F V) := by
  subst O
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (C ⊔ Z)
  have hAB := Submodule.finrank_add_le_finrank_add_finrank A B
  have hCZ := Submodule.finrank_add_le_finrank_add_finrank C Z
  rw [hT] at hdim
  omega

/-- The arbitrary-dimensional characteristic-two opposite-intersection bound. -/
theorem finrank_opposite_sum_le_two_deficiency
    (A B C Z : Submodule F V) :
    finrank F (((A ⊔ B) ⊓ (C ⊔ Z)) ⊔
      ((A ⊔ C) ⊓ (B ⊔ Z)) ⊔
      ((A ⊔ Z) ⊓ (B ⊔ C)) : Submodule F V) ≤
      2 * (finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z : Submodule F V)) := by
  let OW : Submodule F V := (A ⊔ B) ⊓ (C ⊔ Z)
  let OX : Submodule F V := (A ⊔ C) ⊓ (B ⊔ Z)
  let OY : Submodule F V := (A ⊔ Z) ⊓ (B ⊔ C)
  have hOW : finrank F OW ≤
      finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z : Submodule F V) := by
    apply finrank_opposite_le_deficiency A B C Z
    · simp [sup_left_comm, sup_comm]
    · rfl
  have hOX : finrank F OX ≤
      finrank F A + finrank F B + finrank F C + finrank F Z -
        finrank F (A ⊔ B ⊔ C ⊔ Z : Submodule F V) := by
    have h := finrank_opposite_le_deficiency A C B Z
      (by simp [sup_left_comm, sup_comm]) OX rfl
    have hperm : (A ⊔ C ⊔ B ⊔ Z : Submodule F V) = A ⊔ B ⊔ C ⊔ Z := by
      ac_rfl
    rw [hperm] at h
    omega
  have hOY : OY ≤ OW ⊔ OX := by
    dsimp [OW, OX, OY]
    exact opposite_sum_inclusion A B C Z
  have hdim := Submodule.finrank_add_le_finrank_add_finrank OW OX
  have hsum : finrank F (OW ⊔ OX : Submodule F V) ≤ finrank F OW + finrank F OX := hdim
  have hsum' : finrank F (OW ⊔ OX ⊔ OY : Submodule F V) ≤
      finrank F OW + finrank F OX := by
    exact (Submodule.finrank_mono (sup_le le_rfl hOY)).trans hsum
  change finrank F (OW ⊔ OX ⊔ OY : Submodule F V) ≤ _
  omega

end

end D5.S3.Combinatorics.Matroids.CharacteristicTwoNonFano
