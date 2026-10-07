/- GID: D5/S3/FiniteGroups/NikolovSegal/Alpha
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Alpha
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The attained largest alternating section degree of a finite group. -/

import D5.S3.FiniteGroups.NikolovSegal.Sections
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false

namespace NikolovSegal

universe u v

def alternatingDegrees (G : Type u) [Group G] : Set ℕ :=
  {k | Involves (alternatingGroup (Fin k)) G}

/-- For finite groups this is the largest alternating section degree, including
the trivial alternating groups at the small degrees. -/
noncomputable def alpha (G : Type u) [Group G] : ℕ := sSup (alternatingDegrees G)

variable {G : Type u} [Group G]

theorem alternatingDegrees_nonempty : (alternatingDegrees G).Nonempty := by
  refine ⟨0, involves_of_surjective (1 : G →* alternatingGroup (Fin 0)) ?_⟩
  intro a
  exact ⟨1, Subsingleton.elim _ _⟩

theorem alternating_degree_card_bound [Finite G] {k : ℕ}
    (h : Involves (alternatingGroup (Fin k)) G) : k ≤ 2 * Nat.card G + 1 := by
  by_cases hk : 2 ≤ k
  · have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    have hc : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (involves_card_dvd h)
    have heq := two_mul_nat_card_alternatingGroup (α := Fin k)
    simp only [Nat.card_perm, Nat.card_fin] at heq
    have hfac := Nat.self_le_factorial k
    omega
  · omega

theorem alternatingDegrees_bddAbove [Finite G] : BddAbove (alternatingDegrees G) :=
  ⟨2 * Nat.card G + 1, fun _ h => alternating_degree_card_bound h⟩

/-- This verifies that the supremum really is the paper's largest section degree. -/
theorem alpha_spec [Finite G] :
    Involves (alternatingGroup (Fin (alpha G))) G ∧
      ∀ k, Involves (alternatingGroup (Fin k)) G → k ≤ alpha G := by
  exact ⟨Nat.sSup_mem alternatingDegrees_nonempty alternatingDegrees_bddAbove,
    fun _ h => le_csSup alternatingDegrees_bddAbove h⟩

/-- The all-degrees section transfer implies exactly the stated maximum bound. -/
theorem alpha_le_max_of_section_transfer {Q : Type v} [Group Q] [Finite Q]
    (h : ∀ k : ℕ, 5 ≤ k → Involves (alternatingGroup (Fin k)) G →
      Involves (alternatingGroup (Fin k)) Q) : alpha G ≤ max (alpha Q) 4 := by
  apply csSup_le alternatingDegrees_nonempty
  intro k hk
  by_cases hsmall : k ≤ 4
  · exact hsmall.trans (le_max_right _ _)
  · exact ((alpha_spec (G := Q)).2 k (h k (by omega) hk)).trans (le_max_left _ _)

end NikolovSegal
