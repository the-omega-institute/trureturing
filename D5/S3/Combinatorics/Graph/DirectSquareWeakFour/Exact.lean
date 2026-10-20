/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact weak-four metric dimensions of every complete graph direct square of order at least four. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Construction
import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Exception

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

/-- The formula is a universal lower bound on actual landmark sets. -/
theorem lower_bound (n : ℕ) (hn : 4 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : IsWeakFour S) : target n ≤ S.card := by
  by_cases hlarge : 3*n-2 ≤ S.card
  · exact (target_lt_three n hn).le.trans hlarge
  obtain ⟨hr,hc⟩ := minimum_degrees hn S hS (by omega)
  have hl := linear_lower hn S hS hr hc
  by_cases hn5 : n = 5
  · subst n
    have ht : target 5 = 12 := by decide
    rw [ht]
    by_contra hh
    have he : S.card = 11 := by omega
    exact five_obstruction S hS he
  · simp only [target, if_neg hn5]
    omega

/-- The feasible family is nonempty and its least cardinality is attained. -/
theorem minimum (n : ℕ) (hn : 4 ≤ n) :
    ∃ S : Finset (Fin n × Fin n), IsWeakFour S ∧ S.card = target n ∧
      ∀ T : Finset (Fin n × Fin n), IsWeakFour T → S.card ≤ T.card := by
  obtain ⟨S,hS,hcard⟩ := construction n hn
  refine ⟨S,hS,hcard,?_⟩
  intro T hT
  rw [hcard]
  exact lower_bound n hn T hT

/-- Farhan--Kuziak--Yero's remaining direct-square question, for every n at least four. -/
def claim : Prop := ∀ n : ℕ, 4 ≤ n →
  wdim n = 2*n + ⌈(2*(n : ℚ))/11⌉₊ + (if n = 5 then 1 else 0)

private theorem ceiling_formula (n : ℕ) :
    ⌈(2*(n : ℚ))/11⌉₊ = (2*n+10)/11 := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.ceil_le, div_le_iff₀ (by norm_num : (0 : ℚ) < 11)]
  have hc : (2*(n : ℚ) ≤ (k : ℚ)*11) ↔ 2*n ≤ k*11 := by norm_cast
  rw [hc]
  omega

/-- The exact original weak-four minimum, with no assumed feasibility premise. -/
theorem result : claim := by
  intro n hn
  rw [ceiling_formula]
  obtain ⟨S,hS,hcard,hmin⟩ := minimum n hn
  apply le_antisymm
  · change wdim n ≤ target n
    calc
      wdim n ≤ S.card := csInf_le' (show S.card ∈
      {c : ℕ | ∃ T : Finset (Fin n × Fin n), IsWeakFour T ∧ T.card = c} from
      ⟨S,hS,rfl⟩)
      _ = target n := hcard
  · change target n ≤ wdim n
    apply le_csInf
    · exact ⟨S.card,S,hS,rfl⟩
    · rintro c ⟨T,hT,rfl⟩
      rw [← hcard]
      exact hmin T hT

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
