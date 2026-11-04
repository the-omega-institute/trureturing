/- GID: D5/S1/Words/Powers/ZeckendorfDeletion
   generality: I
   mirror-B: D5/B/S1/Words/Powers/ZeckendorfDeletion
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Literal least-position Zeckendorf deletion inverts golden substitution blocks. -/

import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf
import D5.S1.Digit.GoldenBase4DenseInput

/-! Literal positional deletion and its golden substitution block. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Powers.ZeckendorfDeletion

open D5.S0.Conventions
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf
open D5.S1.Digit.GoldenBase4DenseInput

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- Delete the position of weight `F₂ = 1`, lower every surviving index by one,
and decode in the same Fibonacci system. This is the literal A319433 operation. -/
def deleteLeast (n : ℕ) : ℕ :=
  (((wdigits n).filter fun k => 3 ≤ k).map fun k => Nat.fib (k - 1)).sum

private theorem delete_start (k : ℕ) : deleteLeast (goldenSubstStart k) = k := by
  rw [deleteLeast, golden_subst_start_wdigits]
  have hfilter : ((wdigits k).map fun j => j + 1).filter (fun j => 3 ≤ j) =
      (wdigits k).map fun j => j + 1 := by
    apply List.filter_eq_self.mpr
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := (occupied_index_bounds k i hi).1
    simp only [decide_eq_true_eq]
    omega
  rw [hfilter, List.map_map]
  simpa only [Function.comp_def, Nat.add_sub_cancel] using decode_wdigits k

private theorem delete_second (k : ℕ) (hk : goldenWord k = true) :
    deleteLeast (goldenSubstStart k + 1) = k := by
  have htwo : 2 ∉ wdigits k := (goldenWord_char_zeckendorf k).mp hk
  have hcanonical :
      (wdigits (goldenSubstStart k) ++ [2]).IsZeckendorfRep := by
    rw [List.IsZeckendorfRep, List.append_assoc, List.isChain_iff_pairwise,
      List.pairwise_append]
    refine ⟨?_, by norm_num, ?_⟩
    · exact (List.pairwise_append.mp
        (List.isChain_iff_pairwise.mp (wdigits_isCanonical _))).1
    · intro a ha b hb
      rw [golden_subst_start_wdigits] at ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      have hmin := (occupied_index_bounds k j hj).1
      have hne : j ≠ 2 := fun h => htwo (h ▸ hj)
      have hb' : b = 2 ∨ b = 0 := by simpa using hb
      rcases hb' with rfl | rfl <;> omega
  have hdigits : wdigits (goldenSubstStart k + 1) =
      wdigits (goldenSubstStart k) ++ [2] := by
    symm
    apply wdigits_unique hcanonical
    simp [List.map_append, decode_wdigits]
  rw [deleteLeast, hdigits, List.filter_append, List.map_append, List.sum_append]
  simpa [deleteLeast] using delete_start k

/-- Every natural index lies in the golden substitution block whose index is
its independently decoded, literal Zeckendorf deletion. -/
theorem deletion_block (n : ℕ) :
    goldenSubstStart (deleteLeast n) ≤ n ∧
      n < goldenSubstStart (deleteLeast n + 1) := by
  obtain ⟨k, hlo, hhi⟩ := exists_goldenSubstStart_window n
  have hdel : deleteLeast n = k := by
    by_cases hn : n = goldenSubstStart k
    · rw [hn, delete_start]
    · have hkn : goldenSubstStart k < n := by omega
      have hk : goldenWord k = true := by
        cases hword : goldenWord k with
        | false =>
            rw [goldenSubstStart_step_false hword] at hhi
            omega
        | true => rfl
      rw [goldenSubstStart_step_true hk] at hhi
      have hn' : n = goldenSubstStart k + 1 := by omega
      rw [hn', delete_second k hk]
  simpa only [hdel] using And.intro hlo hhi

#print axioms deletion_block

end D5.S1.Words.Powers.ZeckendorfDeletion
