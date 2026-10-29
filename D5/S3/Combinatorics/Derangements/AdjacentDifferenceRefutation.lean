/- GID: D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation
   mirror-E: none(waiver:direct-refutation-of-external-conjecture)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Centralizer]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.claim; result=D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.result; claim=D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.claim
   digest: The literal n-4 adjacent derangement identity fails at n=5. -/

import D5.S3.Combinatorics.Derangements.TerminalDifference

/-! Exact refutation of the original adjacent-column derangement conjecture. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Derangements.AdjacentDifferenceRefutation

open Equiv
open D5.S3.Combinatorics.Derangements.TerminalDifference

/-- The zero-offset A238474 formula, with exact rational division. -/
def b (m : ℕ) : ℚ :=
  (-1 : ℚ) ^ m * ((m + 3).factorial : ℚ) / (2 * ((m + 1 : ℕ) : ℚ))

/-- The original A378495 universal adjacent-column conjecture, preserving `n-4`. -/
def claim : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (T n (n - 1) : ℚ) - (T n (n - 2) : ℚ) = |b (n - 4)|

/-- At five labels the actual cardinality difference is 20, whereas `|b 1| = 6`. -/
theorem result : ¬ claim := by
  classical
  intro h
  have he : excluded 5 4 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hp' : p ∈ derangements (Fin 5) ∧ 4 ∈ p.cycleType := by
      simpa only [excluded, D, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have ht : p.cycleType = {4} :=
      Perm.cycleType_of_card_le_mem_cycleType_add_two (by norm_num) hp'.2
    have hs := (noFixed_iff_sum p).mp hp'.1
    simp [ht] at hs
  have h4 := T_add_excluded 5 4
  have h3 := T_add_excluded 5 3
  have hm := excluded_penultimate_mul (n := 5) (by omega)
  norm_num [he] at h4
  norm_num [Nat.factorial] at hm
  have hd : T 5 4 = T 5 3 + 20 := by omega
  have hdQ : (T 5 4 : ℚ) - (T 5 3 : ℚ) = 20 := by
    have hc : (T 5 4 : ℚ) = (T 5 3 : ℚ) + 20 := by exact_mod_cast hd
    linarith only [hc]
  have hh := h 5 (by omega)
  norm_num [b, Nat.factorial] at hh
  linarith only [hdQ, hh]

end D5.S3.Combinatorics.Derangements.AdjacentDifferenceRefutation
