/- GID: D5/S3/Arith/Coding/ResidueCodeErrorDetection
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ResidueCodeErrorDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Codes of minimum distance at least d detect every nonzero error of weight at most d-1, and the bound is sharp. -/

import Mathlib.InformationTheory.Hamming

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'detects_up_to_min_distance_minus_one' D5 Golden/Frozen/accepted`
     returned no matches.
   * The broad repository search for `hammingDist|minDistance|codeword|errorDetect`
     found the unrelated public `D5.S0.Diagonal.DistanceProfile.hammingDistance` and its
     listing-count theorems, plus one private listing equivalence, but no code-set minimum
     distance or error-detection theorem. The new `Coding` directory was empty before this
     module; every digest in both adjacent Arith directories was checked without a match.
   * Pinned Mathlib's `InformationTheory.Hamming` provides `hammingDist` and its basic
     zero, symmetry, triangle, positivity, and cardinality lemmas, but no minimum-distance
     code predicate or detection-bound theorem. This module reuses `hammingDist` and
     `hammingDist_pos`; the remaining proof is order reasoning and a concrete Boolean count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ResidueCodeErrorDetection

/-- Every pair of distinct codewords has Hamming distance at least `d`. -/
def MinDistanceAtLeast {α : Type*} [DecidableEq α] {n : ℕ}
    (C : Set (Fin n → α)) (d : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c'

/-- A word less than the minimum distance from a codeword cannot be another codeword. -/
theorem codeword_eq_of_hammingDist_lt {α : Type*} [DecidableEq α] {n d : ℕ}
    {C : Set (Fin n → α)} {c x : Fin n → α} (hC : MinDistanceAtLeast C d)
    (hc : c ∈ C) (hx : x ∈ C) (hLt : hammingDist c x < d) : x = c := by
  by_contra hxc
  exact (Nat.not_le_of_lt hLt) (hC c hc x hx (Ne.symm hxc))

/-- Every nonzero error affecting at most `d - 1` coordinates is detected. -/
theorem detects_up_to_min_distance_minus_one {α : Type*} [DecidableEq α] {n d : ℕ}
    {C : Set (Fin n → α)} {c x : Fin n → α} (hC : MinDistanceAtLeast C d)
    (hc : c ∈ C) (hPositive : 1 ≤ hammingDist c x)
    (hBound : hammingDist c x ≤ d - 1) : x ∉ C := by
  intro hx
  have hne : c ≠ x := hammingDist_pos.mp hPositive
  have hMin : d ≤ hammingDist c x := hC c hc x hx hne
  have hd : 0 < d := by
    by_contra h
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos h
    subst d
    exact Nat.not_succ_le_zero 0 (hPositive.trans hBound)
  have hLt : hammingDist c x < d := (Nat.le_sub_one_iff_lt hd).mp hBound
  exact (Nat.not_le_of_lt hLt) hMin

/-- The `d - 1` guarantee is sharp: at distance `d`, corruption can reach a codeword. -/
theorem detection_bound_is_sharp (d : ℕ) (hd : 0 < d) :
    ∃ (C : Set (Fin d → Bool)) (c x : Fin d → Bool),
      MinDistanceAtLeast C d ∧ c ∈ C ∧ x ∈ C ∧ c ≠ x ∧ hammingDist c x = d := by
  let c₀ : Fin d → Bool := fun _ => false
  let c₁ : Fin d → Bool := fun _ => true
  let C : Set (Fin d → Bool) := {c₀, c₁}
  have hdist : hammingDist c₀ c₁ = d := by
    simp [hammingDist, c₀, c₁]
  have hne : c₀ ≠ c₁ := by
    intro h
    have hcoordinate := congrFun h ⟨0, hd⟩
    simp [c₀, c₁] at hcoordinate
  refine ⟨C, c₀, c₁, ?_, ?_, ?_, hne, hdist⟩
  · intro c hc c' hc' hcc'
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hc'
    rcases hc with (rfl | rfl) <;> rcases hc' with (rfl | rfl)
    · exact (hcc' rfl).elim
    · exact hdist.ge
    · rw [hammingDist_comm]
      exact hdist.ge
    · exact (hcc' rfl).elim
  · simp [C]
  · simp [C]

example :
    ∃ (C : Set (Fin 3 → Bool)) (c x : Fin 3 → Bool),
      MinDistanceAtLeast C 3 ∧ c ∈ C ∧ x ∈ C ∧ c ≠ x ∧ hammingDist c x = 3 := by
  exact detection_bound_is_sharp 3 (by decide)

#print axioms detects_up_to_min_distance_minus_one
#print axioms detection_bound_is_sharp

end D5.S3.Arith.Coding.ResidueCodeErrorDetection
