/- GID: D5/S3/Arith/Coding/UniqueDecodingRadius
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/UniqueDecodingRadius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimum distance gives unique decoding through the canonical half-distance radius. -/

import D5.S3.Arith.Coding.ResidueCodeErrorDetection
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * The current-tree search for `MinDistanceAtLeast`, `hammingDist`, and unique
     decoding found the family SSOT in `ResidueCodeErrorDetection`; this module
     imports its predicate and directly applies `codeword_eq_of_hammingDist_lt`.
   * Pinned Mathlib's `InformationTheory.Hamming` provides
     `hammingDist_triangle_left` and `hammingDist_eq_zero`, both applied below.
   * Repository and Mathlib searches found no packaged theorem combining the
     arbitrary unique-decoding radius with the `(d - 1) / 2` guarantee.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.UniqueDecodingRadius

open D5.S3.Arith.Coding.ResidueCodeErrorDetection

/-- A code of minimum distance `d` has a unique nearby codeword whenever twice
the error radius is below `d`, in particular through radius `(d - 1) / 2`. -/
theorem unique_decoding_radius {α : Type*} [DecidableEq α] {n d : ℕ}
    {C : Set (Fin n → α)} (hC : MinDistanceAtLeast C d) :
    (∀ trueWord received e, trueWord ∈ C →
      hammingDist received trueWord ≤ e → 2 * e < d →
      ∃! candidate, candidate ∈ C ∧ hammingDist received candidate ≤ e) ∧
    (∀ trueWord received, trueWord ∈ C →
      hammingDist received trueWord ≤ (d - 1) / 2 →
      ∃! candidate, candidate ∈ C ∧
        hammingDist received candidate ≤ (d - 1) / 2) := by
  have hUnique : ∀ trueWord received e, trueWord ∈ C →
      hammingDist received trueWord ≤ e → 2 * e < d →
      ∃! candidate, candidate ∈ C ∧ hammingDist received candidate ≤ e := by
    intro trueWord received e hTrue hReceived hRadius
    refine ⟨trueWord, ⟨hTrue, hReceived⟩, ?_⟩
    intro candidate hCandidate
    have hDistanceLt : hammingDist trueWord candidate < d := calc
      hammingDist trueWord candidate ≤
          hammingDist received trueWord + hammingDist received candidate :=
        hammingDist_triangle_left trueWord candidate received
      _ ≤ e + e := Nat.add_le_add hReceived hCandidate.2
      _ < d := by omega
    exact codeword_eq_of_hammingDist_lt hC hTrue hCandidate.1 hDistanceLt
  refine ⟨hUnique, ?_⟩
  intro trueWord received hTrue hReceived
  by_cases hd : d = 0
  · subst d
    have hReceivedZero : hammingDist received trueWord ≤ 0 := by
      simpa using hReceived
    have hReceivedEq : received = trueWord :=
      hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hReceivedZero)
    refine ⟨trueWord, ⟨hTrue, hReceivedZero⟩, ?_⟩
    intro candidate hCandidate
    have hCandidateEq : received = candidate :=
      hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hCandidate.2)
    exact hCandidateEq.symm.trans hReceivedEq
  · have hdPositive : 0 < d := Nat.pos_of_ne_zero hd
    have hRadius : 2 * ((d - 1) / 2) < d := by omega
    exact hUnique trueWord received ((d - 1) / 2) hTrue hReceived hRadius

#print axioms unique_decoding_radius

end D5.S3.Arith.Coding.UniqueDecodingRadius
