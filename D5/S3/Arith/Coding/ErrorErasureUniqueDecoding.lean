/- GID: D5/S3/Arith/Coding/ErrorErasureUniqueDecoding
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ErrorErasureUniqueDecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint errors and erasures decode uniquely below the minimum distance. -/

import D5.S3.Arith.Coding.ResidueCodeErrorDetection
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * Current-tree searches for joint error/erasure decoding, `2 * e + s`, known
     erasures, and uniqueness found no exact D5 theorem.
   * The exact family primitives are `ResidueCodeErrorDetection.MinDistanceAtLeast`
     and `codeword_eq_of_hammingDist_lt`; both are imported and applied directly.
   * `UniqueDecodingRadius.unique_decoding_radius` covers unknown errors without an
     erased-coordinate carrier, so it is adjacent but not an exact atom hit.
   * Pinned Mathlib's `InformationTheory.Hamming` supplies `hammingDist` and its
     coordinate-filter definition, while `Finset.card_union_le` supplies the finite
     disagreement bound. Pinned Mathlib has no joint error-and-erasure uniqueness theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ErrorErasureUniqueDecoding

open D5.S3.Arith.Coding.ResidueCodeErrorDetection

/-- If each legal candidate has at most `e` disagreements with the received word
outside at most `s` known erased coordinates, then `2 * e + s < d` makes the legal
candidate unique for a code of minimum distance at least `d`. -/
theorem error_erasure_unique_decoding
    {α : Type*} [DecidableEq α] {n d e s : ℕ}
    {C : Set (Fin n → α)} (hC : MinDistanceAtLeast C d)
    (erased : Finset (Fin n)) (hErased : erased.card ≤ s)
    (hBudget : 2 * e + s < d) :
    ∀ (trueWord received : Fin n → α), trueWord ∈ C →
      (Finset.univ.filter fun i => i ∉ erased ∧ received i ≠ trueWord i).card ≤ e →
      ∃! candidate, candidate ∈ C ∧
        (Finset.univ.filter fun i => i ∉ erased ∧ received i ≠ candidate i).card ≤ e := by
  intro trueWord received hTrue hTrueErrors
  refine ⟨trueWord, ⟨hTrue, hTrueErrors⟩, ?_⟩
  intro candidate hCandidate
  have hDistanceLt : hammingDist trueWord candidate < d := by
    let trueErrors : Finset (Fin n) :=
      Finset.univ.filter fun i => i ∉ erased ∧ received i ≠ trueWord i
    let candidateErrors : Finset (Fin n) :=
      Finset.univ.filter fun i => i ∉ erased ∧ received i ≠ candidate i
    have hTrueCard : trueErrors.card ≤ e := by
      simpa only [trueErrors] using hTrueErrors
    have hCandidateCard : candidateErrors.card ≤ e := by
      simpa only [candidateErrors] using hCandidate.2
    have hSubset :
        Finset.univ.filter (fun i => trueWord i ≠ candidate i) ⊆
          erased ∪ (trueErrors ∪ candidateErrors) := by
      intro i hi
      have hWordsDiffer : trueWord i ≠ candidate i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      by_cases hErase : i ∈ erased
      · exact Finset.mem_union_left _ hErase
      · have hError : received i ≠ trueWord i ∨ received i ≠ candidate i := by
          by_contra hNoError
          simp only [not_or, not_not] at hNoError
          exact hWordsDiffer (hNoError.1.symm.trans hNoError.2)
        apply Finset.mem_union_right erased
        rcases hError with hTrueError | hCandidateError
        · apply Finset.mem_union_left candidateErrors
          simp only [trueErrors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hErase, hTrueError⟩
        · apply Finset.mem_union_right trueErrors
          simp only [candidateErrors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hErase, hCandidateError⟩
    calc
      hammingDist trueWord candidate =
          (Finset.univ.filter fun i => trueWord i ≠ candidate i).card := rfl
      _ ≤ (erased ∪ (trueErrors ∪ candidateErrors)).card :=
        Finset.card_le_card hSubset
      _ ≤ erased.card + (trueErrors ∪ candidateErrors).card :=
        Finset.card_union_le erased (trueErrors ∪ candidateErrors)
      _ ≤ erased.card + (trueErrors.card + candidateErrors.card) :=
        Nat.add_le_add_left (Finset.card_union_le trueErrors candidateErrors) erased.card
      _ ≤ s + (e + e) :=
        Nat.add_le_add hErased (Nat.add_le_add hTrueCard hCandidateCard)
      _ < d := by omega
  exact codeword_eq_of_hammingDist_lt hC hTrue hCandidate.1 hDistanceLt

#print axioms error_erasure_unique_decoding

end D5.S3.Arith.Coding.ErrorErasureUniqueDecoding
