/- GID: D5/S1/Digit/Infinite/PendingObligationLift
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/PendingObligationLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transported endpoint exclusions characterize exact finite observation histories. -/

import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
import D5.S1.Digit.Infinite.FixedTailClosedBudget

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.PendingObligationLift

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.FixedTailClosedBudget (SourcePath addressPrefix source_path_realization)

/-- Insert the current exclusions, transport all outstanding equalities, and
discard equalities outside the next guard interval. -/
noncomputable def pending (F : ℕ → ℝ → ℝ) (P I Z : ℕ → Set ℝ) : ℕ → Set ℝ
  | 0 => ∅
  | n + 1 => (F n '' (pending F P I Z n ∪ (Z n ∩ P n))) ∩ I (n + 1)

private theorem history_avoidance (F : ℕ → ℝ → ℝ) (P I Z : ℕ → Set ℝ)
    (x : ℕ → ℝ) (n : ℕ)
    (hF : ∀ j < n, Function.Injective (F j))
    (hP : ∀ j < n, x j ∈ P j) (hI : ∀ j ≤ n, x j ∈ I j)
    (hstep : ∀ j < n, x (j + 1) = F j (x j)) :
    x n ∉ pending F P I Z n ↔ ∀ j < n, x j ∉ Z j := by
  induction n with
  | zero => simp [pending]
  | succ n ih =>
    have hpast := ih (fun j hj => hF j (by omega))
      (fun j hj => hP j (by omega)) (fun j hj => hI j (by omega))
      (fun j hj => hstep j (by omega))
    have hmem : x (n + 1) ∈ pending F P I Z (n + 1) ↔
        x n ∈ pending F P I Z n ∨ x n ∈ Z n := by
      simp only [pending, Set.mem_inter_iff, Set.mem_image, Set.mem_union,
        Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨z, hz, he⟩, _⟩
        have heq : z = x n := hF n (by omega) (he.trans (hstep n (by omega)))
        subst z
        exact hz.elim Or.inl (fun h => Or.inr h.1)
      · intro h
        refine ⟨⟨x n, ?_, (hstep n (by omega)).symm⟩, hI (n + 1) le_rfl⟩
        exact h.elim Or.inl (fun h => Or.inr ⟨h, hP n (by omega)⟩)
    rw [hmem, not_or, hpast]
    constructor
    · rintro ⟨hp, hn⟩ j hj
      by_cases hjn : j < n
      · exact hp j hjn
      · have : j = n := by omega
        simpa [this] using hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

end D5.S1.Digit.Infinite.PendingObligationLift
