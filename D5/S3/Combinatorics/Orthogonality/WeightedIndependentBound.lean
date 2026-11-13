/- GID: D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/WeightedIndependentBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weighted_bound; instance=D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check
   digest: Exhaustive weighted independent-set bound with a universal finite-set soundness proof. -/

import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! A terminating include-or-omit recursion checks a bound for every independent
subset, rather than sampling sets or assuming a maximum. The independent
question and its six-bit input are the received O2 weighted inequality. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.WeightedIndependentBound

variable {α : Type*} [DecidableEq α]

/-- Compatibility means that two distinct selected vertices may share a color. -/
def bound (weight : α → ℕ) (compatible : α → α → Bool) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, a :: tail =>
      max (bound weight compatible fuel tail)
        (weight a + bound weight compatible fuel (tail.filter (compatible a)))

/-- Every compatible finite subset is bounded. No completeness premise is
supplied by the caller: both possibilities for each candidate are covered. -/
theorem sound (weight : α → ℕ) (compatible : α → α → Bool)
    (fuel : ℕ) (candidates : List α) (hlen : candidates.length ≤ fuel)
    (S : Finset α) (hsub : ∀ x ∈ S, x ∈ candidates)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → compatible x y = true) :
    ∑ x ∈ S, weight x ≤ bound weight compatible fuel candidates := by
  induction fuel generalizing candidates S with
  | zero =>
    have hc : candidates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro x hx
      simpa [hc] using hsub x hx)
    simp [hs, bound]
  | succ fuel ih =>
    cases candidates with
    | nil =>
      have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        simpa using hsub x hx)
      simp [hs, bound]
    | cons a tail =>
      have ht : tail.length ≤ fuel := by simpa using hlen
      by_cases ha : a ∈ S
      · have he : ∀ x ∈ S.erase a, x ∈ tail.filter (compatible a) := by
          intro x hx
          have hxa := Finset.mem_erase.mp hx
          apply List.mem_filter.mpr
          refine ⟨?_, hpair a ha x hxa.2 (Ne.symm hxa.1)⟩
          exact (List.mem_cons.mp (hsub x hxa.2)).resolve_left hxa.1
        have hp : ∀ x ∈ S.erase a, ∀ y ∈ S.erase a,
            x ≠ y → compatible x y = true := by
          intro x hx y hy hxy
          exact hpair x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have hb := ih (tail.filter (compatible a))
          ((List.length_filter_le _ _).trans ht) (S.erase a) he hp
        have hsum := Finset.sum_erase_add S weight ha
        dsimp only [bound]
        exact (by omega : (∑ x ∈ S, weight x) ≤ weight a +
          bound weight compatible fuel (tail.filter (compatible a))).trans (le_max_right _ _)
      · have he : ∀ x ∈ S, x ∈ tail := by
          intro x hx
          rcases List.mem_cons.mp (hsub x hx) with h | h
          · exact (ha (h ▸ hx)).elim
          · exact h
        exact (ih tail ht S he hpair).trans (le_max_left _ _)

#print axioms sound

end D5.S3.Combinatorics.Orthogonality.WeightedIndependentBound
