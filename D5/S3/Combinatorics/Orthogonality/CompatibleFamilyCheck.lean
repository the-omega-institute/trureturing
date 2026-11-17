/- GID: D5/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A terminating full compatible-family predicate check with a universal soundness proof. -/

import D5.S3.Combinatorics.Orthogonality.WeightedIndependentBound

/-! Both include/omit branches are checked. This universal theorem supplies
no assumed completeness or answer-encoding premise. The actual instances
bind the original finite domains and predicates, and still need reduction. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Orthogonality.CompatibleFamilyCheck
variable {α : Type*} [DecidableEq α]

/-- Check every compatible extension, including the empty extension.
The accumulator preserves all original data needed by the predicate. -/
def check (good : Finset α → Bool) (compatible : α → α → Bool) :
    ℕ → Finset α → List α → Bool
  | 0, selected, _ => good selected
  | _ + 1, selected, [] => good selected
  | fuel + 1, selected, a :: tail =>
      check good compatible fuel selected tail &&
      check good compatible fuel (insert a selected) (tail.filter (compatible a))

/-- Every compatible finite extension satisfies the checked full predicate. -/
theorem sound (good : Finset α → Bool) (compatible : α → α → Bool)
    (fuel : ℕ) (selected : Finset α) (candidates : List α)
    (hlen : candidates.length ≤ fuel) (S : Finset α)
    (hsub : ∀ x ∈ S, x ∈ candidates)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → compatible x y = true)
    (hc : check good compatible fuel selected candidates = true) :
    good (selected ∪ S) = true := by
  induction fuel generalizing selected candidates S with
  | zero =>
    have he : candidates = [] := List.length_eq_zero_iff.mp
      (Nat.eq_zero_of_le_zero hlen)
    have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro x hx
      simpa [he] using hsub x hx)
    simpa [hs,check] using hc
  | succ fuel ih =>
    cases candidates with
    | nil =>
      have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        simpa using hsub x hx)
      simpa [hs,check] using hc
    | cons a tail =>
      have ht : tail.length ≤ fuel := by simpa using hlen
      have hh := Bool.and_eq_true_iff.mp hc
      by_cases ha : a ∈ S
      · have he : ∀ x ∈ S.erase a, x ∈ tail.filter (compatible a) := by
          intro x hx
          have hxa := Finset.mem_erase.mp hx
          exact List.mem_filter.mpr
            ⟨(List.mem_cons.mp (hsub x hxa.2)).resolve_left hxa.1,
              hpair a ha x hxa.2 hxa.1.symm⟩
        have hp : ∀ x ∈ S.erase a, ∀ y ∈ S.erase a,
            x ≠ y → compatible x y = true := by
          intro x hx y hy hxy
          exact hpair x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have hb := ih (insert a selected) (tail.filter (compatible a))
          ((List.length_filter_le _ _).trans ht) (S.erase a) he hp hh.2
        have hu : insert a selected ∪ S.erase a = selected ∪ S := by
          ext x
          by_cases hxa : x = a
          · subst x
            simp [ha]
          · simp [hxa]
        simpa only [hu] using hb
      · have he : ∀ x ∈ S, x ∈ tail := by
          intro x hx
          rcases List.mem_cons.mp (hsub x hx) with h | h
          · exact (ha (h ▸ hx)).elim
          · exact h
        exact ih selected tail ht S he hpair hh.1

#print axioms sound
end D5.S3.Combinatorics.Orthogonality.CompatibleFamilyCheck
