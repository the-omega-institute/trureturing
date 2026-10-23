/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit affected-path replacement propagates the exact even and odd endpoint relations. -/
/- algebraic last step of the simultaneous boundary induction.
   This only proves (58.41)--(58.43) for the independently defined templates.
   Native J restoration must first earn this transformation on actual
   whole paths; no native realization or all-n induction is claimed here. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.RecursiveBoundaryAdvance

open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary

def previousIndex (p : RawPort) : RawPort := (p.1 - 1, p.2)

/-- Shift all old indices, remove the actual old L0--L(k-1) full path,
and splice its shifted ends through the two new single-order paths. -/
def advance (k : ℕ) (B : RawPort → RawPort → Prop) (p q : RawPort) : Prop :=
  (0 < p.1 ∧ 0 < q.1 ∧ B (previousIndex p) (previousIndex q) ∧
    ¬ pair (previousIndex p) (previousIndex q) (k - 1, 1) (0, 1)) ∨
    pair p q (0, 1) (k, 1) ∨ pair p q (0, 0) (1, 1)

set_option maxHeartbeats 800000 in
/-- The complete even template, including its guarded ladder range,
is stable under the single-order path update. -/
theorem advance_even_boundary (k : ℕ) (hk : 3 ≤ k) (p q : RawPort) :
    advance k (evenBoundary k) p q ↔ evenBoundary (k + 1) p q := by
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  by_cases hs₀ : s = 0 <;> by_cases hs₁ : s = 1 <;>
    by_cases ht₀ : t = 0 <;> by_cases ht₁ : t = 1 <;>
    simp_all [advance, previousIndex, evenBoundary, ladder, pair] <;> omega

set_option maxHeartbeats 800000 in
/-- The odd template has the same update; k=3 retains its empty old
ladder and gains precisely the new R0--L1 ladder edge at k=4. -/
theorem advance_odd_boundary (k : ℕ) (hk : 3 ≤ k) (p q : RawPort) :
    advance k (oddBoundary k) p q ↔ oddBoundary (k + 1) p q := by
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  by_cases hs₀ : s = 0 <;> by_cases hs₁ : s = 1 <;>
    by_cases ht₀ : t = 0 <;> by_cases ht₁ : t = 1 <;>
    simp_all [advance, previousIndex, oddBoundary, ladder, pair] <;> omega

#print axioms advance_even_boundary
#print axioms advance_odd_boundary

end D5.S3.Combinatorics.Graph.PrefixReversal.RecursiveBoundaryAdvance
