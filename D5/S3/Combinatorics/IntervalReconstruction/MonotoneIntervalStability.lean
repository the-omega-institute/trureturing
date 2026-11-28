/- GID: D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalStability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalStability
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/OmegaMath.Combinatorics.MonotoneIntervalStability]
   utility: none
   digest: Full interval occurrence matchings uniformly control nonnegative nondecreasing real tuples. -/

module

public import D5.S3.Combinatorics.IntervalReconstruction.Occurrences.MonotoneIntervalStability

/-! Uniform noisy recovery from all inclusive interval occurrences of length at least two. -/

@[expose] public section

namespace D5.S3.Combinatorics.IntervalReconstruction.MonotoneIntervalStability

open Omega.MonotoneIntervalReconstruction Omega.MonotoneIntervalStability

/-- A length-dependent constant works for every tuple, noise level and occurrence matching. -/
theorem result (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Fin n → ℝ,
      (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → Monotone a → Monotone b →
      ∀ ε : ℝ, 0 ≤ ε → ∀ π : Equiv.Perm (Occurrence n),
      (∀ p : Occurrence n,
        |intervalSum (extend a) p.val - intervalSum (extend b) (π p).val| ≤ ε) →
      ∀ i, |a i - b i| ≤ C * ε :=
  exists_uniform_recovery_constant n hn

end D5.S3.Combinatorics.IntervalReconstruction.MonotoneIntervalStability
