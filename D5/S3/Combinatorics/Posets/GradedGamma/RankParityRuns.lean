/- GID: D5/S3/Combinatorics/Posets/GradedGamma/RankParityRuns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/RankParityRuns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Atoms.Finite]
   utility: none
   digest: A constant-parity interval in a graded extension is an antichain. -/

import D5.S3.Combinatorics.Posets.PPartitions.Definitions
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Grade
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions

/-- A comparable pair in a linear extension forces an opposite-parity grade
between its positions, unless it is a cover; covers themselves change parity. -/
theorem parity_run_incomparable {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (e : EnumeratingExtension α)
    (i j : Fin (Fintype.card α))
    (hsame : ∀ k : Fin (Fintype.card α), i ≤ k → k ≤ j →
      (grade ℕ (e k)) % 2 = (grade ℕ (e i)) % 2) :
    ¬ e i < e j := by
  intro hcmp
  obtain ⟨z, hcov, hzy⟩ := exists_covBy_le_of_lt hcmp
  have hik : i < e.1.symm z := by
    simpa using e.2 hcov.lt
  have hkj : e.1.symm z ≤ j := by
    rcases hzy.eq_or_lt with rfl | hlt
    · simp
    · simpa using (e.2 hlt).le
  have hpar := hsame (e.1.symm z) hik.le hkj
  simp only [Equiv.apply_symm_apply] at hpar
  have hgrade : grade ℕ z = grade ℕ (e i) + 1 :=
    (Nat.covBy_iff_add_one_eq.mp (hcov.grade ℕ)).symm
  rw [hgrade] at hpar
  omega

end D5.S3.Combinatorics.Posets.GradedGamma
