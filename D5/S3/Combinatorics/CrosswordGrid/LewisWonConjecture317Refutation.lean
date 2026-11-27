/- GID: D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.claim; result=D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result; claim=D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.claim
   digest: The only admissible size at n = 3 lies on the excluded lower endpoint. -/

/- Judgement form for preregistration #34932.
   admission_basis: open-problem-resolution.
   result: bind-only. The exact cutoff and admissibility at size three contradict
     the strict lower bound by normalization and natural linear arithmetic.
   Direct frozen dependencies: none. Escape witness: none.
   eq31 and isLowerCutoff define the data used in claim; result also uses isLowerCutoff. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Enumerative.Stirling

/-! The existential maximizer assertion fails at the first size in the cutoff domain. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.CrosswordGrid.LewisWonConjecture317Refutation

private def eq31 (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m, (Nat.stirlingSecond m k * k ^ (n - 2 * m) * k.factorial) ^ 2

private def isLowerCutoff (n : ℕ) (x : ℝ) : Prop :=
  1 ≤ x ∧ (n : ℝ) = Real.log (x + 1) / Real.log (1 + 1 / x) + 2 * x

/-- The existential maximizer in Lewis and Won, §3.4, printed pp. 20–22. -/
def claim : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ x : ℝ, isLowerCutoff n x →
    ∃ m : ℕ, ((1 ≤ m ∧ 2 * m ≤ n) ∧
      (∀ j : ℕ, (1 ≤ j ∧ 2 * j ≤ n) → eq31 n j ≤ eq31 n m)) ∧
      x < (m : ℝ) ∧ (m : ℝ) < x + 2

/-- At size three the only admissible size equals the strict lower endpoint. -/
theorem result : ¬ claim := by
  have cutoff : isLowerCutoff 3 1 := by
    have logTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨le_rfl, ?_⟩
    change (3 : ℝ) = Real.log (1 + 1) / Real.log (1 + 1 / 1) + 2 * 1
    norm_num [ne_of_gt logTwoPos]
  intro asserted
  obtain ⟨m, ⟨⟨positive, balanced⟩, _⟩, lower, _⟩ := asserted 3 le_rfl 1 cutoff
  have size : m = 1 := by omega
  rw [size] at lower
  norm_num at lower

end D5.S3.Combinatorics.CrosswordGrid.LewisWonConjecture317Refutation
