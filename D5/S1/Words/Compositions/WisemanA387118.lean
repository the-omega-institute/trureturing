/- GID: D5/S1/Words/Compositions/WisemanA387118
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/WisemanA387118
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonchoosable partitions and nonsuperdiagonal reversed partitions have equal totals. -/

/-
admission_basis: open-problem-resolution (#18602; Proved)
escape_witness: none
result: proof_shape: bind-only; consumer: none (settling result).
Same-delivery dependency: WisemanA388712.sorted_choosable_iff_superdiagonal.
The source counts retain their literal filters and reuse ChoosableInitial and
Superdiagonal from ChoosableInitialIntervals without duplicate predicates.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22068

-/

import D5.S1.Words.Compositions.ChoosableInitialIntervals
import D5.S1.Words.Compositions.WisemanA388712

set_option autoImplicit false

namespace D5.S1.Words.Compositions.WisemanA387118

open D5.S1.Words.Compositions.ChoosableInitialIntervals

open scoped Classical in
/-- The number of integer partitions of `n` without choosable initial intervals. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => ¬ ChoosableInitial (p.parts.sort (· ≥ ·)))).card

open scoped Classical in
/-- The number of non-superdiagonal reversed integer partitions of `n`. -/
noncomputable def nonSuperdiagonal (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => ¬ Superdiagonal (p.parts.sort (· ≤ ·)))).card

/-- The conjecture of A387118. -/
def claim : Prop := ∀ n : ℕ, a n = nonSuperdiagonal n

/-- Equality of the two partition counts for every value of the parameters. -/
theorem result : WisemanA387118.claim := by
  classical
  intro n
  unfold a nonSuperdiagonal
  congr 1
  apply Finset.filter_congr
  intro p _
  exact not_congr (WisemanA388712.sorted_choosable_iff_superdiagonal p.parts)

end D5.S1.Words.Compositions.WisemanA387118
