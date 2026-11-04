/- GID: D5/S1/Words/Compositions/WisemanA388713
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/WisemanA388713
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Superdiagonal reversed partitions and choosable partitions have equal counts by maximum. -/

/-
admission_basis: open-problem-resolution (#18603; Proved)
escape_witness: none
result: proof_shape: bind-only; consumer: none (settling result).
Same-delivery dependency: WisemanA388712.sorted_choosable_iff_superdiagonal.
The source counts retain their literal filters and reuse ChoosableInitial and
Superdiagonal from ChoosableInitialIntervals without duplicate predicates.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22068

The empty partition has maximum zero; both formal counts are 1 at (0,0),
whereas the printed OEIS row is 0. Both sides use the same vacuous predicates.
-/

import D5.S1.Words.Compositions.ChoosableInitialIntervals
import D5.S1.Words.Compositions.WisemanA388712

set_option autoImplicit false

namespace D5.S1.Words.Compositions.WisemanA388713

open D5.S1.Words.Compositions.ChoosableInitialIntervals

open scoped Classical in
/-- The number of superdiagonal reversed partitions of `n` with maximum `k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.sup = k ∧ Superdiagonal (p.parts.sort (· ≤ ·)))).card

open scoped Classical in
/-- The number of partitions of `n` with maximum `k` and choosable initial intervals. -/
noncomputable def choosable (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.sup = k ∧ ChoosableInitial (p.parts.sort (· ≥ ·)))).card

/-- The conjecture of A388713. -/
def claim : Prop := ∀ n k : ℕ, T n k = choosable n k

/-- Equality of the two partition counts for every value of the parameters. -/
theorem result : WisemanA388713.claim := by
  classical
  intro n k
  unfold T choosable
  congr 1
  apply Finset.filter_congr
  intro p _
  exact and_congr_right (fun _ =>
    (WisemanA388712.sorted_choosable_iff_superdiagonal p.parts).symm)

end D5.S1.Words.Compositions.WisemanA388713
