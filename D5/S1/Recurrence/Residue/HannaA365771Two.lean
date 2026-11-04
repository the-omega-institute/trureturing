/- GID: D5/S1/Recurrence/Residue/HannaA365771Two
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA365771Two
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's congruence (2) follows from the base-five residue classification. -/

/-
admission_basis: open-problem-resolution (#18657; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22018
Direct frozen dependencies: none.
Same-delivery content: D5/S1/Recurrence/Residue/HannaA365771.
The sequence and digit predicate are reused from HannaA365771; claim retains
exactly the source quantifiers, positivity condition and natural arithmetic.
Declaration judgement:
claim: definition; escape_witness: none.
result: proof_shape: content; escape_witness: HannaA365771.M_mod.
The division-by-five induction in that proposition lies on the result's live path.
-/

import D5.S1.Recurrence.Residue.HannaA365771

set_option autoImplicit false

namespace D5.S1.Recurrence.Residue.HannaA365771Two

open D5.S1.Recurrence.Residue.HannaA365771

/-- Hanna's second conjecture, with m ranging over positive sums of distinct powers of five. -/
def claim : Prop := ∀ m : ℕ, 0 < m → InA033042 m → a (5 * m + 1) % 5 = 2

theorem result : claim := by
  intro m hm hd
  have hi : InA033042 (5 * m + 1) := by
    apply (digits_step (5 * m + 1) (by omega)).mpr
    exact ⟨by omega, by simpa only [show (5 * m + 1) / 5 = m by omega] using hd⟩
  simpa [hi, show (5 * m + 1) % 5 = 1 by omega] using residue_classification (5 * m + 1) (by omega)

end D5.S1.Recurrence.Residue.HannaA365771Two
