/- GID: D5/S1/Recurrence/Residue/HannaA365771Zero
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA365771Zero
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's congruence (3) holds outside the two base-five exceptional forms. -/

/-
admission_basis: open-problem-resolution (#18658; Proved)
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

namespace D5.S1.Recurrence.Residue.HannaA365771Zero

open D5.S1.Recurrence.Residue.HannaA365771

/-- Hanna's third conjecture; the exceptional multiplier may be zero. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → (¬ ∃ m : ℕ, InA033042 m ∧ (n = 5 * m ∨ n - 1 = 5 * m)) → a n % 5 = 0

theorem result : claim := by
  intro n hn hex
  have hi : ¬ InA033042 n := by
    intro hd
    obtain ⟨hr, hq⟩ := (digits_step n hn).mp hd
    apply hex
    refine ⟨n / 5, hq, ?_⟩
    omega
  simpa [hi] using residue_classification n hn

end D5.S1.Recurrence.Residue.HannaA365771Zero
