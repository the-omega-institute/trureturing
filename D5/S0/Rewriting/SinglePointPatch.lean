/- GID: D5/S0/Rewriting/SinglePointPatch
   generality: G
   mirror-B: D5/B/S0/Rewriting/SinglePointPatch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An update outside a finite record preserves its values and changes the rule. -/

import Mathlib.Data.Finset.Basic

namespace D5.S0.Rewriting.SinglePointPatch

/-- Replacing a rule's value outside a finite record preserves consistency with every recorded
value. If the replacement differs from the old value, the patched rule is genuinely new. -/
theorem update_outside_record_preserves_consistency
    {D Y : Type*} [DecidableEq D]
    (record : Finset D) (prescribed rule : D → Y) (a : D) (b : Y)
    (hRule : ∀ d, d ∈ record → rule d = prescribed d)
    (hOutside : a ∉ record) (hChanged : b ≠ rule a) :
    (∀ d, d ∈ record → Function.update rule a b d = prescribed d) ∧
      Function.update rule a b ≠ rule := by
  constructor
  · intro d hd
    rw [Function.update_of_ne]
    · exact hRule d hd
    · intro hda
      exact hOutside (hda ▸ hd)
  · exact Function.update_ne_self_iff.mpr hChanged

/-- The domains in the generic patch statement can be inhabited. -/
example : Nonempty (Fin 2 × Bool) := inferInstance

/-- Changing coordinate one of a two-coordinate constant-false rule preserves the observation at
coordinate zero and produces a distinct rule. -/
example :
    (∀ d, d ∈ ({0} : Finset (Fin 2)) →
      Function.update (fun _ : Fin 2 => false) 1 true d = false) ∧
      Function.update (fun _ : Fin 2 => false) 1 true ≠ (fun _ => false) := by
  apply update_outside_record_preserves_consistency
  · intro d hd
    simp at hd
    subst d
    rfl
  · decide
  · decide

end D5.S0.Rewriting.SinglePointPatch
