/- GID: D5/S3/QuantumContext/TwoTorsionPhaseIndices
   generality: I
   mirror-B: D5/B/S3/QuantumContext/TwoTorsionPhaseIndices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classify the nonzero two-torsion phase indices modulo twenty-four. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches for `ZMod 24`, two-torsion, and the three displayed pairs found no
     equivalent D5 declaration.
   * Pinned-Mathlib source search found `ZMod.neg_eq_self_iff`, which classifies the elements
     fixed by negation in every `ZMod n`, and `ZMod.natCast_zmod_val`, which identifies the
     surviving residue. Both are applied below.
   * The local `smart_search.sh` declaration-name queries returned no theorem for the full
     two-coordinate classification, so only the short product argument remains local.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.QuantumContext.TwoTorsionPhaseIndices

private theorem coordinate_two_torsion_iff (a : ZMod 24) :
    2 • a = 0 ↔ a = 0 ∨ a = 12 := by
  rw [two_nsmul, ← neg_eq_iff_add_eq_zero, ZMod.neg_eq_self_iff]
  apply or_congr Iff.rfl
  constructor
  · intro h
    have hval : a.val = 12 := by omega
    calc
      a = (a.val : ZMod 24) := (ZMod.natCast_zmod_val a).symm
      _ = 12 := congrArg (fun n : Nat => (n : ZMod 24)) hval
  · intro h
    subst a
    decide

/-- The nonzero indices killed by doubling in `(ZMod 24)^2` are exactly the three
nontrivial two-torsion pairs displayed in the source clause. -/
theorem nonzero_two_torsion_phase_indices (index : ZMod 24 × ZMod 24) :
    2 • index = 0 ∧ index ≠ 0 ↔
      index = (0, 12) ∨ index = (12, 0) ∨ index = (12, 12) := by
  constructor
  · rintro ⟨hTwo, hne⟩
    rcases index with ⟨a, b⟩
    have haTwo : 2 • a = 0 := by
      simpa using congrArg Prod.fst hTwo
    have hbTwo : 2 • b = 0 := by
      simpa using congrArg Prod.snd hTwo
    rcases (coordinate_two_torsion_iff a).1 haTwo with (rfl | rfl) <;>
      rcases (coordinate_two_torsion_iff b).1 hbTwo with (rfl | rfl)
    · exact (hne rfl).elim
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl) <;> decide

#print axioms nonzero_two_torsion_phase_indices

end D5.S3.QuantumContext.TwoTorsionPhaseIndices
