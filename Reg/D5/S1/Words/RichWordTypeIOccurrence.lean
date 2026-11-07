import D5.S1.Words.RichWordTypeIOccurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.RichWordTypeIOccurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff

abbrev signature : Signature where
  Params := Word
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s q => Occ (sentinel s) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Word) (q : ℕ),
    R.readout () s q ↔ ∃ a, q = boundary a ∧ Occ s a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h [] 0).mpr ⟨0, by decide, by decide⟩

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨[], 0, 1, ?_⟩
    change Occ (sentinel []) 0 ≠ Occ (sentinel []) 1
    intro h
    exact (by decide : ¬ Occ (sentinel []) 1) (Eq.mp h (by decide))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.RichWordTypeIOccurrence, definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.RichWordTypeIOccurrence.ordinary_occurrence_iff
