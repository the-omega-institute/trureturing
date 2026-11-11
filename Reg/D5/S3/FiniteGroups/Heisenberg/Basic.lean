import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Heisenberg.Basic
import Reg.Support.DependentFamily

/-! Cardinality is an actual varying observation on coefficient carriers. -/

namespace Reg.D5.S3.FiniteGroups.Heisenberg.Basic

open _root_.D5.S3.FiniteGroups
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := Type u
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def noAnchor : Empty → Unit → Type u := fun e => nomatch e

def actual : Realization signature.{u} := realize signature
  (fun _ _ R => Nat.card (HeisenbergGroup R)) noAnchor.{u}

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) noAnchor.{u}

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u}, R.readout () () A = Nat.card A ^ 3

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (A := ULift.{u} Unit)
  norm_num [rejected, realize] at hh

def family : Registration arena.{u} (type_of% (@HeisenbergGroup.card_eq.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@HeisenbergGroup.card_eq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),ULift.{u} Empty,ULift.{u} Unit,?_⟩
    norm_num [actual, realize, HeisenbergGroup.card_eq]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HeisenbergGroup.card_eq.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.HeisenbergGroup.card_eq.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Heisenberg.Basic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ R => Nat.card (HeisenbergGroup R)) noAnchor.{u})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Heisenberg.Basic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.Heisenberg.Basic
