import D5.S3.Combinatorics.Graph.StarForming.Amplification
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.Amplification

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.Amplification
universe u

abbrev Parameters := Type u

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset (p × Fin 10)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (I : Type u), Finset (I × Fin 10) → ℕ :=
  fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (I : Type u), Finset (I × Fin 10) :=
  fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature observation noAnchor

def bad : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) noAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I],
    r.readout () I (Finset.univ.product selected) = 6 * Fintype.card I

private theorem bad_law : ¬ arena.{u}.Law bad.{u} := by
  intro h
  have hh := h (I := ULift.{u} Unit)
  change 0 = 6 * Fintype.card (ULift.{u} Unit) at hh
  simp at hh

abbrev SourceClaim : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I],
    ((Finset.univ : Finset I).product selected).card = 6 * Fintype.card I

def family : Registration arena.{u} SourceClaim.{u} where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := by
    refine ⟨?_,bad,bad_law⟩
    intro I fi ei
    exact chosen_card
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit,∅,{(ULift.up (),0)},?_⟩
    change (∅ : Finset (ULift.{u} Unit × Fin 10)).card ≠
      ({(ULift.up (),0)} : Finset (ULift.{u} Unit × Fin 10)).card
    simp

noncomputable def chosenCardRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.Amplification.chosen_card.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.Amplification.chosen_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.Amplification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.Amplification
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.Amplification
