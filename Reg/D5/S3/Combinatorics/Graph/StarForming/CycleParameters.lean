import D5.S3.Combinatorics.Graph.StarForming.CycleParameters
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.CycleParameters
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.CycleParameters

abbrev signature : Signature where
  Params := ℕ
  State p := Finset (Fin p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (p : ℕ), Finset (Fin p) → ℕ := fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (p : ℕ), Finset (Fin p) := fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ _ _ => 1) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, r.readout () n (selection n)=2*n/3

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0
  change 1=2*0/3 at hh
  norm_num at hh

abbrev SourceClaim : Prop := ∀ n : ℕ, (selection n).card=2*n/3

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun n => selection_card n,bad,bad_law⟩
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
    refine ⟨1,∅,{(0 : Fin 1)},?_⟩
    change (∅ : Finset (Fin 1)).card ≠ ({(0 : Fin 1)} : Finset (Fin 1)).card
    simp

noncomputable def selectionCardRegistration :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.CycleParameters.selection_card)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.CycleParameters.selection_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.CycleParameters.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.CycleParameters
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.CycleParameters
