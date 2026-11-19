import D5.S3.Combinatorics.Graph.StarForming.ClosedCore
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.ClosedCore
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.ClosedCore

abbrev signature : Signature where
  Params := Unit
  State _ := Finset (Fin 20)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Unit), Finset (Fin 20) → ℕ := fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (_ : Unit), Finset (Fin 20) := fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ _ _ => 13) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ S : Finset (Fin 20), IsKIndependent graph 2 S →
    r.readout () () S + omitted S false ≤ 12

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hi : IsKIndependent graph 2 (∅ : Finset (Fin 20)) := by simp [IsKIndependent]
  have hh := h ∅ hi
  change 13 + omitted ∅ false ≤ 12 at hh
  omega

abbrev SourceClaim : Prop := ∀ S : Finset (Fin 20), IsKIndependent graph 2 S →
  S.card + omitted S false ≤ 12

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun S hS => omission_bound S hS,bad,bad_law⟩
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
    refine ⟨(),∅,{0},?_⟩
    change (∅ : Finset (Fin 20)).card ≠ ({0} : Finset (Fin 20)).card
    simp

noncomputable def omissionBoundRegistration :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.ClosedCore.omission_bound)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.ClosedCore.omission_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.ClosedCore.family
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
    owner := `D5.S3.Combinatorics.Graph.StarForming.ClosedCore
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.ClosedCore
