import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeSubQuorum
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open _root_.D5.S3.Combinatorics.Graph.Hypercube
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.HypercubeSubQuorum

abbrev paritySignature : Signature where
  Params := ℕ
  State n := Fin n → Bool
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def parityActual : Realization paritySignature :=
  realize paritySignature (fun _ _ x => cubeParity x) (fun e => nomatch e)

def parityRejected : Realization paritySignature :=
  realize paritySignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev parityArena : Arena where
  signature := paritySignature
  Law R := ∀ {n : ℕ} {x y : Fin n → Bool}, (hypercube n).Adj x y →
    R.readout false n x ≠ R.readout true n y

private theorem parity_rejected_law : ¬ parityArena.Law parityRejected := by
  intro h
  have ha : (hypercube 1).Adj (fun _ => false) (fun _ => true) := by
    change (Finset.univ.filter (fun _ : Fin 1 => (false : Bool) ≠ true)).card = 1
    simp
  exact h ha rfl

def parityIntervention (role : Bool) : Realization paritySignature :=
  realize paritySignature (fun j _ x => if j = role then false else cubeParity x)
    (fun e => nomatch e)

private theorem parity_intervention_rejected (role : Bool) :
    ¬ parityArena.Law (parityIntervention role) := by
  intro h
  have ha : (hypercube 1).Adj (fun _ => false) (fun _ => true) := by
    change (Finset.univ.filter (fun _ : Fin 1 => (false : Bool) ≠ true)).card = 1
    simp
  cases role
  · have hh := h ha.symm
    change (false : Bool) ≠ cubeParity (fun _ : Fin 1 => false) at hh
    simp [cubeParity] at hh
  · have hh := h ha
    change cubeParity (fun _ : Fin 1 => false) ≠ (false : Bool) at hh
    simp [cubeParity] at hh

def parityRecord : Registration parityArena (type_of% (@cubeParity_ne_of_adj)) where
  actual := parityActual
  bridge := Iff.rfl
  variation := ⟨@cubeParity_ne_of_adj, parityRejected, parity_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨parityIntervention i, ?_, rfl, parity_intervention_rejected i⟩
      intro j hji
      funext n x
      simp [parityIntervention, parityActual, realize, hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (fun _ : Fin 1 => false), (fun _ : Fin 1 => true), ?_⟩
    change cubeParity (fun _ : Fin 1 => false) ≠ cubeParity (fun _ : Fin 1 => true)
    simp [cubeParity, Fin.sum_univ_succ]

noncomputable def parity_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.HypercubeSubQuorum.cubeParity_ne_of_adj)
    (type_of% (realize paritySignature
      (fun _ _ x => cubeParity x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeSubQuorum.parity_information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeSubQuorum.parityRecord
  realizationSource := none
  generated := false
  arena := .source ⟨parityArena⟩
  objectArena := .source ⟨parityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source parityArena ⟨parityRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySignature
    (fun _ _ x => cubeParity x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeSubQuorum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms parityRecord
#print axioms parity_registration

end Reg.D5.S3.Combinatorics.Graph.HypercubeSubQuorum
