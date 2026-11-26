import D5.S1.Words.Powers.CommonWitnessCompactness
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

namespace Reg.D5.S1.Words.Powers.CommonWitnessCompactness

open _root_.D5.S1.Words.Powers.CommonWitnessCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Type u
  State A := Set (List A × List A)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ G => CommonWitness G) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (A : Type u) (G : Set (List A × List A)),
    R.readout () A G ↔
      ∀ T : Set (List A × List A), T ⊆ G → T.Finite → T.ncard ≤ 3 →
        CommonWitness T

private theorem empty_common (A : Type u) :
    CommonWitness (∅ : Set (List A × List A)) := by
  refine ⟨[], .inl ?_⟩
  intro p hp
  exact hp.elim

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (ULift.{u} Unit) ∅).mpr
    ((commonWitness_iff_three ∅).mp (empty_common _))

private theorem singleton_not_common :
    ¬ CommonWitness ({([], [ULift.up ()])} :
      Set (List (ULift.{u} Unit) × List (ULift.{u} Unit))) := by
  rintro ⟨z, hz | hz⟩
  · have heq := hz ([], [ULift.up ()]) (by simp)
    change [] ++ z = z ++ [ULift.up ()] at heq
    have hlen := congrArg List.length heq
    simp at hlen
  · have heq := hz ([], [ULift.up ()]) (by simp)
    change z ++ [] = [ULift.up ()] ++ z at heq
    have hlen := congrArg List.length heq
    simp at hlen

def family : Registration arena.{u} (type_of% (@commonWitness_iff_three.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@commonWitness_iff_three.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨ULift.{u} Unit, ∅, {([], [ULift.up ()])}, ?_⟩
    intro heq
    exact singleton_not_common (Eq.mp heq (empty_common _))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@commonWitness_iff_three.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Powers.CommonWitnessCompactness.commonWitness_iff_three.__information_unit
  realizationName := `Reg.D5.S1.Words.Powers.CommonWitnessCompactness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Powers.CommonWitnessCompactness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.Powers.CommonWitnessCompactness
