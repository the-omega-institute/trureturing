import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Powers.CommonWitnessCompactness
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Powers.CommonWitnessCompactness
open _root_.D5.S1.Words.Powers.CommonWitnessCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

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
  Law R := ∀ {A : Type u} (G : Set (List A × List A)),
    R.readout () A G ↔
      ∀ T : Set (List A × List A), T ⊆ G → T.Finite → CommonWitness T

theorem actual_law : arena.{u}.Law actual := @commonWitness_iff_finite.{u}

theorem empty_witness (A : Type u) : CommonWitness (∅ : Set (List A × List A)) := by
  refine ⟨[], Or.inl ?_⟩
  intro p hp
  exact hp.elim

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have bad := (h (A := ULift.{u} Empty) ∅).mpr
    ((commonWitness_iff_finite ∅).mp (empty_witness _))
  exact bad

theorem no_witness (a : ULift.{u} Unit) :
    ¬ CommonWitness ({([], [a])} : Set (List (ULift.{u} Unit) × List (ULift.{u} Unit))) := by
  rintro ⟨z, h | h⟩
  · have e := h ([], [a]) (by simp)
    change [] ++ z = z ++ [a] at e
    have l := congrArg List.length e
    simp only [List.length_append, List.length_nil, List.length_cons] at l
    omega
  · have e := h ([], [a]) (by simp)
    change z ++ [] = [a] ++ z at e
    have l := congrArg List.length e
    simp only [List.length_append, List.length_nil, List.length_cons] at l
    omega

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, ∅, {([], [ULift.up ()])}, ?_⟩
  intro equal
  exact no_witness (ULift.up ()) (equal ▸ empty_witness _)

def source_registration : Registration arena.{u}
    (type_of% @commonWitness_iff_finite.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@commonWitness_iff_finite.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Words.Powers.CommonWitnessCompactness.unit
  realizationName := `Reg.D5.S1.Words.Powers.CommonWitnessCompactness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ G => CommonWitness G) (fun e => nomatch e))
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
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S1.Words.Powers.CommonWitnessCompactness
