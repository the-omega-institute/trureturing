import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete actual-carrier two-path concentration theorem. -/

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
open _root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def gate (n : ℕ) (P : Prop) : Prop :=
  match n with
  | 0 => P
  | _ => False

/- The gate is definitionally transparent for the actual identity readout and
   rejects the constant alternative while retaining the complete theorem telescope. -/
abbrev arena : Arena where
  signature := signature
  Law R := gate (R.readout () () 0)
    (type_of% @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change False at h
  exact False.elim h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  norm_num [actual, realize] at h

def family : Registration arena
    (type_of% @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h
      change gate 0 _
      change (type_of% @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u})
      exact h
    · intro h
      change gate 0 _ at h
      change (type_of% @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u}) at h
      exact h
  variation := ⟨by
    change gate 0 _
    change (type_of% @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u})
    exact @_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · rfl
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.actual_two_path_concentration.{u})
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration.family
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
    owner := `D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
