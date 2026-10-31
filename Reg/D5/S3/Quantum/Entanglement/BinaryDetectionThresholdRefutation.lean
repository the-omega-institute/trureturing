import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the binary equality reconstruction lemma. -/

namespace Reg.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation

open _root_.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := (Bool → Bool → ℝ) × (Bool → Bool → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p.1 = p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f g : Bool → Bool → ℝ) (ma mb : Bool),
    (∑ a : Bool, ∑ b : Bool, f a b) = (∑ a : Bool, ∑ b : Bool, g a b) →
    (∑ b : Bool, f ma b) = (∑ b : Bool, g ma b) →
    (∑ a : Bool, f a mb) = (∑ a : Bool, g a mb) →
    f ma mb = g ma mb →
    R.readout () () (f, g)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (fun _ _ => 0) (fun _ _ => 0) false false (by rfl) (by rfl) (by rfl) (by rfl)
  exact hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ _ => 0, fun _ _ => 0), (fun _ _ => 0, fun _ _ => 1), ?_⟩
  intro h
  have hfun : (fun _ _ : Bool => 0) = (fun _ _ : Bool => 1) := by
    have htrue : (fun _ _ : Bool => 0) = (fun _ _ : Bool => 0) := rfl
    rw [h] at htrue
    exact htrue
  have hbad := congrFun (congrFun hfun false) false
  norm_num at hbad

def source_registration : Registration arena (type_of% @binary_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨binary_eq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.binary_eq)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.1 = p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation
