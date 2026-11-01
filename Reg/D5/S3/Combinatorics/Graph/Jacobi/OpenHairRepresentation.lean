import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation
import Reg.Support.DependentFamily

/-! Source-bound observation of the actual rotor-fixed flag count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation

open _root_.D5.S3.Combinatorics.Graph.Jacobi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := HairTree Color
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ t => t.model.leafCount) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : HairTree Color, R.readout () () t = t.leafCount

def originalStatement : Prop := ∀ t : HairTree Color, t.model.leafCount = t.leafCount

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (.leaf .red)
  exact Nat.zero_ne_one hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), .leaf .red, .node (.leaf .red) (.leaf .red), ?_⟩
  change (HairTree.leaf Color.red).model.leafCount ≠
    (HairTree.node (.leaf Color.red) (.leaf Color.red)).model.leafCount
  rw [OpenHair.model_leafCount, OpenHair.model_leafCount]
  decide

noncomputable def source_registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨OpenHair.model_leafCount, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def model_leafCount_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Graph.Jacobi.OpenHair.model_leafCount)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation.leafCount_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t.model.leafCount) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Graph.Jacobi.OpenHairRepresentation
