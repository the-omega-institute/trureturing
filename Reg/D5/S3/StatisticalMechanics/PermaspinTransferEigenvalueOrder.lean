import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
import Reg.Support.DependentFamily

/-! Source-bound audit of the explicit eigenvalue in the transfer-matrix ordering. -/

namespace Reg.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder

open _root_.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the squared-difference eigenvalue as the second parameter varies. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c d => c * (1 - d) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ c d => largestRoot c d + 1) (fun e => nomatch e)

/-- Retain root existence, boundedness, and the complete maximum equality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ c d : ℝ, 0 < c → 0 < d →
    {x : ℝ | (dukesCubic c d).eval x = 0}.Nonempty ∧
    BddAbove {x : ℝ | (dukesCubic c d).eval x = 0} ∧
    max (max (largestRoot c d) (r.readout () c d)) (c * (1 - d ^ 2)) =
      largestRoot c d

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 1 (by norm_num) (by norm_num)).2.2
  change max (max (largestRoot 1 1) (largestRoot 1 1 + 1))
    (1 * (1 - 1 ^ 2)) = largestRoot 1 1 at hbad
  have hle : largestRoot 1 1 + 1 ≤ largestRoot 1 1 := calc
    _ ≤ max (largestRoot 1 1) (largestRoot 1 1 + 1) := le_max_right _ _
    _ ≤ max (max (largestRoot 1 1) (largestRoot 1 1 + 1))
        (1 * (1 - 1 ^ 2)) := le_max_left _ _
    _ = largestRoot 1 1 := hbad
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change (1 : ℝ) * (1 - 1) ^ 2 ≠ 1 * (1 - 2) ^ 2
  norm_num

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ c d => c * (1 - d) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
    definition := some {
      owner := `D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
      name := `D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg",
        "fn", "arg", "fn", "arg", "arg"]
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
end Reg.D5.S3.StatisticalMechanics.PermaspinTransferEigenvalueOrder
