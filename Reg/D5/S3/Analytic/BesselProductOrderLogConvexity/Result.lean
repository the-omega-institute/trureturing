import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.BesselProductOrderLogConvexity.Result
import Reg.Support.DependentFamily

/-! Source-bound audit of the nonintegrality of integer translates of one half. -/

namespace Reg.D5.S3.Analytic.BesselProductOrderLogConvexity.Result

open _root_.D5.S3.Analytic.BesselProductOrderLogConvexity.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => (k : ℝ) + 1 / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k n : ℤ, R.readout () () k ≠ (n : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change ((0 : ℤ) : ℝ) + 1 / 2 ≠ ((1 : ℤ) : ℝ) + 1 / 2
  norm_num

def source_registration : Registration arena (type_of% @half_noninteger) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@half_noninteger, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@half_noninteger) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.BesselProductOrderLogConvexity.Result.unit
  realizationName :=
    `Reg.D5.S3.Analytic.BesselProductOrderLogConvexity.Result.source_registration
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
    (realize signature (fun _ _ k => (k : ℝ) + 1 / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselProductOrderLogConvexity.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
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
end Reg.D5.S3.Analytic.BesselProductOrderLogConvexity.Result
