import D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
open scoped BigOperators
namespace Reg.D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
open _root_.D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => (ℕ → ℝ) → (ℕ → ℝ) → ℝ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => chartDistanceSq n) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, let observed := R.readout () () n; StabilityLaw n observed

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := (h 1).1 (fun _ => 1) (fun _ => 4) (by intros; norm_num)
  have hf := hn.mp rfl 0 (by decide)
  norm_num at hf

private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  intro h
  have he := congrFun (congrFun h (fun _ => 1)) (fun _ => 4)
  change chartDistanceSq 0 (fun _ => 1) (fun _ => 4) =
    chartDistanceSq 1 (fun _ => 1) (fun _ => 4) at he
  have hz : chartDistanceSq 0 (fun _ => 1) (fun _ => 4) = 0 := by simp [chartDistanceSq,SqNorm]
  have hn := (weighted_stability 1).1 (fun _ => 1) (fun _ => 4) (by intros; norm_num)
  have hf := hn.mp (he.symm.trans hz) 0 (by decide)
  norm_num at hf

noncomputable def family : Registration arena (type_of% @weighted_stability) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_stability,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, actual_dependence⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@weighted_stability) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability.weighted_stability.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability.family
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
      owner := `D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
      definition := none
      coordinates := #[]
      readouts := #[{
        path := #["body","value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
