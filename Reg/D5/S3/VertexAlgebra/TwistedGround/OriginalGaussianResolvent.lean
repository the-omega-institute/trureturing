import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
import Reg.Support.SingleDependentReadout

/-! The scalar readout varies its actual real parameter while retaining the
full absolute-convergence and signed-operator statement. -/

noncomputable section
open scoped BigOperators
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ r => ((r / (4 * (1 - r)) : ℝ) : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    Summable (fun n : ℕ => ‖weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n‖) ∧
    (∑' n : ℕ, weightedSource r hr.le hr1 n *
      oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr.le hr1) n) =
        R.readout () () r

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := (bilinear_opposite_resolvent_scalar (r := 1 / 2) (by norm_num)
    (by norm_num)).2
  have hb := (h (r := 1 / 2) (by norm_num) (by norm_num)).2
  rw [ha] at hb
  norm_num [rejected, realize] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (type_of% @bilinear_opposite_resolvent_scalar) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinear_opposite_resolvent_scalar, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinear_opposite_resolvent_scalar) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.scalarUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ r => ((r / (4 * (1 - r)) : ℝ) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
