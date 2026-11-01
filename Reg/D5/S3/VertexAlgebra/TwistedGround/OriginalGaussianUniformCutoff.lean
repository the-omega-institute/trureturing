import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ R => traceWeightMass R) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ (N : ℕ) {r R : ℝ}, r ≤ R → 0 ≤ R → R < 1 →
    ‖weightedCutoff N r‖ ≤ A.readout () () R

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (r := 0) (R := 0) le_rfl le_rfl (by norm_num)
  norm_num [rejected, realize, weightedCutoff] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  have hz : traceWeightMass 0 = 0 := by
    simp [traceWeightMass, traceWeightBound]
  have hp : 0 < traceWeightMass (1 / 2) := by
    apply (traceWeightBound_summable (R := 1 / 2) (by norm_num) (by norm_num)).tsum_pos (i := 0)
    · intro n
      unfold traceWeightBound
      positivity
    · norm_num [traceWeightBound] <;> positivity
  change traceWeightMass 0 ≠ traceWeightMass (1 / 2)
  rw [hz]
  exact hp.ne

def evidence : Registration arena (type_of% @weightedCutoff_norm_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedCutoff_norm_le, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weightedCutoff_norm_le) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ R => traceWeightMass R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
