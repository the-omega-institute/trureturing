import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => 1 / (4 * (1 - r))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ r => 1 / (4 * (1 - r)) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law A := ∀ {r : ℝ}, 0 < r → r < 1 →
    HasDerivAt (fun t : ℝ => gaussianLogDet (Real.sqrt t : ℂ))
      ((deriv F r / F r - A.readout () () r : ℝ) : ℂ) r

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := gaussianLogDet_hasDerivAt_period (r := 1 / 2) (by norm_num) (by norm_num)
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have he := ha.unique hb
  change ((deriv F (1 / 2) / F (1 / 2) - 1 / (4 * (1 - 1 / 2)) : ℝ) : ℂ) =
    ((deriv F (1 / 2) / F (1 / 2) - (1 / (4 * (1 - 1 / 2)) + 1) : ℝ) : ℂ) at he
  have hh := Complex.ofReal_injective he
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1 / 4, 1 / 2, ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (type_of% @gaussianLogDet_hasDerivAt_period) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gaussianLogDet_hasDerivAt_period, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussianLogDet_hasDerivAt_period) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => 1 / (4 * (1 - r))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
