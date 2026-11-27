import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observation of a sparse step as a function of the input vector. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseData
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer


noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => State → ℤ) (fun _ => State → ℤ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ v => step v)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ v s => step v s + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (v : State → ℤ), R.readout () () v = Matrix.vecMul v T

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := congrFun (h (fun _ => 0)) 0
  have right := congrFun (step_correct (fun _ => 0)) 0
  change step (fun _ => 0) 0 + 1 = _ at wrong
  change step (fun _ => 0) 0 = _ at right
  omega

def family : Registration arena (type_of% @step_correct) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨step_correct, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro equal
    have entry := congrFun equal 0
    exact (by decide +kernel : step (fun _ => 0) 0 ≠ step (fun _ => 1) 0) entry

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@step_correct) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Sparse.step_correct.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
