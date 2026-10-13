import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
import Reg.Support.DependentFamily

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw FourthSegmentLawRecovery.Length
open NativeConditionalControl.DepthLaw
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
abbrev signature : Signature where
  Params := unitInterval
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞ × ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r j =>
    (((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+1)},
     ((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+2)}))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f := ∀ (r : unitInterval) (j : ℕ),
    (f.readout () r j).1 = alphaMass r*(alphaMass r*betaMass r)^j ∧
    (f.readout () r j).2 = betaMass r^2*(alphaMass r*betaMass r)^j

theorem source_bridge : (type_of% (@p_kernel_atoms)) ↔ arena.Law actual := Iff.rfl

theorem rejects : ¬ arena.Law rejected := by
  intro h
  have hh := (h (1 : unitInterval) 0).1
  norm_num [rejected,realize,alphaMass,betaMass] at hh

def record : Registration arena (type_of% (@p_kernel_atoms)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨p_kernel_atoms,rejected,rejects⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejects⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(1 : unitInterval), (0 : ℕ), (1 : ℕ), ?_⟩
    intro he
    have hh := congrArg Prod.fst he
    change ((explicitStoppedWordLaw .p 1).map lengthProjection) {some (2*0+1)} =
      ((explicitStoppedWordLaw .p 1).map lengthProjection) {some (2*1+1)} at hh
    rw [(p_kernel_atoms 1 0).1,(p_kernel_atoms 1 1).1] at hh
    norm_num [alphaMass,betaMass] at hh

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@p_kernel_atoms) (Realization signature) (Type) Unit := {
  unitName := `FourthSegmentLawRecovery.p_kernel_atoms.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r j =>
    (((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+1)},
     ((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+2)}))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body","body","fn","arg","fn","arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false },
      { path := #["body","body","arg","fn","arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms record

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
