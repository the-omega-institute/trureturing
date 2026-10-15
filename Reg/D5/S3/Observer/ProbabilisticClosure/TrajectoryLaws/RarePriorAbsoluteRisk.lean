import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeFullResidual RarePriorAbsoluteRisk
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open MeasureTheory
open scoped ENNReal

abbrev projectionSignature : Signature where
  Params := ActivePhase
  State s := Measure (ValidTail s) × Measure (ValidTail s)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature := realize projectionSignature
  (fun _ _ PQ => measurableTotalVariation (PQ.1.map Subtype.val) (PQ.2.map Subtype.val))
  (fun e => nomatch e)
def projectionArena : Arena where
  signature := projectionSignature
  Law R := ∀ s (P Q : Measure (ValidTail s)),
    R.readout () s (P,Q) = measurableTotalVariation P Q

theorem projectionBridge : (type_of% (@subtype_tv)) ↔
    projectionArena.Law projectionActual := by
  constructor <;> intro h s P Q <;> exact h s P Q

theorem projectionActualLaw : projectionArena.Law projectionActual :=
  projectionBridge.mp (@subtype_tv)


universe u

structure CommonParameters where
  X : Type u
  m : MeasurableSpace X
  P : @Measure X m
  C : @Measure X m

instance (p : CommonParameters) : MeasurableSpace p.X := p.m

abbrev commonSignature : Signature where
  Params := CommonParameters.{u}
  State p := Measure p.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def commonActual : Realization commonSignature.{u} := realize commonSignature.{u}
  (fun _ p Q => measurableTotalVariation p.P Q) (fun e => nomatch e)

def commonRejected : Realization commonSignature.{u} := realize commonSignature.{u}
  (fun _ _ _ => 1) (fun e => nomatch e)

def commonArena : Arena where
  signature := commonSignature.{u}
  Law f := ∀ (p : CommonParameters.{u}) (Q : Measure p.X),
    IsProbabilityMeasure p.P → IsProbabilityMeasure Q → IsFiniteMeasure p.C →
    p.C ≤ p.P → p.C ≤ Q → f.readout () p Q ≤ 1 - p.C Set.univ

theorem commonBridge : (type_of% (@common_measure_tv.{u})) ↔
    commonArena.{u}.Law commonActual.{u} := by
  constructor
  · intro h p Q hP hQ hC hCP hCQ
    letI := hP
    letI := hQ
    letI := hC
    exact h p.P Q p.C hCP hCQ
  · intro h X m P Q C hP hQ hC hCP hCQ
    exact h ⟨X,m,P,C⟩ Q hP hQ hC hCP hCQ

def commonWitness : CommonParameters.{u} :=
  { X := ULift.{u} Bool, m := ⊤,
    P := Measure.dirac ⟨false⟩, C := Measure.dirac ⟨false⟩ }

theorem commonRejects : ¬ commonArena.{u}.Law commonRejected.{u} := by
  intro h
  have hP : IsProbabilityMeasure commonWitness.{u}.P :=
    ⟨Measure.dirac_apply_of_mem (Set.mem_univ _)⟩
  have hC : IsFiniteMeasure commonWitness.{u}.C := by
    change IsFiniteMeasure commonWitness.{u}.P
    letI := hP
    infer_instance
  have hh := h commonWitness.{u} commonWitness.{u}.P hP hP hC le_rfl le_rfl
  change (1 : ℝ≥0∞) ≤ 1 -
    (@Measure.dirac (ULift.{u} Bool) ⊤ ⟨false⟩) Set.univ at hh
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _),tsub_self] at hh
  norm_num at hh

def commonRecord : Registration commonArena.{u} (type_of% (@common_measure_tv.{u})) where
  actual := commonActual.{u}
  bridge := commonBridge.{u}
  variation := ⟨commonBridge.{u}.mp (@common_measure_tv.{u}),
    commonRejected.{u}, commonRejects.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨commonRejected.{u},?_,rfl,commonRejects.{u}⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let p : CommonParameters.{u} := commonWitness.{u}
    let a : p.X := ⟨false⟩
    let b : p.X := ⟨true⟩
    refine ⟨p, Measure.dirac a, Measure.dirac b, ?_⟩
    have hzero : measurableTotalVariation p.P (Measure.dirac a) = 0 := by
      change measurableTotalVariation (Measure.dirac a) (Measure.dirac a) = 0
      simp only [measurableTotalVariation,tsub_self,max_self,iSup_const]
    have hone : 1 ≤ measurableTotalVariation p.P (Measure.dirac b) := by
      unfold measurableTotalVariation
      apply le_iSup_of_le (⟨{a}, by trivial⟩ : {E : Set p.X // MeasurableSet E})
      change 1 ≤ max ((Measure.dirac a) {a} - (Measure.dirac b) {a})
        ((Measure.dirac b) {a} - (Measure.dirac a) {a})
      rw [Measure.dirac_apply_of_mem (Set.mem_singleton a),
        Measure.dirac_apply' b (show MeasurableSet ({a} : Set p.X) from trivial)]
      have hba : b ∉ ({a} : Set p.X) := by
        intro h
        have he := congrArg ULift.down (Set.mem_singleton_iff.mp h)
        norm_num [a,b] at he
      rw [Set.indicator_of_notMem hba]
      norm_num
    intro he
    change measurableTotalVariation p.P (Measure.dirac a) =
      measurableTotalVariation p.P (Measure.dirac b) at he
    rw [← he,hzero] at hone
    exact (by norm_num at hone)

def commonRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_measure_tv.{u}) (Realization commonSignature.{u}) (Type) Unit := {
  unitName := `RarePriorAbsoluteRisk.common_measure_tv.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk.commonRecord
  realizationSource := none, generated := false
  arena := .source ⟨commonArena.{u}⟩, objectArena := .source ⟨commonArena.{u}⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source commonArena.{u} ⟨commonRecord.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize commonSignature.{u}
    (fun _ p Q => measurableTotalVariation p.P Q) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent, partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
    definition := none, coordinates := #[0,1,2,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 3, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }


end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
