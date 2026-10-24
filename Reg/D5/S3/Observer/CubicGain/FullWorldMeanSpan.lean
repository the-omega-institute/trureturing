import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.FullWorldMeanSpan
import Reg.Support.SingleDependentReadout

/-! The unrestricted native mean map, varied over the complete original world family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.FullWorldMeanSpan
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.FullWorldMeanSpan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => OriginalWorld) (fun _ => Fin 17 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => fullWorldMean) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := affineSpan ℝ (R.readout () () '' {W : OriginalWorld | FullWorld W}) = ⊤

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle : affineSpan ℝ (rejected.readout () () '' {W : OriginalWorld | FullWorld W}) ≤
      affineSpan ℝ ({0} : Set (Fin 17 → ℝ)) := by
    apply affineSpan_mono
    rintro _ ⟨W,hW,rfl⟩
    simp [rejected,realize]
  have hm : (Pi.single 0 1 : Fin 17 → ℝ) ∈ affineSpan ℝ ({0} : Set (Fin 17 → ℝ)) := by
    apply hle
    change _ ∈ affineSpan ℝ (rejected.readout () () '' {W : OriginalWorld | FullWorld W})
    rw [h]
    trivial
  have he : (Pi.single 0 1 : Fin 17 → ℝ) = 0 :=
    by simpa only [AffineSubspace.mem_affineSpan_singleton] using hm
  have h0 := congrFun he 0
  norm_num at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1/4,1/8,0,![1,0,0,0]), (1/4,1/8,1,![1,0,0,0]), ?_⟩
  intro h
  have h0 := congrFun h 0
  norm_num [actual,realize,fullWorldMean,meanCoordinates] at h0

def source_registration : Registration arena (type_of% @full_world_mean_span) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_world_mean_span,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@full_world_mean_span) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.FullWorldMeanSpan.full_world_mean_span.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.FullWorldMeanSpan.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => fullWorldMean) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.FullWorldMeanSpan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","arg","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
end Reg.D5.S3.Observer.CubicGain.FullWorldMeanSpan
