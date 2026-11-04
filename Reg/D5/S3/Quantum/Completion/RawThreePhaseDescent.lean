import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawThreePhaseDescent

/-! Full-telescope source registration of the retained C133-V prerequisite. -/

namespace Reg.D5.S3.Quantum.Completion.RawThreePhaseDescent
open _root_.D5.S3.Quantum.Completion.RawThreePhaseDescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ), RawBalance U c →
    (∀ u v, R.readout () () (c (U u) (U v)) (c u v)) ∧
    (∀ a b u v, c (a * U (U (U u))) (b * U (U (U v))) = c (a * u) (b * v)) ∧
    (∀ u z, c (U (U (U u))) z = c u z ∧ c z (U (U (U u))) = c z u)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : RawBalance (id : ULift.{u} Unit → ULift.{u} Unit)
      (fun _ _ => (0 : ℝ)) := ⟨rfl, fun _ _ => le_rfl, fun _ => rfl,
        fun _ _ _ _ => by norm_num⟩
  exact (h id (fun _ _ => 0) hz).1 1 1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena.{u} (type_of% @raw_marker_readouts.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@raw_marker_readouts.{u}, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@raw_marker_readouts.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawThreePhaseDescent.raw_marker_readouts.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawThreePhaseDescent.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.RawThreePhaseDescent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawThreePhaseDescent
