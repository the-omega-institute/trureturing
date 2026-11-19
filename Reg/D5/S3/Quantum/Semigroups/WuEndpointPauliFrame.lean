import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointPauliFrame

/-! Source-bound readouts for the Pauli overlap estimates. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

namespace FrameOverlap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : EuclideanSpace ℂ Mode),
    R.readout () () (‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j : Fin 4, ‖⟪u, (endpointU j).toEuclideanLin v⟫_ℂ‖ ^ 2)
      (2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @pauli_frame_overlap_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauli_frame_overlap_le_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pauli_frame_overlap_le_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.pauli_frame_overlap_le_two.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.FrameOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FrameOverlap

namespace TailOverlap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : EuclideanSpace ℂ Mode),
    R.readout () () (‖⟪u, endpointVolume.toEuclideanLin v⟫_ℂ‖ ^ 2 +
      ∑ j : Fin 4, ‖⟪u, (endpointTriple j).toEuclideanLin v⟫_ℂ‖ ^ 2)
      (2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% @pauli_tail_overlap_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauli_tail_overlap_le_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pauli_tail_overlap_le_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.pauli_tail_overlap_le_two.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame.TailOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailOverlap

end Reg.D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
