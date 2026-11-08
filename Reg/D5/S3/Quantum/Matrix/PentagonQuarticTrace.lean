import D5.S3.Quantum.Matrix.PentagonQuarticTrace
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound equality, order and strict-order readouts of the quartic certificate. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.PentagonQuarticTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace
noncomputable section
universe u

namespace Sos

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Fin 5 → Mat n),
    (∀ i, (A i).IsHermitian) → (∀ i, A i * A (i + 2) = 0) →
    F.readout () () (8 * (∑ i, reTrace (A i ^ 4)) - reTrace ((∑ i, A i)^4)) ((∑ i, hsSq (remainder A i - remainder A (i + 1))) +
      (1/2 : ℝ) * (∑ i, hsSq (remainder A i - (2 : ℝ) • remainder A (i + 1) +
        (2 : ℝ) • remainder A (i + 2) - remainder A (i + 3))) +
      (3/4 : ℝ) * (∑ i, hsSq (commutator A i)) +
      (5/8 : ℝ) * (∑ i, hsSq (commutator A i - commutator A (i + 1))))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 0)
    (by intro i; simp) (by intro i; simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% (@pentagon_quartic_sos.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pentagon_quartic_sos.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pentagon_quartic_sos.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Sos.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Sos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PentagonQuarticTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sos

namespace Bound

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Fin 5 → Mat n),
    (∀ i, (A i).IsHermitian) → (∀ i, A i * A (i + 2) = 0) →
    F.readout () () (reTrace ((∑ i, A i)^4)) (8 * ∑ i, reTrace (A i ^ 4))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 0)
    (by intro i; simp) (by intro i; simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% (@pentagon_quartic_trace_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pentagon_quartic_trace_le.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pentagon_quartic_trace_le.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Bound.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PentagonQuarticTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bound

namespace Sharp

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (c : ℝ), c < 8 →
    ∃ A : Fin 5 → Mat (Fin 1), (∀ i, (A i).IsHermitian) ∧
      (∀ i, A i * A (i + 2) = 0) ∧
      F.readout () () (c * (∑ i, reTrace (A i ^ 4))) (reTrace ((∑ i, A i)^4))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, _, _, hf⟩ := h 0 (by norm_num)
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 1
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@constant_eight_sharp)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@constant_eight_sharp, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@constant_eight_sharp) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Sharp.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace.Sharp.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PentagonQuarticTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sharp

end
end Reg.D5.S3.Quantum.Matrix.PentagonQuarticTrace
