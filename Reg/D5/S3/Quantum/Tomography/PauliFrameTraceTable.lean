import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Tomography.PauliFrameTraceTable
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of Pauli frame completeness, tables and Jordan carriers. -/

namespace Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable
open LeanInformationAudit
open _root_.D5.S3.Quantum.Tomography.PauliFrameTraceTable
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

private abbrev equalitySignature (A : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => A) (fun _ => A → Prop)

private def equalityActual (A : Type) : Realization (equalitySignature A) :=
  realize (equalitySignature A) (fun _ _ x y => x = y) (fun e => nomatch e)

private def equalityBad (A : Type) : Realization (equalitySignature A) :=
  realize (equalitySignature A) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equality_dependence {A : Type} (a b : A) (hab : a ≠ b) :
    ObservationalDependence (equalitySignature A) (equalityActual A) := by
  intro i
  refine ⟨(), a, b, ?_⟩
  intro h
  exact hab ((Eq.mp (congrFun h a) rfl).symm)

namespace RealGenerated
abbrev signature := equalitySignature (Submodule ℝ Op)
def actual : Realization signature := equalityActual (Submodule ℝ Op)
def rejected : Realization signature := equalityBad (Submodule ℝ Op)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (generated (frame true)) realCarrier

private theorem rejected_law : ¬ arena.Law rejected := fun h => h

def family : Registration arena (type_of% (@real_generated)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@real_generated, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := equality_dependence (⊥ : Submodule ℝ Op) (⊤) bot_ne_top

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@real_generated) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.RealGenerated.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.RealGenerated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PauliFrameTraceTable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end RealGenerated

namespace ComplexGenerated
abbrev signature := equalitySignature (Submodule ℝ Op)
def actual : Realization signature := equalityActual (Submodule ℝ Op)
def rejected : Realization signature := equalityBad (Submodule ℝ Op)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (generated (frame false)) complexCarrier

private theorem rejected_law : ¬ arena.Law rejected := fun h => h

def family : Registration arena (type_of% (@complex_generated)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complex_generated, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := equality_dependence (⊥ : Submodule ℝ Op) (⊤) bot_ne_top

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@complex_generated) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.ComplexGenerated.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.ComplexGenerated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PauliFrameTraceTable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ComplexGenerated

namespace TraceTable
abbrev signature := equalitySignature (ℂ)
def actual : Realization signature := equalityActual (ℂ)
def rejected : Realization signature := equalityBad (ℂ)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : Bool) (i j : Fin 3) (st uv : Bits),
    R.readout () () (Matrix.trace (frame c i st * frame c j uv))
      (if i = j then (if st = uv then (1 : ℂ) else 0) else (1 / 4 : ℂ))

private theorem rejected_law : ¬ arena.Law rejected := fun h => h true 0 0 (0, 0) (0, 0)

def family : Registration arena (type_of% (@trace_table)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_table, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := equality_dependence (0 : ℂ) (1) zero_ne_one

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_table) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.TraceTable.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.TraceTable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PauliFrameTraceTable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TraceTable

namespace Dimensions
abbrev signature := equalitySignature ℕ
def actual : Realization signature := equalityActual ℕ
def rejected : Realization signature := equalityBad ℕ
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (Module.finrank ℝ (generated (frame true))) 10 ∧
    R.readout () () (Module.finrank ℝ (generated (frame false))) 16

private theorem rejected_law : ¬ arena.Law rejected := fun h => h.1

def family : Registration arena (type_of% (@generated_dimensions)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@generated_dimensions, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := equality_dependence (0 : ℕ) 1 (by decide)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@generated_dimensions) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.Dimensions.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.Dimensions.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PauliFrameTraceTable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Dimensions

namespace CompleteFrames
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Bool) (fun _ => Fin 3 → Bits → Op)
def actual : Realization signature := realize signature (fun _ _ c => frame c) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Bool, Complete (R.readout () () c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Complete (0 : Fin 3 → Bits → Op) := h true
  have hs := hz.2.2 0
  simpa using hs

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), true, false, ?_⟩
  intro h
  change frame true = frame false at h
  have he := congrArg (fun p : Fin 3 → Bits → Op => Module.finrank ℝ (generated p)) h
  rw [generated_dimensions.1, generated_dimensions.2] at he
  norm_num at he

def family : Registration arena (type_of% (@frame_complete)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@frame_complete, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@frame_complete) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.CompleteFrames.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable.CompleteFrames.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => frame c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PauliFrameTraceTable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end CompleteFrames

end

end Reg.D5.S3.Quantum.Tomography.PauliFrameTraceTable
