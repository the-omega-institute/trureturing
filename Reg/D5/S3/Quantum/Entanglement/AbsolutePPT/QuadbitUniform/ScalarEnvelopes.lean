-- UNCOMPILED dimension-alignment changes; existing registration proofs are preserved.
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix
noncomputable section

namespace positions_literal
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Fin 16 → ℕ)
def actual : Realization signature :=
  realize signature (fun _ N j => positions N j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ => (0 : ℕ))) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (_hN : 56 ≤ N), O.readout () N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 67 6 (by norm_num)) 0
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨67, 0, 1, ?_⟩
  change positions 67 0 ≠ positions 67 1
  intro h
  have he := congrFun h 5
  norm_num [positions] at he
def family : Registration arena (type_of% (@positions_literal)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positions_literal, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positions_literal) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.positions_literal.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.positions_literal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N j => positions N j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positions_literal

namespace positions_strict
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Fin 16 → ℕ)
def actual : Realization signature :=
  realize signature (fun _ N j => positions N j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ => (0 : ℕ))) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (_hN : 56 ≤ N) (_hj : 6 ≤ j) (_hj' : j ≤ N-10), StrictMono (O.readout () N j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 6 (by norm_num) (by norm_num) (by norm_num)
    (show (0 : Fin 16) < 1 by norm_num)
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨67, 0, 1, ?_⟩
  change positions 67 0 ≠ positions 67 1
  intro h
  have he := congrFun h 5
  norm_num [positions] at he
def family : Registration arena (type_of% (@positions_strict)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positions_strict, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positions_strict) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.positions_strict.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.positions_strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N j => positions N j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positions_strict

namespace target_nonneg
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => target N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ), 0 ≤ O.readout () () N
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (0 : ℝ) ≤ -1 at hb
  norm_num at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change target 1 ≠ target 2
  norm_num [target]
def family : Registration arena (type_of% (@target_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@target_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@target_nonneg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.target_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.target_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => target N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end target_nonneg


namespace boundary_envelope_le_common
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => boundaryEnvelope N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℝ) (_hN : 67 ≤ N), O.readout () () N ≤ commonEnvelope N
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 (by norm_num)
  norm_num [rejected, realize, commonEnvelope] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, boundaryEnvelope]
def family : Registration arena (type_of% (@boundary_envelope_le_common)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_envelope_le_common, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_envelope_le_common) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.boundary_envelope_le_common.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.boundary_envelope_le_common.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => boundaryEnvelope N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end boundary_envelope_le_common

namespace middle_envelopeOne_le_common
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => middleEnvelope₁ N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℝ) (_hN : 56 ≤ N), O.readout () () N ≤ commonEnvelope N
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 (by norm_num)
  norm_num [rejected, realize, commonEnvelope] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, middleEnvelope₁]
def family : Registration arena (type_of% (@middle_envelope₁_le_common)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@middle_envelope₁_le_common, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@middle_envelope₁_le_common) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.middle_envelope₁_le_common.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.middle_envelopeOne_le_common.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => middleEnvelope₁ N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end middle_envelopeOne_le_common

namespace middle_envelopeTwo_le_common
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => middleEnvelope₂ N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℝ) (_hN : 67 ≤ N), O.readout () () N ≤ commonEnvelope N
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 (by norm_num)
  norm_num [rejected, realize, commonEnvelope] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, middleEnvelope₂]
def family : Registration arena (type_of% (@middle_envelope₂_le_common)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@middle_envelope₂_le_common, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@middle_envelope₂_le_common) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.middle_envelope₂_le_common.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.middle_envelopeTwo_le_common.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => middleEnvelope₂ N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end middle_envelopeTwo_le_common

namespace common_le_integer_bulk
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => commonEnvelope (N : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (_hN : 56 ≤ N), O.readout () () N ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 (by norm_num)
  norm_num [rejected, realize, bulkValue, bulkIndex] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, commonEnvelope]
def family : Registration arena (type_of% (@common_le_integer_bulk)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_le_integer_bulk, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_le_integer_bulk) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.common_le_integer_bulk.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.common_le_integer_bulk.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => commonEnvelope (N : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end common_le_integer_bulk

namespace bulk_integer_maximum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ N j => bulkValue (N : ℝ) (j : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N j : ℕ) (_hN : 56 ≤ N), O.readout () N j ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 67 0 (by norm_num)
  norm_num [rejected, realize, bulkValue, bulkIndex] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  norm_num [actual, realize, bulkValue]
def family : Registration arena (type_of% (@bulk_integer_maximum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bulk_integer_maximum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bulk_integer_maximum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound.bulk_integer_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes.bulk_integer_maximum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N j => bulkValue (N : ℝ) (j : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end bulk_integer_maximum

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
