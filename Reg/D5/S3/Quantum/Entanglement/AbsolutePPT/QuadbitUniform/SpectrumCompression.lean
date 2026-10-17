import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound.SharedSpectral
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
  Law O := ∀ (N j : ℕ) (_hN : 67 ≤ N), O.readout () N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N]
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
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression.positions_literal.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"]
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
  Law O := ∀ (N j : ℕ) (_hN : 67 ≤ N) (_hj : 6 ≤ j) (_hj' : j ≤ N-10), StrictMono (O.readout () N j)
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
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression.positions_strict.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"]
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
  norm_num [rejected, realize] at hb
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, target]
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
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression.target_nonneg.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end target_nonneg

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
