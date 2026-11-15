import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the native scalar-Gram dimension obstruction. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

noncomputable section

private def nativeM (r : Fin 3) : Matrix (Fin 1) (Fin 3) ℂ :=
  fun _ j => if r = j then 1 else 0

private def nativeN (r : Fin 3) : Matrix (Fin 3) (Fin 1) ℂ :=
  fun i _ => if i = r then 1 else 0

private theorem native_gram :
    (QuantumMaxFlowBound.flow nativeM nativeN)ᴴ *
      QuantumMaxFlowBound.flow nativeM nativeN = (1 : ℂ) • 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [QuantumMaxFlowBound.flow, nativeM, nativeN, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ), 0 < c → 5 * a < 2 * b →
    ∀ (lam : ℝ), 0 < lam →
      (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
        (lam : ℂ) • 1 → r.readout () () (3 * c) d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN (by norm_num) (by norm_num) 1 (by norm_num) (by simpa using native_gram)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have : ¬ ((1 : ℕ) ≤ 0) := by omega
  exact this (Eq.mp he (Nat.zero_le 0))

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.obstruction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
