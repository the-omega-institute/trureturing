import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

/-! Source-bound audit of the native scalar-Gram dimension obstruction. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

noncomputable section

open _root_.Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ), 0 < c → 2 * a < b →
    ∀ (lam : ℝ), 0 < lam →
      (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
        (lam : ℂ) • 1 → r.readout () () (3 * c) d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN (by norm_num) (by norm_num) 1 (by norm_num) (by simpa using native_gram)

def source_registration : Registration arena (type_of% @RestrictedFlatSpectrum.obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@RestrictedFlatSpectrum.obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@RestrictedFlatSpectrum.obstruction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum.source_registration
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum
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
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum
