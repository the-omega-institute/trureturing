import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

/-! A source-bound audit of the unrestricted native rectangular consequence. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
open Matrix

noncomputable section

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (lambda : ℝ) (_hlambda : 0 < lambda) (_hab : 3 * a < 2 * b)
    (_hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) =
        (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)),
    R.readout () () (2 * c) d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN 1 (by norm_num) (by norm_num)
    (by simpa [QuantumMaxFlowBound.flow] using native_gram)

def family : Registration arena (type_of% @NativeRectangularBound.bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NativeRectangularBound.bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@NativeRectangularBound.bound) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound.bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound.family
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
