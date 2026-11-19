import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete native saturation existence equivalence. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b q : ℕ) (_hq : 0 < q),
    (∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin (3 * q)) (Fin (2 * q)) ℂ),
      (∑ r, kronecker (M r) (N r))ᴴ *
        (∑ r, kronecker (M r) (N r)) =
          (1 : Matrix (Fin b × Fin (2 * q)) (Fin b × Fin (2 * q)) ℂ)) ↔
      R.readout () () (2 * b) (3 * a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0 0 1 (by omega)).mp
    ((NativeSaturation.native_saturation_iff 0 0 1 (by omega)).mpr (by omega))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have : ¬ ((1 : ℕ) ≤ 0) := by omega
  exact this (Eq.mp he (Nat.zero_le 0))

def family : Registration arena (type_of% @NativeSaturation.native_saturation_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NativeSaturation.native_saturation_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@NativeSaturation.native_saturation_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation.native_saturation_iff.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation.family
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation
