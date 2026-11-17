import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram
import Reg.Support.SingleDependentReadout

/-! A source-bound equality audit of the original-factor scalar-Gram construction. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _b : ℕ, ℕ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ)
    (_hleft : 2 * b ≤ 3 * a) (_hright : 3 * c ≤ 2 * d)
    (lam : ℝ) (_hlam : 0 < lam),
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      R.readout () ⟨b, c⟩
        ((∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)))
        ((lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, N, hfalse⟩ := h 0 0 0 0 (by omega) (by omega) 1 (by norm_num)
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = 0) =
    ((1 : Matrix _ _ ℂ) = 0) at he
  have hone : (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = 0 := Eq.mp he rfl
  have hentry := congrArg (fun A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ =>
    A (0, 0) (0, 0)) hone
  norm_num at hentry

def family : Registration arena (type_of% @NativeScalarGram.native_scalar_gram_exists) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NativeScalarGram.native_scalar_gram_exists, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@NativeScalarGram.native_scalar_gram_exists) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram.native_scalar_gram_exists.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram.family
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram
