import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification
import Reg.Support.SingleDependentReadout

/-! Equality of column Grams as a dependent observation on the source dimensions. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification
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
  Law R := ∀ (a b c d : ℕ) (lam : ℝ) (_hlam : 0 < lam),
    (∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      R.readout () ⟨b, c⟩
        ((∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)))
        ((lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))) ↔
      ScalarGramAdmissible a b c d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hadm : ScalarGramAdmissible 1 1 1 1 := Or.inr (Or.inr (Or.inl ⟨le_rfl, le_rfl⟩))
  obtain ⟨M, N, hfalse⟩ := (h 1 1 1 1 1 (by norm_num)).mpr hadm
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

def family : Registration arena (type_of% @native_scalar_gram_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_scalar_gram_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_scalar_gram_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification.native_scalar_gram_iff.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification.family
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification
