import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
import Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane
import Reg.Support.DependentFamily

/-! A source-bound audit of the simultaneous native complex pairing. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
open Matrix Module
open scoped ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane

abbrev signature := _root_.Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.signature
abbrev actual := _root_.Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.actual
abbrev rejected := _root_.Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b : ℕ} (_hab : 3 * a < 2 * b) (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (_hX : LinearIndependent ℂ X)
    (_hinj : Function.Injective (stack X).mulVecLin),
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
        (stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ R.readout () T v = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply _root_.Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.rejected_law
  exact h (a := 3) (b := 5) (by norm_num)

def family : Registration arena (type_of% (@common_plane)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_plane, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, ![1,0,0], ?_⟩
    intro he
    have hh := congrFun he 0
    norm_num [actual, _root_.Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.actual,
      realize] at hh

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@common_plane) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane.common_plane.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ T v => T *ᵥ v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
