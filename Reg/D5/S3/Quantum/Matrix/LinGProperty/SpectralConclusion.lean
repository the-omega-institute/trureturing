import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion
import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import Reg.Support.SingleDependentReadout

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1) {c : ℝ} (hc : 1 ≤ c)
    (j : Fin (Fintype.card (Fin n)))
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (hL1 : 2 * singularValuesSorted X j ≤
      (hAp.isHermitian.add hBp.isHermitian).eigenvalues₀ j + 1 - ‖X.trace‖)
    (hG : (geometricMean (phi c A) (phi c B)).IsHermitian),
    R.readout () () (singularValuesSorted (phi c X) j) (hG.eigenvalues₀ j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let M := Matrix (Fin 1) (Fin 1) ℂ
  have hw : (fromBlocks (1 : M) 0 (0 : M) (1 : M)).PosSemidef := by
    rw [Matrix.fromBlocks_one]
    exact PosSemidef.one
  have hw' : (fromBlocks (1 : M) 0 (0 : M)ᴴ (1 : M)).PosSemidef := by
    simpa only [conjTranspose_zero] using hw
  have ht : (1 : M).trace = 1 := by simp [M, Matrix.trace]
  have hp : (1 : M).PosSemidef := PosSemidef.one
  have hm : (geometricMean (phi 1 (1 : M)) (phi 1 (1 : M))).IsHermitian :=
    (geometricMean_riccati (phi_posDef hp one_ne_zero le_rfl)
      (phi_posDef hp one_ne_zero le_rfl)).1.isHermitian
  exact @h 1 1 0 1 hw' ht ht 1 le_rfl 0 hp hp
    (normalized_arithmetic_bound hw' ht ht hp hp 0) hm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena (type_of% @normalized_conclusion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_conclusion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_conclusion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinGProperty.normalized_conclusion.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion.family
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
    owner := `D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion
