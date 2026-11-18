import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
import D5.S3.Quantum.MatrixAnalysis.InverseOperatorConvexity
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
open _root_.D5.S3.Quantum.MatrixAnalysis.InverseOperatorConvexity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

namespace Reg.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
local instance : Pow Mat ℝ := ⟨CFC.rpow⟩

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => 1 ≤ t) (fun e => nomatch e)

def rejected (i : Fin 2) : Realization signature :=
  realize signature (fun j _ t => if j = i then False else 1 ≤ t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α p q : ℝ}, 0 < α → α < 1 → 0 < p → 0 < q →
    (∀ A B : Mat, A.PosDef → B.PosDef →
      harmonicMean α p A B ≤ powerMean α q A B) →
    R.readout 0 () p ∧ R.readout 1 () q

private theorem harmonic_arithmetic_one {A B : Mat} (hA : A.PosDef) (hB : B.PosDef) :
    harmonicMean (1/2) 1 A B ≤ powerMean (1/2) 1 A B := by
  have hS : ((1/2 : ℝ) • A⁻¹ + (1/2 : ℝ) • B⁻¹).PosDef :=
    (hA.inv.smul (by norm_num : (0 : ℝ) < 1/2)).add
      (hB.inv.smul (by norm_num : (0 : ℝ) < 1/2))
  have hT : ((1/2 : ℝ) • A + (1/2 : ℝ) • B).PosDef :=
    (hA.smul (by norm_num : (0 : ℝ) < 1/2)).add
      (hB.smul (by norm_num : (0 : ℝ) < 1/2))
  have hc := posDef_weighted_inverse_le hA.inv hB.inv
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hAi : A⁻¹⁻¹ = A :=
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hBi : B⁻¹⁻¹ = B :=
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  rw [hAi, hBi] at hc
  unfold harmonicMean powerMean
  norm_num only [one_div, inv_one, CFC.rpow_one A hA.posSemidef.nonneg,
    CFC.rpow_one B hB.posSemidef.nonneg]
  convert hc using 1 <;>
    norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num,
      CFC.rpow_one _ hS.inv.posSemidef.nonneg, CFC.rpow_one _ hT.posSemidef.nonneg]

private theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  have hc := h (α := 1/2) (p := 1) (q := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ _ hA hB => harmonic_arithmetic_one hA hB)
  fin_cases i
  · simpa [rejected, realize] using hc.1
  · simpa [rejected, realize] using hc.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (2 : ℝ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext u t
      simp [actual, rejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic.family
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
    (fun _ _ t => 1 ≤ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
