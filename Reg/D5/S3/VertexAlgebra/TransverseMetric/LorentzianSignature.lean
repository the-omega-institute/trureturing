import D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
  _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
  _root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix TensorProduct

noncomputable section

structure Params where
  data : LatticeData
  frame : Matrix (Fin data.rank) (Fin data.rank) ℂ
  frameInverse : Matrix (Fin data.rank) (Fin data.rank) ℂ
  xAxis : Fin data.rank
  yAxis : Fin data.rank

private abbrev witnessData : LatticeData where
  rank := 3
  G := fun first second =>
    if (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) then 1
    else if first = 2 ∧ second = 2 then 2 else 0
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> decide
  even_diagonal := by intro axis; fin_cases axis <;> norm_num [Fin.ext_iff]

private def witnessParams : Params := ⟨witnessData, 1, 1, 0, 1⟩

private theorem witnessSum (value : Fin witnessData.rank → ℂ) :
    ∑ index, value index = value 0 + value 1 + value 2 :=
  Fin.sum_univ_three value

private theorem witnessReal :
    ∀ row column, star ((1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ)
      row column) = (1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ) row column := by
  intro row column
  simp [Matrix.one_apply, apply_ite]

private theorem witnessX : ∀ row,
    gramPair witnessData ((1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ) 1)
      ((1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ) row) =
        if row = 0 then 1 else 0 := by
  intro row
  fin_cases row <;> apply Complex.ext <;>
    norm_num only [gramPair, witnessSum, Matrix.one_apply, witnessData, Fin.ext_iff,
      Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_natCast,
      and_true, true_and, and_false, false_and, false_or, or_false, true_or, or_true,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, ite_true, ite_false]

private theorem witnessY : ∀ row,
    gramPair witnessData ((1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ) 0)
      ((1 : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ) row) =
        if row = 1 then 1 else 0 := by
  intro row
  fin_cases row <;> apply Complex.ext <;>
    norm_num only [gramPair, witnessSum, Matrix.one_apply, witnessData, Fin.ext_iff,
      Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_natCast,
      and_true, true_and, and_false, false_and, false_or, or_false, true_or, or_true,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, ite_true, ite_false]

private theorem witnessSignature :
    _root_.D5.S3.QuadraticForms.ActualSignature.signature (gramReal witnessData).toQuadraticForm' =
      (witnessData.rank : ℤ) - 2 := by
  apply (_root_.D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature
    3 (gramReal witnessData) (by
      intro first second
      exact congrArg (fun value : ℤ => (value : ℝ)) (witnessData.symmetric first second)) 1).mp
  refine Or.inr (Or.inl ⟨2, Or.inl ⟨by norm_num [gramReal, witnessData, Fin.ext_iff], ?_⟩⟩)
  refine Or.inr (Or.inr ⟨?_, 0, 0, ?_, ?_⟩)
  · intro axis
    fin_cases axis <;>
      norm_num [_root_.D5.S3.QuadraticForms.ActualSignature.residualOne,
        gramReal, witnessData, Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]
  · norm_num [_root_.D5.S3.QuadraticForms.ActualSignature.residualOne,
      gramReal, witnessData, Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]
  · rfl

private def witnessVector : TransverseAxis witnessData 0 1 → ℝ := fun _ => 1

private theorem witnessVectorNonzero : witnessVector ≠ 0 := by
  intro equality
  have impossible := congrFun equality ⟨2, by decide, by decide⟩
  norm_num [witnessVector] at impossible

namespace Geometry

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun parameter => TransverseAxis parameter.data parameter.xAxis parameter.yAxis → ℝ)
    (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ parameter vector => by
    classical
    exact decide (0 < Matrix.toQuadraticForm'
      (transverseGram parameter.data parameter.frame parameter.xAxis parameter.yAxis) vector))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (parameter : Params)
    (leftInverse : parameter.frameInverse * parameter.frame = 1)
    (rightInverse : parameter.frame * parameter.frameInverse = 1)
    (distinct : parameter.xAxis ≠ parameter.yAxis)
    (realRows : ∀ row column, star (parameter.frame row column) = parameter.frame row column)
    (xDual : ∀ row, gramPair parameter.data (parameter.frame parameter.yAxis)
      (parameter.frame row) = if row = parameter.xAxis then 1 else 0)
    (yDual : ∀ row, gramPair parameter.data (parameter.frame parameter.xAxis)
      (parameter.frame row) = if row = parameter.yAxis then 1 else 0),
    _root_.D5.S3.QuadraticForms.ActualSignature.signature (gramReal parameter.data).toQuadraticForm' =
      (parameter.data.rank : ℤ) - 2 →
    ∀ vector : TransverseAxis parameter.data parameter.xAxis parameter.yAxis → ℝ,
      vector ≠ 0 → observation.readout () parameter vector = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.transverseGram_posDef)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source parameter leftInverse rightInverse distinct realRows xDual yDual lorentzian vector nonzero
    exact decide_eq_true ((source parameter.data parameter.frame parameter.frameInverse
      leftInverse rightInverse parameter.xAxis parameter.yAxis distinct realRows xDual yDual
      lorentzian).toQuadraticForm' vector nonzero)
  · intro law data frame inverse leftInverse rightInverse xAxis yAxis distinct realRows xDual yDual lorentzian
    apply Matrix.PosDef.of_toQuadraticForm'
    · ext first second
      exact congrArg Complex.re (gramPair_symm data (frame second.1) (frame first.1))
    · intro vector nonzero
      exact of_decide_eq_true (law ⟨data, frame, inverse, xAxis, yAxis⟩ leftInverse rightInverse
        distinct realRows xDual yDual lorentzian vector nonzero)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessParams (by simp [witnessParams]) (by simp [witnessParams])
    (by decide) witnessReal witnessX witnessY witnessSignature witnessVector witnessVectorNonzero
  change false = true at impossible
  cases impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessParams, 0, witnessVector, ?_⟩
  have positive := (transverseGram_posDef witnessData 1 1 (by simp) (by simp) 0 1
    (by decide) witnessReal witnessX witnessY witnessSignature).toQuadraticForm'
      witnessVector witnessVectorNonzero
  change decide (0 < (transverseGram witnessData 1 0 1).toQuadraticForm' 0) ≠
    decide (0 < (transverseGram witnessData 1 0 1).toQuadraticForm' witnessVector)
  rw [decide_eq_true positive]
  simp

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.transverseGram_posDef)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp transverseGram_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Geometry

namespace Polynomial

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun parameter => MvPolynomial (TransverseAxis parameter.data parameter.xAxis parameter.yAxis × ℕ) ℂ)
    (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ parameter polynomial => by
    classical
    exact decide (0 < (fockForm parameter.data
        (nativePolynomial parameter.data parameter.frame parameter.xAxis parameter.yAxis polynomial)
        (nativePolynomial parameter.data parameter.frame parameter.xAxis parameter.yAxis polynomial)).re ∧
        (fockForm parameter.data
          (nativePolynomial parameter.data parameter.frame parameter.xAxis parameter.yAxis polynomial)
          (nativePolynomial parameter.data parameter.frame parameter.xAxis parameter.yAxis polynomial)).im = 0))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (parameter : Params)
    (leftInverse : parameter.frameInverse * parameter.frame = 1)
    (rightInverse : parameter.frame * parameter.frameInverse = 1)
    (distinct : parameter.xAxis ≠ parameter.yAxis)
    (realRows : ∀ row column, star (parameter.frame row column) = parameter.frame row column)
    (xDual : ∀ row, gramPair parameter.data (parameter.frame parameter.yAxis)
      (parameter.frame row) = if row = parameter.xAxis then 1 else 0)
    (yDual : ∀ row, gramPair parameter.data (parameter.frame parameter.xAxis)
      (parameter.frame row) = if row = parameter.yAxis then 1 else 0),
    _root_.D5.S3.QuadraticForms.ActualSignature.signature (gramReal parameter.data).toQuadraticForm' =
      (parameter.data.rank : ℤ) - 2 →
    ∀ polynomial : MvPolynomial (TransverseAxis parameter.data parameter.xAxis parameter.yAxis × ℕ) ℂ,
      polynomial ≠ 0 → observation.readout () parameter polynomial = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.nativePolynomial_positive_of_lorentzian)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source parameter leftInverse rightInverse distinct realRows xDual yDual lorentzian polynomial nonzero
    exact decide_eq_true (source parameter.data parameter.frame parameter.frameInverse
      leftInverse rightInverse parameter.xAxis parameter.yAxis distinct realRows xDual yDual
      lorentzian polynomial nonzero)
  · intro law data frame inverse leftInverse rightInverse xAxis yAxis distinct realRows xDual yDual
      lorentzian polynomial nonzero
    exact of_decide_eq_true (law ⟨data, frame, inverse, xAxis, yAxis⟩ leftInverse rightInverse
      distinct realRows xDual yDual lorentzian polynomial nonzero)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessParams (by simp [witnessParams]) (by simp [witnessParams])
    (by decide) witnessReal witnessX witnessY witnessSignature 1 one_ne_zero
  change false = true at impossible
  cases impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessParams, 0, 1, ?_⟩
  have positive := nativePolynomial_positive_of_lorentzian witnessData 1 1 (by simp) (by simp)
    0 1 (by decide) witnessReal witnessX witnessY witnessSignature 1 one_ne_zero
  change decide (0 < (fockForm witnessData (nativePolynomial witnessData 1 0 1 0)
    (nativePolynomial witnessData 1 0 1 0)).re ∧
    (fockForm witnessData (nativePolynomial witnessData 1 0 1 0)
      (nativePolynomial witnessData 1 0 1 0)).im = 0) ≠
    decide (0 < (fockForm witnessData (nativePolynomial witnessData 1 0 1 1)
      (nativePolynomial witnessData 1 0 1 1)).re ∧
      (fockForm witnessData (nativePolynomial witnessData 1 0 1 1)
        (nativePolynomial witnessData 1 0 1 1)).im = 0)
  rw [decide_eq_true positive]
  simp [fockForm]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.nativePolynomial_positive_of_lorentzian)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp nativePolynomial_positive_of_lorentzian, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Polynomial

namespace C0

structure StateParams extends Params where
  gramInverse : Matrix (Fin data.rank) (Fin data.rank) ℂ
  beta : Charge data
  level : ℤ

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature StateParams
    (fun parameter => State parameter.data) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ parameter state => by
    classical
    exact decide (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F parameter.data state
        (C parameter.data 0 state)).re ∧
        (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F parameter.data state
          (C parameter.data 0 state)).im = 0))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (parameter : StateParams)
    (leftGramInverse : parameter.gramInverse * gramComplex parameter.data = 1)
    (rightGramInverse : gramComplex parameter.data * parameter.gramInverse = 1)
    (leftFrameInverse : parameter.frameInverse * parameter.frame = 1)
    (rightFrameInverse : parameter.frame * parameter.frameInverse = 1)
    (distinct : parameter.xAxis ≠ parameter.yAxis)
    (realRows : ∀ row column, star (parameter.frame row column) = parameter.frame row column)
    (xDual : ∀ row, gramPair parameter.data (parameter.frame parameter.yAxis)
      (parameter.frame row) = if row = parameter.xAxis then 1 else 0)
    (yDual : ∀ row, gramPair parameter.data (parameter.frame parameter.xAxis)
      (parameter.frame row) = if row = parameter.yAxis then 1 else 0),
    _root_.D5.S3.QuadraticForms.ActualSignature.signature (gramReal parameter.data).toQuadraticForm' =
      (parameter.data.rank : ℤ) - 2 → ∀ state : State parameter.data,
    state ∈ nativeTransverseEnergySpace parameter.data parameter.gramInverse parameter.frame
      parameter.frameInverse leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      parameter.beta parameter.xAxis parameter.yAxis parameter.level →
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J parameter.data state = state →
    state ≠ 0 → observation.readout () parameter state = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source parameter leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      distinct realRows xDual yDual lorentzian state member degreeOne nonzero
    exact decide_eq_true (source parameter.data parameter.gramInverse parameter.frame parameter.frameInverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse parameter.beta
      parameter.xAxis parameter.yAxis distinct parameter.level realRows xDual yDual lorentzian
      state member degreeOne nonzero)
  · intro law data gramInverse frame inverse leftGramInverse rightGramInverse leftFrameInverse
      rightFrameInverse beta xAxis yAxis distinct level realRows xDual yDual lorentzian
      state member degreeOne nonzero
    exact of_decide_eq_true (law ⟨⟨data, frame, inverse, xAxis, yAxis⟩, gramInverse, beta, level⟩
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse distinct realRows
      xDual yDual lorentzian state member degreeOne nonzero)

private def witnessInverse : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ :=
  fun first second =>
    if (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) then 1
    else if first = 2 ∧ second = 2 then 1 / 2 else 0

private theorem witnessHG : witnessInverse * gramComplex witnessData = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;> apply Complex.ext <;>
    norm_num only [witnessInverse, gramComplex, Matrix.map_apply, witnessData, Matrix.mul_apply,
      Matrix.one_apply, witnessSum, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_natCast,
      and_true, true_and, and_false, false_and, false_or, or_false, true_or, or_true,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, Complex.div_ofNat_re, Complex.div_ofNat_im, ite_true, ite_false]

private theorem witnessGH : gramComplex witnessData * witnessInverse = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;> apply Complex.ext <;>
    norm_num only [witnessInverse, gramComplex, Matrix.map_apply, witnessData, Matrix.mul_apply,
      Matrix.one_apply, witnessSum, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_natCast,
      and_true, true_and, and_false, false_and, false_or, or_false, true_or, or_true,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, Complex.div_ofNat_re, Complex.div_ofNat_im, ite_true, ite_false]

private def witnessStateParams : StateParams := ⟨witnessParams, witnessInverse, 0, 0⟩

private def witnessState : State witnessData := nativeWord witnessData 1 0 (0, ∅)

private theorem witnessPairing :
    -_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
      (C witnessData 0 witnessState) = 1 := by
  rw [witnessState,
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection.F_c0_native_empty_normalization]
  simp [coordinateSub, MvPolynomial.monomial_zero, fockForm_vacuum_left]

private theorem witnessNonzero : witnessState ≠ 0 := by
  intro zero
  have impossible := witnessPairing
  rw [zero] at impossible
  simp [_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F] at impossible

private theorem witnessMember : witnessState ∈ nativeTransverseEnergySpace witnessData
    witnessInverse 1 1 witnessHG witnessGH (by simp) (by simp) 0 0 1 0 := by
  let index : transverseLevelIndex witnessData 0 1 0 :=
    ⟨(0, ∅), by simp, by simp, by simp, by simp [nativeLevel, polarizedLevel]⟩
  exact transverseLevelWord_mem_space witnessData witnessInverse 1 1 witnessHG witnessGH
    (by simp) (by simp) 0 0 1 0 index

private theorem witnessDegree :
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J witnessData witnessState =
      witnessState := by
  simp [witnessState, nativeWord_J, epsilonCount, thetaCount, etaCount]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessStateParams witnessHG witnessGH
    (by simp [witnessStateParams, witnessParams]) (by simp [witnessStateParams, witnessParams])
    (by decide) witnessReal witnessX witnessY witnessSignature
    witnessState witnessMember witnessDegree witnessNonzero
  change false = true at impossible
  cases impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessStateParams, 0, witnessState, ?_⟩
  change decide (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData 0
    (C witnessData 0 0)).re ∧
    (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData 0 (C witnessData 0 0)).im = 0) ≠
    decide (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
      (C witnessData 0 witnessState)).re ∧
      (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
        (C witnessData 0 witnessState)).im = 0)
  rw [witnessPairing]
  simp [_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature.native_degree_one_negative_C0_positive_of_lorentzian)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp native_degree_one_negative_C0_positive_of_lorentzian,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end C0

#print axioms transverseGram_posDef
#print axioms Geometry.familyRegistration
#print axioms Polynomial.familyRegistration
#print axioms C0.familyRegistration

end
end Reg.D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature
