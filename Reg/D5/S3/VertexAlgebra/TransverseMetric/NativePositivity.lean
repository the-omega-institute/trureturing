import D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct

noncomputable section

structure Params where
  data : LatticeData
  gramInverse : Matrix (Fin data.rank) (Fin data.rank) ℂ
  frame : Matrix (Fin data.rank) (Fin data.rank) ℂ
  frameInverse : Matrix (Fin data.rank) (Fin data.rank) ℂ
  beta : Charge data
  xAxis : Fin data.rank
  yAxis : Fin data.rank
  level : ℤ

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Params (fun parameter => State parameter.data)
    (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ parameter state => @decide
    (∃ polynomial, nativeDown parameter.data parameter.frame parameter.beta
      parameter.xAxis parameter.yAxis polynomial = state) (Classical.propDecidable _))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (parameter : Params) (state : State parameter.data)
    (leftGramInverse : parameter.gramInverse * gramComplex parameter.data = 1)
    (rightGramInverse : gramComplex parameter.data * parameter.gramInverse = 1)
    (leftFrameInverse : parameter.frameInverse * parameter.frame = 1)
    (rightFrameInverse : parameter.frame * parameter.frameInverse = 1),
    state ∈ nativeTransverseEnergySpace parameter.data parameter.gramInverse parameter.frame
      parameter.frameInverse leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      parameter.beta parameter.xAxis parameter.yAxis parameter.level →
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J parameter.data state = state →
    observation.readout () parameter state = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.native_J_one_down)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source parameter state leftGramInverse rightGramInverse leftFrameInverse
      rightFrameInverse member degreeOne
    exact decide_eq_true (source parameter.data parameter.gramInverse parameter.frame
      parameter.frameInverse leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      parameter.beta parameter.xAxis parameter.yAxis parameter.level state member degreeOne)
  · intro law data gramInverse frame frameInverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level state member degreeOne
    exact of_decide_eq_true (law ⟨data, gramInverse, frame, frameInverse, beta, xAxis, yAxis, level⟩
      state leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse member degreeOne)

private abbrev witnessData : LatticeData where
  rank := 2
  G := Matrix.diagonal (fun axis => if axis = 0 then -2 else 2)
  symmetric := by
    intro first second
    by_cases equal : first = second
    · subst second
      rfl
    · simp [Matrix.diagonal_apply, equal, Ne.symm equal]
  even_diagonal := by intro axis; fin_cases axis <;> norm_num [Matrix.diagonal_apply]

private def witnessInverse : Matrix (Fin witnessData.rank) (Fin witnessData.rank) ℂ :=
  Matrix.diagonal (fun axis => if axis = 0 then -(1 / 2) else 1 / 2)

private theorem witnessHG : witnessInverse * gramComplex witnessData = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [witnessInverse, gramComplex, witnessData, Matrix.mul_apply, Matrix.diagonal_apply]

private theorem witnessGH : gramComplex witnessData * witnessInverse = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [witnessInverse, gramComplex, witnessData, Matrix.mul_apply, Matrix.diagonal_apply]

private def witnessParams : Params :=
  ⟨witnessData, witnessInverse, 1, 1, 0, 0, 1, 0⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have zeroMember : (0 : State witnessData) ∈
      nativeTransverseEnergySpace witnessData witnessInverse 1 1 witnessHG witnessGH
        (by simp) (by simp) 0 0 1 0 := Submodule.zero_mem _
  have impossible := law witnessParams 0 witnessHG witnessGH
    (by simp [witnessParams]) (by simp [witnessParams])
    zeroMember (by simp)
  change false = true at impossible
  cases impossible

private theorem nativeDown_J (parameter : Params)
    (polynomial : MvPolynomial (TransverseAxis parameter.data parameter.xAxis parameter.yAxis × ℕ) ℂ) :
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J parameter.data
        (nativeDown parameter.data parameter.frame parameter.beta parameter.xAxis parameter.yAxis polynomial) =
      nativeDown parameter.data parameter.frame parameter.beta parameter.xAxis parameter.yAxis polynomial := by
  have degree := (original_polarized_state_sector parameter.data
    (Finsupp.single parameter.beta
      (nativePolynomial parameter.data parameter.frame parameter.xAxis parameter.yAxis polynomial)) ∅).1
  simpa [nativeDown, downWord, epsilonCount, thetaCount, etaCount] using degree

private theorem partner_not_range :
    ¬ ∃ polynomial, nativeDown witnessData 1 0 0 1 polynomial =
      nativeWord witnessData 1 0 (0, {3}) := by
  rintro ⟨polynomial, equality⟩
  have degreeOne := nativeDown_J witnessParams polynomial
  change _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J witnessData
    (nativeDown witnessData 1 0 0 1 polynomial) = nativeDown witnessData 1 0 0 1 polynomial at degreeOne
  rw [equality, nativeWord_J] at degreeOne
  norm_num [epsilonCount, thetaCount, etaCount] at degreeOne
  have zeroPartner : nativeWord witnessData 1 0 (0, {3}) = 0 := by
    simpa [two_smul, add_eq_left] using degreeOne
  have independent := nativeWord_linearIndependent witnessData 1 1 (by simp) (by simp) 0
  exact independent.ne_zero (0, {3}) zeroPartner

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨witnessParams, 0, nativeWord witnessData 1 0 (0, {3}), ?_⟩
  change decide (∃ polynomial, nativeDown witnessData 1 0 0 1 polynomial = 0) ≠
    decide (∃ polynomial, nativeDown witnessData 1 0 0 1 polynomial = nativeWord witnessData 1 0 (0, {3}))
  rw [decide_eq_true (show ∃ polynomial, nativeDown witnessData 1 0 0 1 polynomial = 0 from
    ⟨0, map_zero _⟩), decide_eq_false partner_not_range]
  decide

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.native_J_one_down)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp native_J_one_down, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

example : type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.nativePolynomial_positive) :=
  nativePolynomial_positive

example : type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.native_degree_one_negative_C0_positive) :=
  native_degree_one_negative_C0_positive

#print axioms nativePolynomial_positive
#print axioms nativePolynomial_norm_real
#print axioms nativePolynomial_injective
#print axioms native_J_one_down
#print axioms native_degree_one_negative_C0_positive
#print axioms familyRegistration

namespace C0

def actual : Realization signature := by
  classical
  exact realize signature (fun _ parameter state => decide
    (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F parameter.data state
      (C parameter.data 0 state)).re ∧
      (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F parameter.data state
        (C parameter.data 0 state)).im = 0))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (parameter : Params) (state : State parameter.data)
    (leftGramInverse : parameter.gramInverse * gramComplex parameter.data = 1)
    (rightGramInverse : gramComplex parameter.data * parameter.gramInverse = 1)
    (leftFrameInverse : parameter.frameInverse * parameter.frame = 1)
    (rightFrameInverse : parameter.frame * parameter.frameInverse = 1)
    (realRows : ∀ (axis : TransverseAxis parameter.data parameter.xAxis parameter.yAxis) component,
      star (parameter.frame axis.1 component) = parameter.frame axis.1 component),
    (transverseGram parameter.data parameter.frame parameter.xAxis parameter.yAxis).PosDef →
    state ∈ nativeTransverseEnergySpace parameter.data parameter.gramInverse parameter.frame
      parameter.frameInverse leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      parameter.beta parameter.xAxis parameter.yAxis parameter.level →
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J parameter.data state = state →
    state ≠ 0 → observation.readout () parameter state = true

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.native_degree_one_negative_C0_positive)) ↔
      arena.Law actual := by
  classical
  constructor
  · intro source parameter state leftGramInverse rightGramInverse leftFrameInverse
      rightFrameInverse realRows positive member degreeOne nonzero
    exact decide_eq_true (source parameter.data parameter.gramInverse parameter.frame
      parameter.frameInverse leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
      parameter.beta parameter.xAxis parameter.yAxis parameter.level realRows positive state
      member degreeOne nonzero)
  · intro law data gramInverse frame frameInverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level realRows positive state member degreeOne nonzero
    exact of_decide_eq_true (law ⟨data, gramInverse, frame, frameInverse, beta, xAxis, yAxis, level⟩
      state leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse realRows positive
      member degreeOne nonzero)

private theorem no_transverse_axis (axis : TransverseAxis witnessData 0 1) : False := by
  rcases axis with ⟨axis, restrictions⟩
  fin_cases axis <;> simp_all

private theorem witnessRestrictedPositive : (transverseGram witnessData 1 0 1).PosDef := by
  constructor
  · ext axis
    exact False.elim (no_transverse_axis axis)
  · intro vector nonzero
    exact False.elim (nonzero (Finsupp.ext fun axis => False.elim (no_transverse_axis axis)))

private def witnessState : State witnessData := nativeWord witnessData 1 0 (0, ∅)

private theorem witnessNonzero : witnessState ≠ 0 :=
  (nativeWord_linearIndependent witnessData 1 1 (by simp) (by simp) 0).ne_zero (0, ∅)

private theorem witnessMember : witnessState ∈
    nativeTransverseEnergySpace witnessData witnessInverse 1 1 witnessHG witnessGH
      (by simp) (by simp) 0 0 1 0 := by
  let index : transverseLevelIndex witnessData 0 1 0 :=
    ⟨(0, ∅), by simp, by simp, by simp, by simp [nativeLevel, polarizedLevel]⟩
  exact transverseLevelWord_mem_space witnessData witnessInverse 1 1 witnessHG witnessGH
    (by simp) (by simp) 0 0 1 0 index

private theorem witnessDegree :
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber.J witnessData witnessState = witnessState := by
  simp [witnessState, nativeWord_J, epsilonCount, thetaCount, etaCount]

private theorem witnessPairing :
    -_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
      (C witnessData 0 witnessState) = 1 := by
  rw [witnessState,
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostAuxiliarySelection.F_c0_native_empty_normalization]
  simp [coordinateSub, MvPolynomial.monomial_zero,
    _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm.fockForm_vacuum_left]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessParams witnessState witnessHG witnessGH
    (by simp [witnessParams]) (by simp [witnessParams])
    (by intro axis; exact False.elim (no_transverse_axis axis)) witnessRestrictedPositive
    witnessMember witnessDegree witnessNonzero
  change false = true at impossible
  cases impossible

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨witnessParams, 0, witnessState, ?_⟩
  change decide (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData 0
    (C witnessData 0 0)).re ∧
    (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData 0 (C witnessData 0 0)).im = 0) ≠
    decide (0 < (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
      (C witnessData 0 witnessState)).re ∧
      (-_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F witnessData witnessState
        (C witnessData 0 witnessState)).im = 0)
  rw [witnessPairing]
  simp [_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm.F, map_zero]

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity.native_degree_one_negative_C0_positive)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp native_degree_one_negative_C0_positive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

#print axioms familyRegistration

end C0

end
end Reg.D5.S3.VertexAlgebra.TransverseMetric.NativePositivity
