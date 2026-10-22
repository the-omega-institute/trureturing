import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
open scoped TensorProduct

noncomputable section

abbrev Parameters := Σ object : NativeLattice,
  Σ _left : Charge object.lattice, Σ _right : Charge object.lattice, ℤ

abbrev Parameters.object (parameter : Parameters) : NativeLattice := parameter.1
abbrev Parameters.left (parameter : Parameters) : Charge parameter.object.lattice :=
  parameter.2.1
abbrev Parameters.right (parameter : Parameters) : Charge parameter.object.lattice :=
  parameter.2.2.1
abbrev Parameters.total (parameter : Parameters) : ℤ := parameter.2.2.2

abbrev signature : Signature where
  Params := Parameters
  State parameter := ActualTensor parameter.object.lattice parameter.object.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℤ → ActualTensor parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter state => fun exponent =>
    clearedOrderedCoefficient parameter.object.lattice parameter.object.native
      parameter.left parameter.right
      exponent (parameter.total - exponent) state) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ state => fun _ => state) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (object : NativeLattice) (left right : Charge object.lattice)
      (total : ℤ) (state : ActualTensor object.lattice object.native),
    Function.HasFiniteSupport (observation.readout () ⟨object, left, right, total⟩ state)

private def probeLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro first second; rfl
  even_diagonal := by intro colour; exact Fin.elim0 colour

private theorem probeNative : IsUnit probeLattice.G.det := by
  simp [probeLattice, Matrix.det_isEmpty]

private def probeState : ActualTensor probeLattice probeNative :=
  (1 : Oscillator probeLattice) ⊗ₜ[ℂ] (1 : ActualGround probeLattice probeNative)

private theorem probe_nonzero : probeState ≠ 0 := by
  have leading := charged_ground_leading probeLattice probeNative 0
    (1 : ActualGround probeLattice probeNative) one_ne_zero
  intro zero
  change chargedCoefficient probeLattice probeNative 0
    (-chargeNorm probeLattice 0) probeState ≠ 0 at leading
  rw [zero, map_zero] at leading
  exact leading rfl

private theorem probe_coefficient (state : ActualTensor probeLattice probeNative) :
    chargedCoefficient probeLattice probeNative 0 0 state = state := by
  have identity := congrArg
    (fun field : HVertexOperator ℤ ℂ (ActualTensor probeLattice probeNative)
      (ActualTensor probeLattice probeNative) => field.coeff 0 state)
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.charged_zero_identity
      probeLattice probeNative)
  simp only [chargedField, HVertexOperator.coeff_of_coeff] at identity
  change chargedCoefficient probeLattice probeNative 0 0 state =
    ((HahnModule.of ℂ).symm
      ((_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField
        (V := ActualTensor probeLattice probeNative)) state)).coeff 0 at identity
  rw [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    VertexOperator.of_coeff_apply_coeff] at identity
  simpa using identity

private theorem probe_cleared (state : ActualTensor probeLattice probeNative) :
    clearedOrderedCoefficient probeLattice probeNative 0 0 0 0 state = state := by
  simp [clearedOrderedCoefficient, bilinear, probe_coefficient, Module.End.mul_apply]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have finite := law ⟨probeLattice, probeNative⟩ 0 0 0 probeState
  change (Function.support (fun _ : ℤ => probeState)).Finite at finite
  have support : Function.support (fun _ : ℤ => probeState) = Set.univ := by
    ext exponent
    exact iff_true_intro probe_nonzero
  rw [support] at finite
  exact Set.infinite_univ.not_finite finite

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨⟨probeLattice, probeNative⟩, 0, 0, 0⟩, probeState, 0, ?_⟩
  intro equality
  have coefficient := congrFun equality 0
  change clearedOrderedCoefficient probeLattice probeNative 0 0 0 (0 - 0) probeState =
    clearedOrderedCoefficient probeLattice probeNative 0 0 0 (0 - 0) 0 at coefficient
  simp only [sub_self, probe_cleared] at coefficient
  exact probe_nonzero coefficient

def registration : Registration arena (type_of% (@cleared_diagonal_support)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cleared_diagonal_support, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cleared_diagonal_support)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.cleared_diagonal_support.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameter state => fun exponent =>
    clearedOrderedCoefficient parameter.object.lattice parameter.object.native
      parameter.left parameter.right
      exponent (parameter.total - exponent) state) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

abbrev ChartParameters := Σ object : NativeLattice,
  Σ _left : Charge object.lattice, Σ _right : Charge object.lattice, Σ _order : ℕ, ℤ

abbrev ChartParameters.object (parameter : ChartParameters) : NativeLattice := parameter.1
abbrev ChartParameters.left (parameter : ChartParameters) : Charge parameter.object.lattice :=
  parameter.2.1
abbrev ChartParameters.right (parameter : ChartParameters) : Charge parameter.object.lattice :=
  parameter.2.2.1
abbrev ChartParameters.order (parameter : ChartParameters) : ℕ := parameter.2.2.2.1
abbrev ChartParameters.total (parameter : ChartParameters) : ℤ := parameter.2.2.2.2

abbrev chartSignature : Signature where
  Params := ChartParameters
  State parameter := ActualTensor parameter.object.lattice parameter.object.native
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def actualCharts : Realization chartSignature :=
  realize chartSignature (fun role parameter state =>
    if role = 0 then
      localPlus parameter.object.lattice parameter.object.native parameter.left parameter.right
        parameter.order parameter.total state
    else
      localMinus parameter.object.lattice parameter.object.native parameter.left parameter.right
        parameter.order parameter.total state) (fun empty => nomatch empty)

def rejectedCharts : Realization chartSignature :=
  realize chartSignature (fun _ _ state => state) (fun empty => nomatch empty)

def rejectedRoleCharts (selected : Fin 2) : Realization chartSignature :=
  realize chartSignature (fun role parameter state =>
    if role = selected then state else actualCharts.readout role parameter state)
    (fun empty => nomatch empty)

abbrev chartArena : Arena where
  signature := chartSignature
  Law observation := ∀ (object : NativeLattice) (left right : Charge object.lattice)
      (order : ℕ) (total : ℤ) (state : ActualTensor object.lattice object.native),
    (order < ((bilinear object.lattice left right).natAbs +
        bilinear object.lattice left right : ℤ).toNat →
      observation.readout 0 ⟨object, left, right, order, total⟩ state = 0) ∧
    (order < ((bilinear object.lattice left right).natAbs -
        bilinear object.lattice left right : ℤ).toNat →
      observation.readout 1 ⟨object, left, right, order, total⟩ state = 0)

private def hyperbolicLattice : LatticeData where
  rank := 2
  G := ![![0, 1], ![1, 0]]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro colour; fin_cases colour <;> norm_num

private theorem hyperbolicNative : IsUnit hyperbolicLattice.G.det := by
  change IsUnit (Matrix.det (![![0, 1], ![1, 0]] : Matrix (Fin 2) (Fin 2) ℤ))
  norm_num [Matrix.det_fin_two]

private def hyperbolicState : ActualTensor hyperbolicLattice hyperbolicNative :=
  (1 : Oscillator hyperbolicLattice) ⊗ₜ[ℂ]
    (1 : ActualGround hyperbolicLattice hyperbolicNative)

private theorem hyperbolic_state_nonzero : hyperbolicState ≠ 0 := by
  have leading := charged_ground_leading hyperbolicLattice hyperbolicNative 0
    (1 : ActualGround hyperbolicLattice hyperbolicNative) one_ne_zero
  intro zero
  change chargedCoefficient hyperbolicLattice hyperbolicNative 0
    (-chargeNorm hyperbolicLattice 0) hyperbolicState ≠ 0 at leading
  rw [zero, map_zero] at leading
  exact leading rfl

private theorem hyperbolic_gram :
    bilinear hyperbolicLattice (fun _ => 1) (fun _ => 1) = 2 := by
  change (∑ first : Fin 2, ∑ second : Fin 2,
    (1 : ℤ) * (![![0, 1], ![1, 0]] : Matrix (Fin 2) (Fin 2) ℤ) first second * 1) = 2
  norm_num [Fin.sum_univ_two]

private theorem rejected_chart_law : ¬ chartArena.Law rejectedCharts := by
  intro law
  have endpoint := (law ⟨hyperbolicLattice, hyperbolicNative⟩
    (fun _ => 1) (fun _ => 1) 0 0 hyperbolicState).1
  have below : 0 < ((bilinear hyperbolicLattice (fun _ => 1) (fun _ => 1)).natAbs +
      bilinear hyperbolicLattice (fun _ => 1) (fun _ => 1) : ℤ).toNat := by
    rw [hyperbolic_gram]
    norm_num
  exact hyperbolic_state_nonzero (endpoint below)

private theorem rejected_role_chart_law (selected : Fin 2) :
    ¬ chartArena.Law (rejectedRoleCharts selected) := by
  intro law
  fin_cases selected
  · have endpoint := (law ⟨hyperbolicLattice, hyperbolicNative⟩
      (fun _ => 1) (fun _ => 1) 0 0 hyperbolicState).1
    have below : 0 < ((bilinear hyperbolicLattice (fun _ => 1) (fun _ => 1)).natAbs +
        bilinear hyperbolicLattice (fun _ => 1) (fun _ => 1) : ℤ).toNat := by
      rw [hyperbolic_gram]
      norm_num
    have zero := endpoint below
    exact hyperbolic_state_nonzero (by simpa [rejectedRoleCharts, realize] using zero)
  · have endpoint := (law ⟨hyperbolicLattice, hyperbolicNative⟩
      (-(fun _ => 1)) (fun _ => 1) 0 0 hyperbolicState).2
    have below : 0 < ((bilinear hyperbolicLattice (-(fun _ => 1)) (fun _ => 1)).natAbs -
        bilinear hyperbolicLattice (-(fun _ => 1)) (fun _ => 1) : ℤ).toNat := by
      rw [_root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration.bilinear_neg_left,
        hyperbolic_gram]
      norm_num
    have zero := endpoint below
    exact hyperbolic_state_nonzero (by simpa [rejectedRoleCharts, realize] using zero)

private theorem probe_zero_coefficient (exponent : ℤ)
    (state : ActualTensor probeLattice probeNative) :
    chargedCoefficient probeLattice probeNative 0 exponent state =
      if exponent = 0 then state else 0 := by
  have identity := congrArg
    (fun field : HVertexOperator ℤ ℂ (ActualTensor probeLattice probeNative)
      (ActualTensor probeLattice probeNative) => field.coeff exponent state)
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.charged_zero_identity
      probeLattice probeNative)
  simp only [chargedField, HVertexOperator.coeff_of_coeff] at identity
  change chargedCoefficient probeLattice probeNative 0 exponent state =
    ((HahnModule.of ℂ).symm
      ((_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField
        (V := ActualTensor probeLattice probeNative)) state)).coeff exponent at identity
  rw [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
    VertexOperator.of_coeff_apply_coeff] at identity
  by_cases zero : exponent = 0 <;> simpa [zero] using identity

private theorem probe_local_plus (state : ActualTensor probeLattice probeNative) :
    localPlus probeLattice probeNative 0 0 0 0 state = state := by
  change (∑ᶠ exponent : ℤ, halfIntegerBinomial exponent 0 •
    clearedOrderedCoefficient probeLattice probeNative 0 0 exponent (0 - exponent) state) = _
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp [halfIntegerBinomial, probe_cleared]
  · intro exponent nonzero
    simp [clearedOrderedCoefficient, bilinear, LinearMap.smul_apply,
      LinearMap.sum_apply, Module.End.mul_apply, probe_zero_coefficient, nonzero]

private theorem probe_local_minus (state : ActualTensor probeLattice probeNative) :
    localMinus probeLattice probeNative 0 0 0 0 state = state := by
  change (∑ᶠ exponent : ℤ, (((-1 : ℂ) ^ exponent) * halfIntegerBinomial exponent 0) •
    clearedOrderedCoefficient probeLattice probeNative 0 0 exponent (0 - exponent) state) = _
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp [halfIntegerBinomial, probe_cleared]
  · intro exponent nonzero
    simp [clearedOrderedCoefficient, bilinear, LinearMap.smul_apply,
      LinearMap.sum_apply, Module.End.mul_apply, probe_zero_coefficient, nonzero]

private theorem chartDependence : ObservationalDependence chartSignature actualCharts := by
  intro role
  refine ⟨⟨⟨probeLattice, probeNative⟩, 0, 0, 0, 0⟩, probeState, 0, ?_⟩
  intro equality
  change (if role = 0 then localPlus probeLattice probeNative 0 0 0 0 probeState else
      localMinus probeLattice probeNative 0 0 0 0 probeState) =
    (if role = 0 then localPlus probeLattice probeNative 0 0 0 0 0 else
      localMinus probeLattice probeNative 0 0 0 0 0) at equality
  by_cases first : role = 0
  · simp only [if_pos first, probe_local_plus] at equality
    exact probe_nonzero equality
  · simp only [if_neg first, probe_local_minus] at equality
    exact probe_nonzero equality

def chartRegistration : Registration chartArena (type_of% (@local_charts_below_start)) where
  actual := actualCharts
  bridge := Iff.rfl
  variation := ⟨local_charts_below_start, rejectedCharts, rejected_chart_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejectedRoleCharts role, ?_, rfl, rejected_role_chart_law role⟩
      intro other distinct
      funext parameter state
      simp [rejectedRoleCharts, realize, distinct]
    · intro empty
      exact nomatch empty
  dependence := chartDependence

def chartAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@local_charts_below_start)
    (Realization chartSignature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.local_charts_below_start.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence.chartRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨chartArena⟩
  objectArena := .source ⟨chartArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chartArena ⟨chartRegistration⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize chartSignature (fun role parameter state =>
    if role = 0 then
      localPlus parameter.object.lattice parameter.object.native parameter.left parameter.right
        parameter.order parameter.total state
    else
      localMinus parameter.object.lattice parameter.object.native parameter.left parameter.right
        parameter.order parameter.total state) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
