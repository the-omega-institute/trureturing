import D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.RingTheory.Flat.Basic

/-! Source-bound residue observations with actual hyperbolic-lattice probes. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectedField
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

noncomputable section

private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change (Matrix.det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private def probeGround : ActualGround hyperbolic hyperbolic_unit := fun _ => 1

private theorem probeGround_nonzero : probeGround ≠ 0 := by
  intro equality
  have coordinate := congrFun equality (0 : Half (groundRank hyperbolic hyperbolic_unit))
  exact one_ne_zero (show (1 : ℂ) = 0 from coordinate)

private def probeState : ActualTensor hyperbolic hyperbolic_unit :=
  (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround

private def probeExcited : ActualTensor hyperbolic hyperbolic_unit :=
  (MvPolynomial.X ((1 : Fin 2), 0) : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround

private def probeSeed : NativeField hyperbolic hyperbolic_unit :=
  chargedField hyperbolic hyperbolic_unit 0

private theorem probe_leading : probeSeed.coeff 0 probeState ≠ 0 := by
  change chargedCoefficient hyperbolic hyperbolic_unit 0 0
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround) ≠ 0
  simpa [chargeNorm, bilinear] using
    charged_ground_leading hyperbolic hyperbolic_unit 0 probeGround probeGround_nonzero

private theorem probe_negative (e : ℤ) (he : e < 0) :
    probeSeed.coeff e probeState = 0 := by
  change chargedCoefficient hyperbolic hyperbolic_unit 0 e
    ((1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround) = 0
  apply charged_polynomial_lower_bound
  simpa [chargeNorm, bilinear, nativeOddWeightedDegree,
    MvPolynomial.weightedTotalDegree] using he

private theorem creation_injective : Function.Injective
    (LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) (-1)) := by
  let A := LinearMap.mulLeft ℂ (MvPolynomial.X ((0 : Fin 2), 0) : Oscillator hyperbolic)
  have hA : Function.Injective A := by
    intro a b eq
    exact mul_left_cancel₀ (MvPolynomial.X_ne_zero _) eq
  have injection := TensorProduct.map_injective_of_flat_flat A
    (LinearMap.id : Module.End ℂ (ActualGround hyperbolic hyperbolic_unit)) hA
    (fun _ _ eq => eq)
  simpa [A, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
    LatticeHalfFock.current] using injection

private theorem probe_creation_nonzero :
    LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) (-1) (probeSeed.coeff 0 probeState) ≠ 0 := by
  intro zero
  apply probe_leading
  apply creation_injective
  simpa only [map_zero] using zero

private theorem probe_current_nonnegative (q : ℤ) (hq : 0 ≤ q) :
    LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) q probeState = 0 := by
  simp [probeState, LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
    LatticeHalfFock.current, not_lt.mpr hq, ← LatticeActualAnnihilation.annihilation_apply]

private theorem probe_excited_annihilation :
    LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) 0 probeExcited = (1 / 2 : ℂ) • probeState := by
  norm_num [probeExcited, probeState, LatticeHalfFock.tensorCurrent,
    LatticeHalfFock.tensorEnd, LatticeHalfFock.current, LatticeHalfFock.frequency,
    LatticeActualAnnihilation.annihilate_X, hyperbolic, TensorProduct.smul_tmul]

private theorem probe_singleton :
    (singletonLinear hyperbolic hyperbolic_unit ((0 : Fin 2), 0) probeSeed).coeff (-1)
      probeState =
    LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) (-1) (probeSeed.coeff 0 probeState) := by
  have expression := singleton_negative_current_residue hyperbolic hyperbolic_unit
    ((0 : Fin 2), 0) probeSeed 0 (-1) probeState
  norm_num only [sourceWeight, halfBinomial, Finset.sum_range_succ,
    Finset.sum_range_zero, Finset.prod_range_zero, Nat.factorial_zero,
    zero_add, add_zero, div_one, one_smul] at expression
  rw [expression, currentResidue]
  have currentZero (l : ℕ) :
      LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
        0 l probeState = 0 := probe_current_nonnegative l (by omega)
  simp only [currentZero, map_zero, smul_zero, finsum_zero, sub_zero]
  rw [finsum_eq_single _ 0]
  · simp
  · intro l hl
    have below : -2 * ((-1 : ℤ) + l) - 2 < 0 := by omega
    simp only [probe_negative _ below, map_zero, smul_zero]

private theorem probeState_nonzero : probeState ≠ 0 := by
  intro zero
  have nonzero := charged_ground_leading hyperbolic hyperbolic_unit 0
    probeGround probeGround_nonzero
  exact nonzero (by rw [show (1 : Oscillator hyperbolic) ⊗ₜ[ℂ] probeGround = 0 from zero,
    map_zero])

structure ResidueParameter where
  lattice : LatticeData
  unit : IsUnit lattice.G.det
  colour : Fin lattice.rank
  field : NativeField lattice unit
  gamma : ℤ
  residue : ℤ
  mode : ℤ

private theorem repeated_not_finite :
    ¬ Function.HasFiniteSupport (fun _ : ℕ => probeState) := by
  intro finite
  have support : Function.support (fun _ : ℕ => probeState) = Set.univ := by
    ext l
    simp [Function.mem_support, probeState_nonzero]
  change (Function.support _).Finite at finite
  rw [support] at finite
  exact Set.infinite_univ finite

namespace Left

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ResidueParameter
  (fun p => ActualTensor p.lattice p.unit)
  (fun p => ℕ → ActualTensor p.lattice p.unit)

def actual : Realization signature := realize signature
  (fun _ p x l => ((-1 : ℂ) ^ l * Ring.choose (p.residue : ℂ) l) •
    LatticeHalfFock.tensorCurrent p.lattice (ActualGround p.lattice p.unit) p.colour
      (p.residue - l) (p.field.coeff (-2 * (p.mode + l) - p.gamma - 2) x))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ x _ => x) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (F : NativeField D hu) (gamma r t : ℤ) (x : ActualTensor D hu),
    Function.HasFiniteSupport (readout.readout () ⟨D, hu, i, F, gamma, r, t⟩ x)

theorem source_bridge : (type_of% (@current_residue_left_finite)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact repeated_not_finite
    (law hyperbolic hyperbolic_unit (0 : Fin 2) probeSeed (-2) (-1) 0 probeState)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, (0 : Fin 2), probeSeed, -2, -1, 0⟩,
    0, probeState, ?_⟩
  intro equality
  have coordinate := congrFun equality 0
  simp only [actual, realize, map_zero, smul_zero, pow_zero, Ring.choose_zero_right,
    mul_one, one_smul] at coordinate
  exact probe_creation_nonzero coordinate.symm

def familyRegistration : Registration arena (type_of% (@current_residue_left_finite)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp current_residue_left_finite, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_residue_left_finite) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.current_residue_left_finite "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue.Left.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Left

namespace Right

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ResidueParameter
  (fun p => ActualTensor p.lattice p.unit)
  (fun p => ℕ → ActualTensor p.lattice p.unit)

def actual : Realization signature := realize signature
  (fun _ p x l => ((-1 : ℂ) ^ l * Ring.choose (p.residue : ℂ) l) •
    p.field.coeff (-2 * (p.residue + p.mode - l) - p.gamma - 2)
      (LatticeHalfFock.tensorCurrent p.lattice (ActualGround p.lattice p.unit) p.colour l x))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ x _ => x) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (F : NativeField D hu) (gamma r t : ℤ) (x : ActualTensor D hu),
    Function.HasFiniteSupport (readout.readout () ⟨D, hu, i, F, gamma, r, t⟩ x)

theorem source_bridge : (type_of% (@current_residue_right_finite)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact repeated_not_finite
    (law hyperbolic hyperbolic_unit (0 : Fin 2) probeSeed (-2) (0) 0 probeState)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, (0 : Fin 2), probeSeed, -2, 0, 0⟩,
    0, probeExcited, ?_⟩
  intro equality
  have coordinate := congrFun equality 0
  simp only [actual, realize, map_zero, smul_zero, pow_zero, Ring.choose_zero_right,
    mul_one, one_smul] at coordinate
  change 0 = probeSeed.coeff 0
    (LatticeHalfFock.tensorCurrent hyperbolic (ActualGround hyperbolic hyperbolic_unit)
      (0 : Fin 2) 0 probeExcited) at coordinate
  rw [probe_excited_annihilation, map_smul] at coordinate
  exact smul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) probe_leading coordinate.symm

def familyRegistration : Registration arena (type_of% (@current_residue_right_finite)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp current_residue_right_finite, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_residue_right_finite) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.current_residue_right_finite "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue.Right.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Right

structure CoefficientParameter where
  lattice : LatticeData
  unit : IsUnit lattice.G.det
  index : Index lattice
  field : NativeField lattice unit
  gamma : ℤ
  mode : ℤ

namespace Convolution

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  CoefficientParameter
  (fun p => ActualTensor p.lattice p.unit)
  (fun p => ActualTensor p.lattice p.unit)

def actual : Realization signature := realize signature
  (fun _ p x => (singletonLinear p.lattice p.unit p.index p.field).coeff
    (-2 * p.mode - p.gamma - 3) x)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ x => x) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (F : NativeField D hu) (gamma k : ℤ) (x : ActualTensor D hu),
    readout.readout () ⟨D, hu, index, F, gamma, k⟩ x =
      ∑ j ∈ Finset.range (sourceWeight D index), halfBinomial j •
        currentResidue D hu index.1 F gamma
          (-(sourceWeight D index : ℤ) + j) (k - j) x

theorem source_bridge :
    (type_of% (@singleton_negative_current_residue)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit ((0 : Fin 2), 0) 0 0 0 probeState
  have identity := singleton_negative_current_residue hyperbolic hyperbolic_unit
    ((0 : Fin 2), 0) 0 0 0 probeState
  change probeState = _ at bad
  rw [← identity] at bad
  exact probeState_nonzero (by simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using bad)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit, ((0 : Fin 2), 0), probeSeed, 0, -1⟩,
    0, probeState, ?_⟩
  intro equality
  simp only [actual, realize, map_zero] at equality
  apply probe_creation_nonzero
  rw [← probe_singleton]
  exact equality.symm

def familyRegistration : Registration arena (type_of% (@singleton_negative_current_residue)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp singleton_negative_current_residue, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@singleton_negative_current_residue) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.singleton_negative_current_residue "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue.Convolution.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Convolution

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue

