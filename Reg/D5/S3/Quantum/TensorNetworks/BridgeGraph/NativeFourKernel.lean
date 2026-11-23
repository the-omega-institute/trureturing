import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
import Reg.Support.SingleDependentReadout

/-! Source readouts for the spectral and coefficient-space implications. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound (stackK stackK_gram stackK_compression)
open _root_.D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation (gram_identity_injective)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder

noncomputable section

abbrev matrixSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun b => Matrix (Fin b) (Fin b) ℂ)
    (fun b => Matrix (Fin b) (Fin b) ℂ → Prop)

def matrixEq : Realization matrixSignature :=
  realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def matrixFalse : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem matrixDependence : ObservationalDependence matrixSignature matrixEq := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (Fin 1) (Fin 1) ℂ) = 0) =
    ((1 : Matrix (Fin 1) (Fin 1) ℂ) = 0) at he
  have hh := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) (Eq.mp he rfl)
  norm_num at hh

abbrev dimSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def dimLt : Realization dimSignature :=
  realize dimSignature (fun _ _ x y => x < y) (fun e => nomatch e)

def dimLe : Realization dimSignature :=
  realize dimSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def dimFalse : Realization dimSignature :=
  realize dimSignature (fun _ _ _ _ => False) (fun e => nomatch e)

def dimTrue : Realization dimSignature :=
  realize dimSignature (fun _ _ _ _ => True) (fun e => nomatch e)

private theorem ltDependence : ObservationalDependence dimSignature dimLt := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  norm_num [dimLt, realize] at he

private theorem leDependence : ObservationalDependence dimSignature dimLe := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [dimLe, realize] at he

private def oneSlot (r : Fin 4) : Matrix (Fin 1) (Fin 1) ℂ :=
  if r = 0 then 1 else 0

private theorem oneSlotStack : Function.Injective (stackK oneSlot).mulVecLin := by
  apply gram_identity_injective
  rw [stackK_gram]
  simp [oneSlot, Fin.sum_univ_four]

private def units2 (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if r.val = 2 * i.val + j.val then 1 else 0

private theorem units2Independent : LinearIndependent ℂ units2 := by
  rw [Fintype.linearIndependent_iff]
  intro g h r
  have entry (i j : Fin 2) := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) h
  fin_cases r
  · simpa [units2, Fin.sum_univ_four, Matrix.sum_apply, Matrix.smul_apply] using entry 0 0
  · simpa [units2, Fin.sum_univ_four, Matrix.sum_apply, Matrix.smul_apply] using entry 0 1
  · simpa [units2, Fin.sum_univ_four, Matrix.sum_apply, Matrix.smul_apply] using entry 1 0
  · simpa [units2, Fin.sum_univ_four, Matrix.sum_apply, Matrix.smul_apply] using entry 1 1

private def invertibleForm : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1, 1, -1, -1]

private theorem invertibleFormDet : invertibleForm.det = 1 := by
  rw [invertibleForm, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

private theorem invertibleFormHermitian : invertibleForm.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [invertibleForm, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.star_def]

private theorem invertibleCompression : compression units2 invertibleForm = 0 := by
  rw [compression, stackK_compression]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [invertibleForm, units2, Matrix.diagonal_apply, Fin.sum_univ_four, Fin.sum_univ_two,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def]

abbrev adjointArena : Arena where
  signature := matrixSignature
  Law R := ∀ {a b : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ),
    R.readout () b (compression X Tᴴ) (compression X T)ᴴ

private theorem adjointRejected : ¬ adjointArena.Law matrixFalse := by
  intro h
  exact h (0 : Fin 4 → Matrix (Fin 1) (Fin 1) ℂ) 0

def adjointFamily : Registration adjointArena (type_of% @compression_star) where
  actual := matrixEq
  bridge := Iff.rfl
  variation := ⟨@compression_star, matrixFalse, adjointRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    adjointArena.Law matrixEq matrixFalse adjointRejected
  dependence := matrixDependence

def adjointRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@compression_star) (Realization matrixSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.compression_star.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.adjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨adjointArena⟩
  objectArena := .source ⟨adjointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjointArena ⟨adjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev rankArena : Arena where
  signature := dimSignature
  Law R := ∀ {a b : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (_hinj : Function.Injective (stackK X).mulVecLin) (T : Matrix (Fin 4) (Fin 4) ℂ)
    (_hT : T.IsHermitian) (_h : compression X T = 0) (k : ℕ) (_hk : k ≤ 3)
    (_hb : k * a < b), R.readout () () T.rank (2 * (4 - k) - 1)

private theorem rankRejected : ¬ rankArena.Law dimFalse := by
  intro h
  exact h oneSlot oneSlotStack 0 (by simp [Matrix.IsHermitian])
    (by simp [compression, Matrix.zero_kronecker]) 0 (by decide) (by decide)

def rankFamily : Registration rankArena (type_of% @hermitian_rank_bound) where
  actual := dimLt
  bridge := Iff.rfl
  variation := ⟨@hermitian_rank_bound, dimFalse, rankRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    rankArena.Law dimLt dimFalse rankRejected
  dependence := ltDependence

def rankRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_rank_bound) (Realization dimSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.hermitian_rank_bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dimSignature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev geometryArena : Arena where
  signature := dimSignature
  Law R := ∀ {a b : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (_hX : LinearIndependent ℂ X)
    (_h : ∀ T, T.IsHermitian → compression X T = 0 → R.readout () () T.rank 2),
    (∀ T, T.IsHermitian → compression X T = 0 → T = 0) ∨
    (∃ v : Fin 4 → ℂ, v ≠ 0 ∧ ∀ T, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0) ∨
    (∃ E : Matrix (Fin 4) (Fin 3) ℂ, E.rank = 3 ∧
      ∀ T, T.IsHermitian → compression X T = 0 → Eᴴ * T * E = 0)

private theorem geometryRejected : ¬ geometryArena.Law dimTrue := by
  intro h
  have hdet : invertibleForm.det ≠ 0 := by rw [invertibleFormDet]; exact one_ne_zero
  have hTex := Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at hTex
  rcases h units2 units2Independent (fun _ _ _ => trivial) with hz | ⟨v, hv, hker⟩ | ⟨E, hE, hE0⟩
  · have h := hz invertibleForm invertibleFormHermitian invertibleCompression
    exact hdet (by simp [h])
  · have hunit : IsUnit invertibleForm :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    exact hv (hinj ((hker invertibleForm invertibleFormHermitian invertibleCompression).trans
      (Matrix.mulVec_zero _).symm))
  · have h1 := Matrix.rank_mul_ge Eᴴ invertibleForm
    have h2 := Matrix.rank_mul_ge (Eᴴ * invertibleForm) E
    rw [Matrix.rank_conjTranspose, hE, hTex, Fintype.card_fin] at h1
    rw [hE0 invertibleForm invertibleFormHermitian invertibleCompression, Matrix.rank_zero,
      hE, Fintype.card_fin] at h2
    omega

def geometryFamily : Registration geometryArena (type_of% @coefficient_geometry) where
  actual := dimLe
  bridge := Iff.rfl
  variation := ⟨@coefficient_geometry, dimTrue, geometryRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    geometryArena.Law dimLe dimTrue geometryRejected
  dependence := leDependence

def geometryRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coefficient_geometry) (Realization dimSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.coefficient_geometry.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel.geometryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨geometryArena⟩
  objectArena := .source ⟨geometryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source geometryArena ⟨geometryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize dimSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
