import D5.S3.VertexAlgebra.OriginalIntegralBVGerstBracketTransient
import D5.S3.VertexAlgebra.OriginalZeroChargeBrstGrading

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalCartanOperator

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge BcGhostFockSupport BcGhostSuperGenerators
open VertexOperatorTensorProduct
open scoped TensorProduct VertexOperator BigOperators

def currentState (D : LatticeData) (axis : Fin D.rank) : State D :=
  Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0)) ⊗ₜ[ℂ]
    Finsupp.single {1} 1

def cartanState (D : LatticeData) : (Fin D.rank → ℂ) →ₗ[ℂ] State D :=
  -∑ axis, (LinearMap.proj axis).smulRight (currentState D axis)

theorem cartanState_apply (D : LatticeData) (coefficients : Fin D.rank → ℂ) :
    cartanState D coefficients = -∑ axis, coefficients axis • currentState D axis := by
  simp [cartanState]

theorem currentState_field (D : LatticeData) (axis : Fin D.rank) :
    LatticeBcGhostTensorStateField.stateField D (currentState D axis) =
      field (neutralField D axis) (currentField .c) := by
  have matter : ((neutralField D axis)[[-1]]) (LatticeAllStateField.vacuum D) =
      Finsupp.single (0 : Charge D) (MvPolynomial.X (axis, 0)) := by
    rw [neutralField_ncoeff]
    simp [neutralMode, neutralPolynomialMode, LatticeAllStateField.vacuum]
  have ghost : c 1 (vacuum : Fock ℂ) = Finsupp.single {1} 1 := by
    norm_num [c, vacuum, create, createBasis, sign]
  rw [currentState, ← matter, ← ghost, LatticeBcGhostTensorStateField.stateField_tmul,
    LatticeAllStateField.stateField_current, BcGhostSuperStateField.stateField_c_generator]

theorem currentState_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (axis : Fin D.rank) : Q D H (currentState D axis) = 0 := by
  exact OriginalZeroChargeBrstDifferential.Q_current_low D H leftInverse rightInverse axis false

theorem cartanState_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (coefficients : Fin D.rank → ℂ) : Q D H (cartanState D coefficients) = 0 := by
  simp [cartanState_apply, currentState_Q D H leftInverse rightInverse]

theorem currentState_B0 (D : LatticeData) (axis : Fin D.rank) :
    B D 0 (currentState D axis) = 0 := by
  simp only [currentState, B, TensorProduct.map_tmul, LinearMap.id_apply]
  norm_num [b, annihilate, annihilateBasis]

theorem cartanState_B0 (D : LatticeData) (coefficients : Fin D.rank → ℂ) :
    B D 0 (cartanState D coefficients) = 0 := by
  simp [cartanState_apply, currentState_B0]

theorem currentField_B0_tmul (D : LatticeData) (axis : Fin D.rank)
    (mode : ℤ) (matter : Carrier D) (ghost : Fock ℂ) :
    B D 0 (((field (neutralField D axis) (currentField .c))[[mode]])
      (matter ⊗ₜ[ℂ] ghost)) +
      ((field (neutralField D axis) (currentField .c))[[mode]])
        (B D 0 (matter ⊗ₜ[ℂ] ghost)) =
      neutralMode D axis (mode + 1) matter ⊗ₜ[ℂ] ghost := by
  have mapped := (B D 0).toAddMonoidHom.map_finsum
    (diagonal_finite (neutralField D axis) (currentField .c) mode matter ghost)
  simp only [LinearMap.toAddMonoidHom_coe, diagonal] at mapped
  rw [field_mode, mode_tmul, mapped]
  simp only [B, TensorProduct.map_tmul, LinearMap.id_apply]
  change (∑ᶠ index : ℤ, ((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
      b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
    (∑ᶠ index : ℤ, ((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
      ((currentField .c)[[mode - 1 - index]]) (b 0 ghost)) = _
  have firstFinite : Function.HasFiniteSupport (fun index : ℤ =>
      ((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) := by
    exact (diagonal_finite (neutralField D axis) (currentField .c) mode matter ghost).fun_comp
      (g := B D 0) (by simp)
  have joined :
      (∑ᶠ index : ℤ, ((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
      (∑ᶠ index : ℤ, ((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
        ((currentField .c)[[mode - 1 - index]]) (b 0 ghost)) =
      ∑ᶠ index : ℤ, ((((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
        (((neutralField D axis)[[index]]) matter ⊗ₜ[ℂ]
          ((currentField .c)[[mode - 1 - index]]) (b 0 ghost))) := by
    exact (finsum_add_distrib firstFinite
      (diagonal_finite (neutralField D axis) (currentField .c) mode matter (b 0 ghost))).symm
  rw [joined]
  simp only [← TensorProduct.tmul_add, currentField_modes, currentMode]
  have anticommutator (index : ℤ) :
      b 0 (c (mode - 1 - index + 2) ghost) +
        c (mode - 1 - index + 2) (b 0 ghost) =
      if index = mode + 1 then ghost else 0 := by
    have equality := LinearMap.congr_fun
      (BcGhostStressCurrent.b_c (K := ℂ) 0 (mode - 1 - index + 2)) ghost
    simp only [Module.End.mul_apply, LinearMap.add_apply] at equality
    by_cases same : index = mode + 1
    · have zeroMode : (0 : ℤ) + (mode - 1 - index + 2) = 0 := by omega
      rw [if_pos zeroMode] at equality
      simpa only [Module.End.one_apply, if_pos same] using equality
    · have different : (0 : ℤ) + (mode - 1 - index + 2) ≠ 0 := by omega
      rw [if_neg different] at equality
      simpa only [LinearMap.zero_apply, if_neg same] using equality
  simp_rw [anticommutator]
  rw [finsum_eq_single _ (mode + 1)]
  · simp [neutralField_ncoeff]
  · intro index different
    simp [different]

theorem currentState_B0_field (D : LatticeData) (axis : Fin D.rank)
    (mode : ℤ) (state : State D) :
    B D 0 (((LatticeBcGhostTensorStateField.stateField D (currentState D axis))[[mode]])
      state) +
      ((LatticeBcGhostTensorStateField.stateField D (currentState D axis))[[mode]])
        (B D 0 state) =
      TensorProduct.map (neutralMode D axis (mode + 1)) LinearMap.id state := by
  rw [currentState_field]
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul matter ghost =>
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using
        currentField_B0_tmul D axis mode matter ghost
  | add first second firstIH secondIH =>
      simp only [map_add]
      rw [← firstIH, ← secondIH]
      abel

def momentum (D : LatticeData) (coefficients : Fin D.rank → ℂ) : Module.End ℂ (State D) :=
  ∑ axis, coefficients axis • TensorProduct.map (neutralMode D axis 0) LinearMap.id

theorem cartanState_B0_minusOne (D : LatticeData) (coefficients : Fin D.rank → ℂ)
    (state : State D) :
    B D 0 (((LatticeBcGhostTensorStateField.stateField D
      (cartanState D coefficients))[[-1]]) state) +
      ((LatticeBcGhostTensorStateField.stateField D
        (cartanState D coefficients))[[-1]]) (B D 0 state) =
      -momentum D coefficients state := by
  simp only [cartanState_apply, map_neg, map_sum, map_smul, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  simp only [← smul_add, currentState_B0_field,
    show (-1 : ℤ) + 1 = 0 by norm_num, momentum,
    LinearMap.sum_apply, LinearMap.smul_apply]

#print axioms currentState_B0_field
#print axioms cartanState_B0_minusOne

end D5.S3.VertexAlgebra.OriginalCartanOperator
