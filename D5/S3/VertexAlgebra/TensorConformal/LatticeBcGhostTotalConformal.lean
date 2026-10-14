/- GID: D5/S3/VertexAlgebra/TensorConformal/LatticeBcGhostTotalConformal
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TensorConformal/LatticeBcGhostTotalConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual total conformal state and modes on the original full tensor carrier. -/

import D5.S3.VertexAlgebra.LatticeBcGhostTensorJacobi
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.BcGhostActualConformalState
import D5.S3.VertexAlgebra.BcGhostVirasoro
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Int.Cast.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostTotalConformal

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeBcGhostBrstCharge
open scoped TensorProduct VertexOperator

noncomputable section

def omega (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : State D :=
  LatticeActualConformalState.omega D H ⊗ₜ[ℂ]
      (BcGhostFockSupport.vacuum : BcGhostFockSupport.Fock ℂ) +
    LatticeAllStateField.vacuum D ⊗ₜ[ℂ] BcGhostActualConformalState.omegaState

def ghostStress : VertexOperator ℂ (BcGhostFockSupport.Fock ℂ) :=
  SuperFieldProducts.normal (-1) (BcGhostSuperGenerators.currentField .c)
      (FieldNormalProduct.dividedDerivative 1 (BcGhostSuperGenerators.currentField .b)) -
    (2 : ℂ) • SuperFieldProducts.normal (-1) (BcGhostSuperGenerators.currentField .b)
      (FieldNormalProduct.dividedDerivative 1 (BcGhostSuperGenerators.currentField .c))

def stressField (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    VertexOperator ℂ (State D) :=
  VertexOperatorTensorProduct.field (sugawaraField D H)
      (VertexOperatorTensorProduct.identityField (BcGhostFockSupport.Fock ℂ)) +
    VertexOperatorTensorProduct.field (VertexOperatorTensorProduct.identityField (Carrier D))
      ghostStress

def totalMode (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    Module.End ℂ (State D) := M D H mode + G D mode

theorem omega_field (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    LatticeBcGhostTensorStateField.stateField D (omega D H) = stressField D H := by
  rw [omega, map_add, LatticeBcGhostTensorStateField.stateField_tmul,
    LatticeBcGhostTensorStateField.stateField_tmul, LatticeActualConformalState.Y_omega,
    BcGhostSuperStateField.stateField_vacuum, LatticeAllStateField.stateField_vacuum,
    BcGhostActualConformalState.omega_field_expansion]
  rfl

theorem stress_modes (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (mode : ℤ) : (stressField D H)[[mode + 1]] = totalMode D H mode := by
  rw [stressField]
  simp only [map_add, Pi.add_apply]
  rw [VertexOperatorTensorProduct.field_identity_right,
    VertexOperatorTensorProduct.field_identity_left]
  change TensorProduct.map (sugawaraMode D H mode) LinearMap.id +
    TensorProduct.map LinearMap.id (ghostStress[[mode + 1]]) = _
  rw [show ghostStress = BcGhostSuperStateField.Y BcGhostActualConformalState.omegaState
    from BcGhostActualConformalState.omega_field_expansion.symm,
    BcGhostActualConformalState.conformal_modes]
  rfl

theorem omega_modes (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (mode : ℤ) :
    (LatticeBcGhostTensorStateField.stateField D (omega D H))[[mode + 1]] =
      M D H mode + G D mode := by
  rw [omega_field, stress_modes]
  rfl

theorem omega_even (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    omega D H ∈ LatticeBcGhostTensorStateField.homogeneous 0 := by
  have ghostVacuum : (BcGhostFockSupport.vacuum : BcGhostFockSupport.Fock ℂ) ∈
      BcGhostSuperGenerators.homogeneous 0 :=
    BcGhostSuperGenerators.single_mem 0 ∅ 1 (by
      norm_num [BcGhostSuperGenerators.subsetParity])
  have ghostOmega : BcGhostActualConformalState.omegaState ∈
      BcGhostSuperGenerators.homogeneous 0 := by
    apply Submodule.sub_mem
    · exact BcGhostSuperGenerators.single_mem 0 {1, 2} 1 (by
        norm_num [BcGhostSuperGenerators.subsetParity])
    · apply Submodule.smul_mem
      exact BcGhostSuperGenerators.single_mem 0 {0, 3} 1 (by
        norm_num [BcGhostSuperGenerators.subsetParity])
  exact Submodule.add_mem _
    (LatticeBcGhostTensorStateField.tmul_mem 0 _ _ ghostVacuum)
    (LatticeBcGhostTensorStateField.tmul_mem 0 _ _ ghostOmega)

theorem vacuum_annihilation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (bound : -1 ≤ mode) :
    totalMode D H mode (LatticeBcGhostTensorStateField.vacuum D) = 0 := by
  rw [← stress_modes, ← omega_field]
  exact LatticeBcGhostTensorStateField.stateField_creativity D (omega D H) (mode + 1)
    (by omega)

theorem minus_one_eq_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1) :
    totalMode D H (-1) = LatticeBcGhostTensorStateField.translation D := by
  unfold totalMode M G LatticeBcGhostTensorStateField.translation
    VertexOperatorTensorProduct.tensorTranslation
  rw [sugawaraMode_minus_one_eq_translation D H leftInverse rightInverse]
  rfl

theorem virasoro (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (first second : ℤ) :
    totalMode D H first * totalMode D H second -
        totalMode D H second * totalMode D H first =
      ((first - second : ℤ) : ℂ) • totalMode D H (first + second) +
        (if first + second = 0 then
          ((D.rank : ℂ) - 26) / 12 * ((first : ℂ) ^ 3 - first) else 0) •
            (1 : Module.End ℂ (State D)) := by
  have matter := congrArg (LinearMap.rTensorHom (BcGhostFockSupport.Fock ℂ))
    (LatticeSugawaraVirasoro.sugawaraMode_virasoro D H leftInverse rightInverse first second)
  simp only [map_sub, map_add, map_smul, LinearMap.coe_rTensorHom,
    LinearMap.rTensor_mul, Module.End.one_eq_id, LinearMap.rTensor_id] at matter
  have ghost := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostVirasoro.L_virasoro (K := ℂ) first second)
  simp only [map_sub, map_add, map_smul, LinearMap.coe_lTensorHom,
    LinearMap.lTensor_mul, LinearMap.lTensor_id] at ghost
  have divisible : (6 : ℤ) ∣ first ^ 3 - first := by
    have factorial := Nat.factorial_coe_dvd_prod 3 (first - 1)
    norm_num [Finset.prod_range_succ] at factorial
    convert factorial using 1 <;> ring
  have central : ((-13 * (first ^ 3 - first) / 6 : ℤ) : ℂ) =
      -(26 : ℂ) / 12 * ((first : ℂ) ^ 3 - first) := by
    rw [Int.cast_div (dvd_mul_of_dvd_right divisible (-13))
      (by norm_num : (6 : ℂ) ≠ 0)]
    push_cast
    ring
  have commute (matterMode ghostMode : ℤ) :
      M D H matterMode * G D ghostMode = G D ghostMode * M D H matterMode := by
    apply TensorProduct.ext'
    intro matterState ghostState
    simp [M, G, Module.End.mul_apply]
  change M D H first * M D H second - M D H second * M D H first = _ at matter
  change G D first * G D second - G D second * G D first = _ at ghost
  rw [central] at ghost
  calc
    _ = (M D H first * M D H second - M D H second * M D H first) +
        (G D first * G D second - G D second * G D first) := by
      unfold totalMode
      rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add,
        commute first second, commute second first]
      abel
    _ = _ := by
      rw [matter, ghost]
      simp only [Int.cast_sub]
      change ((first : ℂ) - second) • M D H (first + second) +
        (if first + second = 0 then (D.rank : ℂ) / 12 *
          ((first : ℂ) ^ 3 - first) else 0) • (1 : Module.End ℂ (State D)) +
        (((first : ℂ) - second) • G D (first + second) +
        (if first + second = 0 then -(26 : ℂ) / 12 *
          ((first : ℂ) ^ 3 - first) else 0) • (1 : Module.End ℂ (State D))) = _
      unfold totalMode
      rw [smul_add]
      by_cases resonance : first + second = 0
      · simp only [resonance, if_true]
        have scalar : (D.rank : ℂ) / 12 * ((first : ℂ) ^ 3 - first) +
            -(26 : ℂ) / 12 * ((first : ℂ) ^ 3 - first) =
          ((D.rank : ℂ) - 26) / 12 * ((first : ℂ) ^ 3 - first) := by ring
        rw [← scalar, add_smul]
        abel
      · simp only [resonance, if_false, zero_smul, add_zero]

theorem critical_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (critical : D.rank = 26) (first second : ℤ) :
    totalMode D H first * totalMode D H second -
        totalMode D H second * totalMode D H first =
      ((first - second : ℤ) : ℂ) • totalMode D H (first + second) := by
  rw [virasoro D H leftInverse rightInverse, critical]
  norm_num

theorem translation_covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : State D) (mode : ℤ) :
    totalMode D H (-1) * ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) -
        ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) * totalMode D H (-1) =
      -(mode : ℂ) • ((LatticeBcGhostTensorStateField.stateField D state)[[mode - 1]]) := by
  rw [minus_one_eq_translation D H leftInverse rightInverse]
  exact LatticeBcGhostTensorStateField.stateField_covariance D state mode

theorem omega_creation (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    totalMode D H (-2) (LatticeBcGhostTensorStateField.vacuum D) = omega D H := by
  rw [← stress_modes, ← omega_field]
  exact LatticeBcGhostTensorStateField.stateField_creation D (omega D H)

theorem energy_covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : State D) (mode : ℤ) :
    totalMode D H 0 * ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) -
        ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) * totalMode D H 0 =
      ((LatticeBcGhostTensorStateField.stateField D (totalMode D H 0 state))[[mode]]) -
        ((mode : ℂ) + 1) • ((LatticeBcGhostTensorStateField.stateField D state)[[mode]]) := by
  let stateField := LatticeBcGhostTensorStateField.stateField D
  have modeZero : (stateField (omega D H))[[0]] = totalMode D H (-1) := by
    simpa only [stateField, totalMode, show (-1 : ℤ) + 1 = 0 by omega]
      using omega_modes D H (-1)
  have modeOne : (stateField (omega D H))[[1]] = totalMode D H 0 := by
    simpa only [stateField, totalMode, zero_add] using omega_modes D H 0
  have homogeneousLaw (parity : ℕ) (input : State D)
      (member : input ∈ LatticeBcGhostTensorStateField.homogeneous parity) :
      totalMode D H 0 * ((stateField input)[[mode]]) -
          ((stateField input)[[mode]]) * totalMode D H 0 =
        ((stateField (totalMode D H 0 input))[[mode]]) -
          ((mode : ℂ) + 1) • ((stateField input)[[mode]]) := by
    dsimp only [stateField] at *
    have closure := LatticeBcGhostTensorJacobi.stateField_residue_closure D 0 parity
      (omega D H) input 1 (omega_even D H) member
    have product : LatticeBcGhostTensorJacobi.mu D (omega D H) 1 input =
        totalMode D H 0 input := by
      unfold LatticeBcGhostTensorJacobi.mu
      rw [modeOne]
    rw [product] at closure
    have relation : ((stateField (totalMode D H 0 input))[[mode]]) =
        (totalMode D H 0 * ((stateField input)[[mode]]) -
          ((stateField input)[[mode]]) * totalMode D H 0) -
        (totalMode D H (-1) * ((stateField input)[[mode + 1]]) -
          ((stateField input)[[mode + 1]]) * totalMode D H (-1)) := by
      apply LinearMap.ext
      intro vector
      rw [closure]
      have residue := SuperStateFieldReconstruction.positive_residue_modes
        (SuperFieldProducts.koszul 0 parity) (stateField (omega D H))
        (stateField input) 1 mode vector
      dsimp only [stateField] at residue ⊢
      simpa only [pow_one, FieldNormalProductLocality.deltaEnd,
        LinearMap.coe_mk, AddHom.coe_mk, FieldNormalProductLocality.delta,
        SuperFieldProducts.superCommutator, SuperFieldProducts.koszul,
        zero_mul, pow_zero, one_smul, zero_add, Nat.cast_one, modeOne, modeZero,
        LinearMap.sub_apply] using residue
    rw [translation_covariance D H leftInverse rightInverse input (mode + 1),
      show mode + 1 - 1 = mode by omega] at relation
    dsimp only [stateField] at relation ⊢
    simp only [Int.cast_add, Int.cast_one, neg_smul, sub_neg_eq_add] at relation
    rw [relation]
    module
  have first := homogeneousLaw 0 (LatticeBcGhostTensorStateField.parityPart 0 state)
    (LatticeBcGhostTensorStateField.parityPart_mem 0 state)
  have second := homogeneousLaw 1 (LatticeBcGhostTensorStateField.parityPart 1 state)
    (LatticeBcGhostTensorStateField.parityPart_mem 1 state)
  dsimp only [stateField] at *
  have combined := congrArg₂ (fun left right : Module.End ℂ (State D) => left + right)
    first second
  have decomposition := LatticeBcGhostTensorStateField.parity_decomposition state
  have fieldDecomposition := congrArg
    (fun input : State D => (LatticeBcGhostTensorStateField.stateField D input)[[mode]])
    decomposition
  simp only [map_add, Pi.add_apply] at fieldDecomposition
  have energyDecomposition := congrArg
    (fun input : State D =>
      (LatticeBcGhostTensorStateField.stateField D (totalMode D H 0 input))[[mode]])
    decomposition
  simp only [map_add, Pi.add_apply] at energyDecomposition
  have leftCombined :
      (totalMode D H 0 * ((stateField (LatticeBcGhostTensorStateField.parityPart 0 state))[[mode]]) -
        ((stateField (LatticeBcGhostTensorStateField.parityPart 0 state))[[mode]]) * totalMode D H 0) +
      (totalMode D H 0 * ((stateField (LatticeBcGhostTensorStateField.parityPart 1 state))[[mode]]) -
        ((stateField (LatticeBcGhostTensorStateField.parityPart 1 state))[[mode]]) * totalMode D H 0) =
      totalMode D H 0 * ((stateField state)[[mode]]) -
        ((stateField state)[[mode]]) * totalMode D H 0 := by
    rw [← fieldDecomposition, add_mul, mul_add]
    abel
  rw [leftCombined] at combined
  rw [combined]
  rw [← energyDecomposition, ← fieldDecomposition, smul_add]
  abel

theorem omega_weight_two (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1) :
    totalMode D H 0 (omega D H) = (2 : ℂ) • omega D H := by
  have relation := congrArg
    (fun operator : Module.End ℂ (State D) => operator (LatticeBcGhostTensorStateField.vacuum D))
    (virasoro D H leftInverse rightInverse 0 (-2))
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, omega_creation,
    vacuum_annihilation D H 0 (by omega), map_zero, sub_zero, LinearMap.add_apply,
    LinearMap.smul_apply, show (0 : ℤ) - -2 = 2 by omega,
    show (0 : ℤ) + -2 = -2 by omega, show (-2 : ℤ) ≠ 0 by omega,
    if_false, zero_smul, LinearMap.zero_apply, add_zero, Int.cast_ofNat] using relation

theorem omega_positive_action (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (mode : ℤ) (positive : 1 ≤ mode) :
    totalMode D H mode (omega D H) =
      if mode = 2 then (((D.rank : ℂ) - 26) / 2) •
        LatticeBcGhostTensorStateField.vacuum D else 0 := by
  have relation := congrArg
    (fun operator : Module.End ℂ (State D) => operator (LatticeBcGhostTensorStateField.vacuum D))
    (virasoro D H leftInverse rightInverse mode (-2))
  have modeVacuum := vacuum_annihilation D H mode (by omega)
  have shiftedVacuum := vacuum_annihilation D H (mode + -2) (by omega)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, omega_creation,
    modeVacuum, map_zero, sub_zero, LinearMap.add_apply, LinearMap.smul_apply,
    shiftedVacuum, smul_zero, zero_add, Module.End.one_eq_id, LinearMap.id_apply] at relation
  by_cases centralMode : mode = 2
  · subst mode
    simp only [ite_true]
    norm_num at relation
    convert relation using 1
    congr 1
    ring
  · have nonresonant : mode + -2 ≠ 0 := by omega
    simpa only [if_neg nonresonant, if_neg centralMode, zero_smul] using relation

end

end D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostTotalConformal
