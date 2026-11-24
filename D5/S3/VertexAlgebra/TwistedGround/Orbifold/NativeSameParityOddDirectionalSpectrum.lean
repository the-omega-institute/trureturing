/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityOddDirectionalSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityOddDirectionalSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native rank-one zero modes on the first Leech oscillator tensors. -/

import D5.S3.VertexAlgebra.Lattice.LeechFrame.LeechHalfFockQuadraticTransport
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeQuadraticZhuCurrent

/-!
Abe, arXiv:math/9907120v1, (2.11), Table 1 and §4.2.
The normalized norm-four frame supplies the selected and spectator directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity.OddDirectional

open ActualLeechHyperbolic (leechData)
open ActualLeechHalfFockCurrents (orthonormalBasis orthonormalBasis_pairing)
open ActualLeechHalfFockTensorSplit ActualLeechHalfFockQuadraticTransport
open LatticeLightConeCoordinates (E g lin lin_homogeneous)
open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCurrentCorrection LatticeHalfFock LatticeHalfFockCorrectedConformal
open Lattice.ActualZhuCurrentRelations (single_weighted_grade)
open NativeOddTwistedIntertwiner (Twisted leechUnit twistedTop fixedAction fixedTopZero
  quadraticOddTopOscillator)
open MvPolynomial

open private fixedAction_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private polynomialEquiv_symm_X from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

noncomputable section

local notation "ℒ" => leechData
local notation "G₀" => ActualGround ℒ leechUnit
local notation "T₀" => ActualTensor ℒ leechUnit
local notation "T₁" => twistedTop ℒ leechUnit true

local instance : AddCommGroup T₁ :=
  @Submodule.addCommGroup ℂ (Twisted ℒ leechUnit true) _ _ _ T₁

private abbrev neutral : Oscillator ℒ →ₗ[ℂ] Carrier ℒ := Finsupp.lsingle 0

private theorem sigma_lin (n : ℕ) (u : E ℒ) : sigma ℒ (lin n u) = -lin n u := by
  classical
  change sigma ℒ (∑ k, u k • X (k, n)) = -(∑ k, u k • X (k, n))
  simp [sigma_smul, sigma_X]

private theorem lin_weight (n : ℕ) (u : E ℒ) :
    IsWeightedHomogeneous (oscillatorWeight ℒ) (lin n u) (n + 1) :=
  lin_homogeneous n u

private def fixedNeutral (p : Oscillator ℒ) (hp : sigma ℒ p = p) : FixedCarrier ℒ :=
  ⟨neutral p, (mem_fixedSpace ℒ _).mpr (by
    change thetaLinear ℒ (Finsupp.single 0 p) = _
    rw [theta_single, neg_zero, hp, Finsupp.lsingle_apply])⟩

private theorem fixedNeutral_grade (p : Oscillator ℒ) (hp : sigma ℒ p = p)
    (n : ℕ) (hn : IsWeightedHomogeneous (oscillatorWeight ℒ) p n) :
    (fixedNeutral p hp).val ∈ grade ℒ (n : ℤ) := by
  simpa only [fixedNeutral, Finsupp.lsingle_apply, chargeEnergy_zero, zero_add] using
    single_weighted_grade ℒ 0 p n hn

/-- The rank-one stress in the selected unit frame direction. -/
def leechRankOneOmega (c : FrameIndex) : FixedCarrier ℒ :=
  fixedNeutral ((1 / 2 : ℂ) • (lin 0 (orthonormalBasis c) * lin 0 (orthonormalBasis c)))
    (by simp [sigma_smul, map_mul, sigma_lin])

/-- The transported unit-current state h(-3)h(-1)1. -/
def leechAbeState (c : FrameIndex) : FixedCarrier ℒ :=
  fixedNeutral (lin 2 (orthonormalBasis c) * lin 0 (orthonormalBasis c))
    (by simp [map_mul, sigma_lin])

theorem leechRankOneOmega_grade (c : FrameIndex) : (leechRankOneOmega c).val ∈ grade ℒ 2 := by
  apply fixedNeutral_grade
  rw [MvPolynomial.smul_eq_C_mul]
  exact ((lin_weight 0 _).mul (lin_weight 0 _)).C_mul _

theorem leechAbeState_grade (c : FrameIndex) : (leechAbeState c).val ∈ grade ℒ 4 :=
  fixedNeutral_grade _ _ 4 ((lin_weight 2 _).mul (lin_weight 0 _))

abbrev firstOscillator (u : E ℒ) : G₀ →ₗ[ℂ] T₁ :=
  ∑ k, u k • quadraticOddTopOscillator ℒ leechUnit k

theorem firstOscillator_val (u : E ℒ) (x : G₀) :
    (firstOscillator u x).val.val = (lin 0 u : Oscillator ℒ) ⊗ₜ[ℂ] x := by
  let A : T₁ →ₗ[ℂ] T₀ :=
    ((HalfFock.LatticeHalfFockParityField.paritySpace ℒ leechUnit
      (NativeOddTwistedIntertwiner.paritySign true)).subtype).comp
      (twistedTop ℒ leechUnit true).subtype
  change A (firstOscillator u x) = _
  simp only [firstOscillator, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  change (∑ k, u k • ((X (k, 0) : Oscillator ℒ) ⊗ₜ[ℂ] x)) =
    (∑ k, u k • (X (k, 0) : Oscillator ℒ)) ⊗ₜ[ℂ] x
  symm
  let put := (TensorProduct.mk ℂ (Oscillator ℒ) G₀).flip x
  change put (∑ k, u k • X (k,0)) = ∑ k, u k • put (X (k,0))
  simp only [map_sum, map_smul]

abbrev frameOscillator (c : FrameIndex) : G₀ →ₗ[ℂ] T₁ :=
  firstOscillator (orthonormalBasis c)

private theorem split_frameOscillator (c d : FrameIndex) (x : G₀) :
    nativeTensorSplit c leechUnit (frameOscillator d x).val.val =
      if h : d = c then ((X 0 : SinglePolynomial) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] x
      else ((1 : SinglePolynomial) ⊗ₜ[ℂ] X (⟨d, h⟩, 0)) ⊗ₜ[ℂ] x := by
  rw [firstOscillator_val]
  have hcoord :
      LatticeLightConeCoordinates.polynomialEquiv orthonormalBasis (lin 0 (orthonormalBasis d)) =
        X (d, 0) := by
    rw [← polynomialEquiv_symm_X orthonormalBasis d 0, AlgEquiv.apply_symm_apply]
  change (split c (LatticeLightConeCoordinates.polynomialEquiv orthonormalBasis
    (lin 0 (orthonormalBasis d))) ⊗ₜ[ℂ] x) = _
  rw [hcoord]
  split_ifs with h
  · subst d
    rw [split_X_single]
  · exact congrArg (fun P : SplitPolynomial c => P ⊗ₜ[ℂ] x)
      (split_X_complement c ⟨d, h⟩ 0)

private theorem singleCurrent_one_nonneg (k : ℤ) (hk : 0 ≤ k) :
    singleCurrent k 1 = 0 := by
  lift k to ℕ using hk
  simp [singleCurrent, oscillatorMode, Derivation.map_one_eq_zero]

private theorem singleCurrent_X_nonneg (k : ℤ) (hk : 1 ≤ k) :
    singleCurrent k (X 0) = 0 := by
  have hpos : 0 ≤ k := by omega
  lift k to ℕ using hpos
  have hn : k ≠ 0 := by omega
  simp [singleCurrent, oscillatorMode, pderiv_X, Pi.single_apply, hn, Ne.symm hn]

private theorem singleQuadratic_vacuum (a b : ℕ) :
    singleQuadraticMode a b 0 1 = pairScalar (a+1) (b+1) • (1 : SinglePolynomial) := by
  rw [singleQuadraticMode_interval a b 0 1 0 (singleCurrent_one_nonneg)]
  have hbox : modeInterval 0 0 = ∅ := by
    unfold modeInterval
    exact Finset.Icc_eq_empty (by norm_num)
  simp [hbox]

private theorem singleQuadratic_first (a b : ℕ) :
    singleQuadraticMode a b 0 (X 0) =
      (((jetScalar a (-1) * jetScalar b 0 + jetScalar a 0 * jetScalar b (-1)) / 2) +
        pairScalar (a+1) (b+1)) • (X 0 : SinglePolynomial) := by
  rw [singleQuadraticMode_interval a b 0 (X 0) 1 singleCurrent_X_nonneg]
  have hbox : modeInterval 0 1 = ({-1, 0} : Finset ℤ) := by decide
  rw [hbox, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hnormal : normalProduct singleCurrent singleCurrent (-1) 0 (X 0) =
      (1 / 2 : ℂ) • (X 0 : SinglePolynomial) := by
    norm_num [normalProduct, singleCurrent, oscillatorMode, pderiv_X, Pi.single_apply, smul_smul]
    change X (0 : ℕ) * 1 = X 0
    exact mul_one _
  simp only [show (0 : ℤ) - (-1) - 1 = 0 by decide, show (0 : ℤ) - 0 - 1 = -1 by decide,
    if_true, hnormal]
  rw [show normalProduct singleCurrent singleCurrent 0 (-1) (X 0) =
      normalProduct singleCurrent singleCurrent (-1) 0 (X 0) by rfl, hnormal]
  module

/-- The full corrected quadratic coefficient on the selected and spectator inputs. -/
theorem quadratic_on_first (c d : FrameIndex) (x : G₀) (a b : ℕ) :
    (correctedField ℒ leechUnit (frameQuadraticSource c a b)).coeff
        (doubledExponent a b 0) (frameOscillator d x).val.val =
      (pairScalar (a+1) (b+1) + if d = c then
        (jetScalar a (-1) * jetScalar b 0 + jetScalar a 0 * jetScalar b (-1)) / 2
        else 0) • (frameOscillator d x).val.val := by
  let S := nativeTensorSplit c leechUnit
  apply S.injective
  have h := LinearMap.congr_fun (nativeTensorSplit_quadratic_mode c leechUnit a b 0)
    (S (frameOscillator d x).val.val)
  simp only [S, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at h
  rw [h, map_smul, split_frameOscillator]
  by_cases hd : d = c
  · subst d
    simp only [dite_true, ite_true, dif_pos (show c = c from rfl),
      if_pos (show c = c from rfl), onSingle, TensorProduct.map_tmul, LinearMap.id_apply,
      singleQuadratic_first, TensorProduct.smul_tmul']
    <;> rw [add_comm]
  · simp only [dif_neg hd, if_neg hd, add_zero, onSingle, TensorProduct.map_tmul, LinearMap.id_apply,
      singleQuadratic_vacuum, TensorProduct.smul_tmul']

private theorem fixedTopZero_ambient (a : FixedCarrier ℒ) (n : ℕ)
    (ha : a.val ∈ grade ℒ (n : ℤ)) (v : T₁) :
    (fixedTopZero true a n ha v).val.val =
      (correctedField ℒ leechUnit a.val).coeff (-2 * (n : ℤ)) v.val.val := by
  change (fixedAction true a ((n : ℤ)-1) v.val).val = _
  rw [fixedAction_val, show -2 * ((n : ℤ)-1)-2 = -2 * (n : ℤ) by ring]

theorem leechRankOneOmega_odd_zeroMode (c d : FrameIndex) (x : G₀) :
    fixedTopZero true (leechRankOneOmega c) 2 (leechRankOneOmega_grade c)
      (frameOscillator d x) =
        (if d = c then (9 / 16 : ℂ) else 1 / 16) • frameOscillator d x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fixedTopZero_ambient]
  let v : T₀ := (frameOscillator d x).val.val
  let E := ((coefficientAt ℒ leechUnit (-4) v).comp (correctedField ℒ leechUnit)).comp neutral
  let w := lin 0 (orthonormalBasis c) * lin 0 (orthonormalBasis c)
  change E ((1 / 2 : ℂ) • w) = (if d = c then (9 / 16 : ℂ) else 1 / 16) • v
  have h := quadratic_on_first c d x 0 0
  change E w = _ at h
  rw [map_smul, h, smul_smul]
  congr 1
  by_cases hd : d = c <;>
    norm_num [hd, jetScalar, pairScalar, halfBinomial, Finset.prod_range_succ]

theorem leechAbeState_odd_zeroMode (c d : FrameIndex) (x : G₀) :
    fixedTopZero true (leechAbeState c) 4 (leechAbeState_grade c) (frameOscillator d x) =
      (if d = c then (159 / 128 : ℂ) else 15 / 128) • frameOscillator d x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fixedTopZero_ambient]
  let v : T₀ := (frameOscillator d x).val.val
  let q := correctedField ℒ leechUnit (frameQuadraticSource c 2 0)
  change q.coeff (-8) v = (if d = c then (159 / 128 : ℂ) else 15 / 128) • v
  have h := quadratic_on_first c d x 2 0
  change q.coeff (-8) v = _ at h
  rw [h]
  congr 1
  by_cases hd : d = c <;>
    norm_num [hd, jetScalar, pairScalar, halfBinomial, Finset.prod_range_succ]

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity.OddDirectional
