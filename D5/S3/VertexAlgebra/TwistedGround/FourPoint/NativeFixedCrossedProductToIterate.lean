/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedCrossedProductToIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFixedCrossedProductToIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native fixed-channel radial D summation and upper transport of the finite detector. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion

/-! Native fixed-channel D summation and upper transport on the doubled root cover. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeGeneratingFieldLocality (Carrier Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor groundRank)
open LatticeHalfFockCorrectedField (correctedField correctedField_theta)
open LatticeHalfFockGradedTrace (OddMonomial actualGrade actualAmbientBasis)
open LatticeInvolution (FixedCarrier fixedSpace mem_fixedSpace)
open LatticeTwistedGroundRealization (Half)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit paritySign)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeFixedPairField (nu nu_coeff_odd_zero)
open Orbifold.NativeOddUpperRightSkew (lowering)
open Orbifold.NativeFixedUpperRightSkew
  (rightField rightField_coeff rightField_odd_zero R_pairing_finite)
open NativeFixedPairAIterate (fixedAIterateCoeff fixedAIterate_hasSum fixedASlitSewn)
open NativeFixedPairFourPoint (nu_fourPoint_off_right_grade)

open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private cancel_lowering_orders lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private grade_mod_two projected_basis_tensor from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private norm_one_sub_lt_iff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s

/-- The independent doubled modes of the actual iterate through the fixed space. -/
def aJointTerm (s t : Bool) (P Q : State s) (R S : State t)
    (dR zR : ℂ) (i : ℤ × ℤ) : ℂ :=
  actualForm ℒ leechUnit S.val
    ((correctedField ℒ leechUnit ((nu s P).coeff i.1 Q).val).coeff i.2 R.val) *
      (dR ^ i.1 * zR ^ i.2)

/-- The independent doubled modes of the actual fixed D product in order
(P, R, Q, S). The pair is (P, Q) and the right field is attached to R. -/
def dJointTerm (s t : Bool) (P Q : State s) (R S : State t)
    (xR zR : ℂ) (i : ℤ × ℤ) : ℂ :=
  actualForm ℒ leechUnit S.val
    ((rightField ℒ leechUnit t R).coeff i.2 ((nu s P).coeff i.1 Q)).val *
      (xR ^ i.1 * zR ^ i.2)

/-- The scalar of the ellth lowering power in detector translation by x. -/
def translationWeight (x : ℂ) (ell : ℕ) : ℂ :=
  x ^ ell * (ell.factorial : ℂ)⁻¹

/-- The finite action of the stress lowering exponential on a detector of grade N. -/
def translatedDetector (t : Bool) (N : ℕ) (x : ℂ) (S : State t) : State t :=
  ∑ ell ∈ Finset.range (N / 2 + 1), translationWeight x ell • (L₁ t ^ ell) S

/-- Lower the outer doubled exponent by the translation order 2 * ell. -/
def shiftOuterMode (ell : ℕ) : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
  (Equiv.refl ℤ).prodCongr (Equiv.subRight (2 * (ell : ℤ)))

private theorem fixed_odd_mode_zero (a : FixedCarrier ℒ) (e : ℤ) (he : Odd e)
    (v : ActualTensor ℒ leechUnit) :
    (correctedField ℒ leechUnit a.val).coeff e v = 0 := by
  have hc := LinearMap.congr_fun (correctedField_theta ℒ leechUnit a.val e) v
  rw [(mem_fixedSpace ℒ a.val).mp a.property, he.neg_one_zpow] at hc
  simp only [neg_one_smul] at hc
  have hz : (2 : ℂ) • (correctedField ℒ leechUnit a.val).coeff e v = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hc
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem aJointTerm_neg_outer_root (s t : Bool) (P Q : State s) (R S : State t)
    (dR zR : ℂ) (i : ℤ × ℤ) :
    aJointTerm s t P Q R S dR (-zR) i = aJointTerm s t P Q R S dR zR i := by
  by_cases he : Even i.2
  · simp only [aJointTerm, he.neg_zpow]
  · have hz := fixed_odd_mode_zero ((nu s P).coeff i.1 Q) i.2
      (Int.not_even_iff_odd.mp he) R.val
    simp only [aJointTerm, hz, map_zero, zero_mul]

/-- The fixed upper D mode is a finite sum of shifted A modes. The right
root enters A as I * zR and each lowering order subtracts 2 * ell. -/
theorem dJointTerm_eq_sum_shifted_aJointTerm (s t : Bool) (N : ℕ)
    (P Q : State s) (R S : State t) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hz : zR ≠ 0) (i : ℤ × ℤ) :
    dJointTerm s t P Q R S xR zR i =
      ∑ ell ∈ Finset.range (N / 2 + 1), translationWeight (zR ^ 2) ell *
        aJointTerm s t P Q R ((L₁ t ^ ell) S) xR (I * zR) (shiftOuterMode ell i) := by
  rcases i with ⟨j, e⟩
  let a : FixedCarrier ℒ := (nu s P).coeff j Q
  change actualForm ℒ leechUnit S.val ((rightField ℒ leechUnit t R).coeff e a).val *
      (xR ^ j * zR ^ e) =
    ∑ ell ∈ Finset.range (N / 2 + 1), translationWeight (zR ^ 2) ell *
      (actualForm ℒ leechUnit ((L₁ t ^ ell) S).val
        ((correctedField ℒ leechUnit a.val).coeff (e - 2 * (ell : ℤ)) R.val) *
          (xR ^ j * (I * zR) ^ (e - 2 * (ell : ℤ))))
  by_cases he : Even e
  · obtain ⟨k, hk⟩ := he
    let m : ℤ := -k - 1
    have hm : e = -2 * m - 2 := by dsimp [m]; omega
    rw [hm, rightField_coeff ℒ leechUnit t m R a, R_pairing_finite ℒ leechUnit t m N R a
      S.val hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ell _
    have hmode : -2 * (m + (ell : ℤ)) - 2 = (-2 * m - 2) - 2 * (ell : ℤ) := by ring
    have hp : zR ^ (-2 * m - 2) =
        (zR ^ (2 : ℕ)) ^ ell * zR ^ ((-2 * m - 2) - 2 * (ell : ℤ)) := by
      have hexp : ((2 * ell : ℕ) : ℤ) + ((-2 * m - 2) - 2 * (ell : ℤ)) =
          -2 * m - 2 := by
        push_cast
        ring
      rw [← pow_mul, ← zpow_natCast zR (2 * ell), ← zpow_add₀ hz, hexp]
    rw [hmode, hp, lowering_pow_val, mul_zpow, translationWeight]
    ring
  · rw [rightField_odd_zero ℒ leechUnit t e (Int.not_even_iff_odd.mp he), Submodule.coe_zero,
      map_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ell _
    have he' : Odd (e - 2 * (ell : ℤ)) := by
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
      exact ⟨k - (ell : ℤ), by omega⟩
    rw [fixed_odd_mode_zero a _ he', map_zero, zero_mul, mul_zero]

private theorem dJointTerm_translatedDetector (s t : Bool) (N : ℕ)
    (P Q : State s) (R S : State t) (x : ℂ) (xR zR : ℂ) (i : ℤ × ℤ) :
    dJointTerm s t P Q R (translatedDetector t N x S) xR zR i =
      ∑ ell ∈ Finset.range (N / 2 + 1), translationWeight x ell *
        dJointTerm s t P Q R ((L₁ t ^ ell) S) xR zR i := by
  let v := ((rightField ℒ leechUnit t R).coeff i.2 ((nu s P).coeff i.1 Q)).val
  let f : State t →ₗ[ℂ] ℂ :=
    ((actualForm ℒ leechUnit).flip v).comp (paritySpace ℒ leechUnit (paritySign t)).subtype
  change f (translatedDetector t N x S) * (xR ^ i.1 * zR ^ i.2) = _
  rw [translatedDetector, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ell _
  rw [map_smul, smul_eq_mul]
  change (translationWeight x ell * f ((L₁ t ^ ell) S)) * _ =
    translationWeight x ell * (f ((L₁ t ^ ell) S) * _)
  exact mul_assoc _ _ _

/-- At each transported mode, the kth detector term is evaluated at the outer
exponent shifted by 2k. Translation then cancels at the upper root I * zR. -/
theorem dJointTerm_upper_eq_aJointTerm (s t : Bool) (N : ℕ)
    (P Q : State s) (R S : State t) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {dR zR : ℂ} (hz : zR ≠ 0) (i : ℤ × ℤ) :
    (∑ k ∈ Finset.range (N / 2 + 1), translationWeight (zR ^ 2) k *
      dJointTerm s t P Q R ((L₁ t ^ k) S) dR (I * zR) (shiftOuterMode k i)) =
      aJointTerm s t P Q R S dR zR i := by
  have hzI : I * zR ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hturn : I * (I * zR) = -zR := by rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hsq : (I * zR) ^ (2 : ℕ) = -(zR ^ 2) := by
    rw [mul_pow, Complex.I_sq, neg_one_mul]
  let x : ℂ := zR ^ 2
  let F (r : ℕ) := (-x) ^ r *
    aJointTerm s t P Q R ((L₁ t ^ r) S) dR zR (shiftOuterMode r i)
  have hF : F 0 = aJointTerm s t P Q R S dR zR i := by
    rcases i with ⟨j, e⟩
    simp [F, shiftOuterMode, Equiv.prodCongr_apply, Equiv.subRight_apply]
  rw [← hF, ← cancel_lowering_orders (N / 2) F]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hgrade := lowered_grade (s := t) (u := S) hS hk'
  rw [dJointTerm_eq_sum_shifted_aJointTerm s t (N - 2 * k) P Q R ((L₁ t ^ k) S) hgrade hzI,
    show (N - 2 * k) / 2 = N / 2 - k by omega, Finset.mul_sum, hturn, hsq]
  apply Finset.sum_congr rfl
  intro ell _
  rw [aJointTerm_neg_outer_root, ← Module.End.mul_apply, ← pow_add, add_comm ell k]
  have hshift : shiftOuterMode ell (shiftOuterMode k i) = shiftOuterMode (k + ell) i := by
    rcases i with ⟨j, e⟩
    apply Prod.ext
    · rfl
    · change e - 2 * (k : ℤ) - 2 * (ell : ℤ) = e - 2 * ((k + ell : ℕ) : ℤ)
      push_cast
      ring
  rw [hshift]
  change translationWeight x k *
      (translationWeight (-x) ell *
        aJointTerm s t P Q R ((L₁ t ^ (k + ell)) S) dR zR (shiftOuterMode (k + ell) i)) = _
  have hp : (-1 : ℂ) ^ k * (-x) ^ k = x ^ k := by rw [← mul_pow, neg_one_mul, neg_neg]
  dsimp only [translationWeight, F]
  rw [pow_add (-x) k ell]
  calc
    _ = ((-1 : ℂ) ^ k * (-x) ^ k) * (k.factorial : ℂ)⁻¹ *
          ((-x) ^ ell * (ell.factorial : ℂ)⁻¹) *
          aJointTerm s t P Q R ((L₁ t ^ (k + ell)) S) dR zR (shiftOuterMode (k + ell) i) := by
      rw [hp]
      ring
    _ = _ := by ring

private theorem fixed_a_off_diagonal (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + K)) (j e : ℤ)
    (he : e ≠ (N : ℤ) - L - (j + ((M : ℤ) + K + 6))) :
    actualForm ℒ leechUnit S.val
      ((correctedField ℒ leechUnit ((nu s P).coeff j Q).val).coeff e R.val) = 0 := by
  by_cases hj : Even j
  · obtain ⟨k, hk⟩ := hj
    obtain ⟨m, hm⟩ := hpar
    rw [show j = -2 * (-k - 1) - 2 by omega]
    exact nu_fourPoint_off_right_grade s M K L N (-k - 1) (m + k + 3) e
      P Q R.val S.val hP hQ hR hS (by omega) (by omega)
  · simp [nu_coeff_odd_zero s j P Q (Int.not_even_iff_odd.mp hj)]

private theorem a_joint_from_diagonal (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hpar : Even ((M : ℤ) + K)) {zR ξ value : ℂ} (hz : zR ≠ 0)
    (hsum : HasSum (fun j : ℤ => fixedAIterateCoeff s M K L N j P Q R.val S.val * ξ ^ j)
      value) :
    HasSum (aJointTerm s t P Q R S (zR * ξ) zR)
      (zR ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) * value) := by
  let d : ℤ := (N : ℤ) - L - ((M : ℤ) + K + 6)
  let modes (j : ℤ) : ℤ × ℤ := (j, (N : ℤ) - L - (j + ((M : ℤ) + K + 6)))
  have hinj : Function.Injective modes := fun _ _ h => congrArg Prod.fst h
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range modes) :
      aJointTerm s t P Q R S (zR * ξ) zR i = 0 := by
    rcases i with ⟨j, e⟩
    have he : e ≠ (modes j).2 := fun h => hi ⟨j, Prod.ext rfl h.symm⟩
    rw [aJointTerm, fixed_a_off_diagonal s t M K L N P Q R S hP hQ hR hS hpar j e he,
      zero_mul]
  apply (hinj.hasSum_iff hoff).mp
  refine (hsum.mul_left (zR ^ d)).congr_fun ?_
  intro j
  have hpow : (zR * ξ) ^ j * zR ^ (modes j).2 = zR ^ d * ξ ^ j := by
    rw [mul_zpow]
    calc
      _ = (zR ^ j * zR ^ (modes j).2) * ξ ^ j := by ring
      _ = _ := by
        rw [← zpow_add₀ hz, show j + (modes j).2 = d by dsimp [modes, d]; ring]
  change fixedAIterateCoeff s M K L N j P Q R.val S.val *
    ((zR * ξ) ^ j * zR ^ (modes j).2) = _
  rw [hpow]
  ring

/-- The literal fixed A double series on its radial domain, with the physical
outer-root power restored from the one-index Laurent sum. -/
theorem fixed_a_joint_hasSum (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (p q r b : Oscillator ℒ) (u v w c : ActualGround ℒ leechUnit)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    (hPu : P.val = p ⊗ₜ[ℂ] u) (hQv : Q.val = q ⊗ₜ[ℂ] v)
    (hRw : R.val = r ⊗ₜ[ℂ] w) (hSc : S.val = b ⊗ₜ[ℂ] c)
    (hpar : Even ((M : ℤ) + K))
    {dR zR : ℂ} (hd : dR ≠ 0) (hr : ‖dR‖ < ‖zR‖) :
    let ξ := dR / zR
    HasSum (aJointTerm s t P Q R S dR zR)
      (zR ^ ((N : ℤ) - L - ((M : ℤ) + K + 6)) *
        (ξ ^ (-((M : ℤ) + K + 6)) * fixedASlitSewn M K p q r b u v w c (-(ξ ^ 2)))) := by
  have hz : zR ≠ 0 := norm_pos_iff.mp ((norm_nonneg dR).trans_lt hr)
  have hξ : ‖dR / zR‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz)]
    exact hr
  have hsum := fixedAIterate_hasSum s M K L N P Q p q r b u v w c hP hQ hPu hQv
    (hRw ▸ hR) (hSc ▸ hS) hpar (div_ne_zero hd hz) hξ
  rw [← hRw, ← hSc] at hsum
  have h := a_joint_from_diagonal s t M K L N P Q R S hP hQ hR hS hpar hz hsum
  simpa only [mul_div_cancel₀ dR hz] using h

private abbrev FourLinear (s t : Bool) :=
  State s →ₗ[ℂ] State s →ₗ[ℂ] State t →ₗ[ℂ] State t →ₗ[ℂ] ℂ

private def aModeLinear (s t : Bool) (dR zR : ℂ) (i : ℤ × ℤ) : FourLinear s t :=
  let inner : State s →ₗ[ℂ] State s →ₗ[ℂ] FixedCarrier ℒ :=
    ((LinearMap.proj i.1).comp HVertexOperator.coeff).comp (nu s)
  let outer : Carrier ℒ →ₗ[ℂ] ActualTensor ℒ leechUnit →ₗ[ℂ] ActualTensor ℒ leechUnit :=
    ((LinearMap.proj i.2).comp HVertexOperator.coeff).comp (correctedField ℒ leechUnit)
  let outer' : FixedCarrier ℒ →ₗ[ℂ] State t →ₗ[ℂ] ActualTensor ℒ leechUnit :=
    outer.compl₁₂ (fixedSpace ℒ).subtype
    (paritySpace ℒ leechUnit (paritySign t)).subtype
  let pair : ActualTensor ℒ leechUnit →ₗ[ℂ] State t →ₗ[ℂ] ℂ :=
    (actualForm ℒ leechUnit).flip.compl₂
    (paritySpace ℒ leechUnit (paritySign t)).subtype
  (dR ^ i.1 * zR ^ i.2) • inner.compr₂ (outer'.compr₂ pair)

private theorem aModeLinear_apply (s t : Bool) (dR zR : ℂ) (i : ℤ × ℤ)
    (P Q : State s) (R S : State t) :
    aModeLinear s t dR zR i P Q R S = aJointTerm s t P Q R S dR zR i :=
  mul_comm _ _

private abbrev BasisIndex := OddMonomial ℒ × Half (groundRank ℒ leechUnit)

/-- Finite expansion in the actual projected homogeneous basis supplies
double-mode A summability for both same-parity pair fields. -/
theorem fixed_a_joint_summable_of_homogeneous (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {dR zR : ℂ} (hd : dR ≠ 0) (hr : ‖dR‖ < ‖zR‖) :
    Summable (aJointTerm s t P Q R S dR zR) := by
  classical
  by_cases hzero : P = 0 ∨ Q = 0
  · change Summable (fun i => aJointTerm s t P Q R S dR zR i)
    rcases hzero with rfl | rfl <;> simp [← aModeLinear_apply s t]
  push Not at hzero
  have hM := grade_mod_two (s := s) (u := P) hP hzero.1
  have hK := grade_mod_two (s := s) (u := Q) hQ hzero.2
  have hpar : Even ((M : ℤ) + K) := by
    rw [Int.even_iff]
    cases s <;> simp at hM hK <;> omega
  let basis : Module.Basis BasisIndex ℂ (ActualTensor ℒ leechUnit) :=
    actualAmbientBasis ℒ leechUnit
  let cp := basis.repr P.val
  let cq := basis.repr Q.val
  let cr := basis.repr R.val
  let cs := basis.repr S.val
  let F := aModeLinear s t dR zR
  have hexpand (i : ℤ × ℤ) :
      aJointTerm s t P Q R S dR zR i =
        ∑ a ∈ cp.support, cp a * (∑ b ∈ cq.support, cq b * (∑ c ∈ cr.support,
          cr c * (∑ e ∈ cs.support, cs e * F i (project s (basis a)) (project s (basis b))
            (project t (basis c)) (project t (basis e))))) := by
    rw [← aModeLinear_apply s t]
    conv_lhs =>
      rw [← sum_projectedBasis s P]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis s Q]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis t R]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sum_projectedBasis t S]
      simp only [map_sum, map_smul, smul_eq_mul]
  have hBasis (a : BasisIndex) (ha : a ∈ cp.support) (b : BasisIndex) (hb : b ∈ cq.support)
      (c : BasisIndex) (hc : c ∈ cr.support) (e : BasisIndex) (he : e ∈ cs.support) :
      Summable (fun i => F i (project s (basis a)) (project s (basis b))
        (project t (basis c)) (project t (basis e))) := by
    obtain ⟨hPa, p, u, hPu⟩ := projected_basis_tensor s M P hP a ha
    obtain ⟨hQb, q, v, hQv⟩ := projected_basis_tensor s K Q hQ b hb
    obtain ⟨hRc, r, w, hRw⟩ := projected_basis_tensor t L R hR c hc
    obtain ⟨hSe, bOsc, d, hSd⟩ := projected_basis_tensor t N S hS e he
    simp only [F, aModeLinear_apply]
    exact (fixed_a_joint_hasSum s t M K L N _ _ _ _ p q r bOsc u v w d
      hPa hQb hRc hSe hPu hQv hRw hSd hpar hd hr).summable
  have h := hasSum_sum (s := cp.support) fun a ha => HasSum.mul_left (cp a) <|
    hasSum_sum (s := cq.support) fun b hb => HasSum.mul_left (cq b) <|
    hasSum_sum (s := cr.support) fun c hc => HasSum.mul_left (cr c) <|
    hasSum_sum (s := cs.support) fun e he => (hBasis a ha b hb c hc e he).hasSum.mul_left (cs e)
  exact (h.congr_fun hexpand).summable

/-- The actual fixed D series sums to the A iterate with outer root I * zR,
paired against the finitely translated detector. -/
theorem fixed_d_joint_hasSum_crossed_a (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {xR zR : ℂ} (hx : xR ≠ 0) (hz : zR ≠ 0) (hr : ‖xR‖ < ‖zR‖) :
    HasSum (dJointTerm s t P Q R S xR zR)
      (∑ ell ∈ Finset.range (N / 2 + 1), translationWeight (zR ^ 2) ell *
        (∑' i, aJointTerm s t P Q R ((L₁ t ^ ell) S) xR (I * zR) i)) := by
  have hrad : ‖xR‖ < ‖I * zR‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hr
  have hsum (ell : ℕ) (hell : ell ∈ Finset.range (N / 2 + 1)) :
      HasSum (fun i => translationWeight (zR ^ 2) ell *
        aJointTerm s t P Q R ((L₁ t ^ ell) S) xR (I * zR) (shiftOuterMode ell i))
        (translationWeight (zR ^ 2) ell *
          (∑' i, aJointTerm s t P Q R ((L₁ t ^ ell) S) xR (I * zR) i)) := by
    have hell' : ell ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hell)
    have hdesc := lowered_grade (s := t) (u := S) hS hell'
    have hA := (fixed_a_joint_summable_of_homogeneous s t M K L (N - 2 * ell)
      P Q R ((L₁ t ^ ell) S) hP hQ hR hdesc hx hrad).hasSum
    exact ((shiftOuterMode ell).hasSum_iff.mpr hA).mul_left _
  exact (hasSum_sum (s := Finset.range (N / 2 + 1)) hsum).congr_fun
    (dJointTerm_eq_sum_shifted_aJointTerm s t N P Q R S hS hz)

/-- A native A sum transfers to the upper D series after
(2,3). The kth detector summand is reindexed by its own outer-mode shift. -/
theorem upper_fixed_d_hasSum_of_a (s t : Bool) (N : ℕ)
    (P Q : State s) (R S : State t) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {dR zR value : ℂ} (hz : zR ≠ 0)
    (hLowered : ∀ k ∈ Finset.range (N / 2 + 1),
      Summable (dJointTerm s t P Q R ((L₁ t ^ k) S) dR (I * zR)))
    (hA : HasSum (aJointTerm s t P Q R S dR zR) value) :
    HasSum (dJointTerm s t P Q R (translatedDetector t N (zR ^ 2) S) dR (I * zR)) value := by
  let dMode (k : ℕ) : ℤ × ℤ → ℂ :=
    dJointTerm s t P Q R ((L₁ t ^ k) S) dR (I * zR)
  let weight (k : ℕ) : ℂ := translationWeight (zR ^ 2) k
  let orders := Finset.range (N / 2 + 1)
  have hShifted (k : ℕ) (hk : k ∈ orders) :
      HasSum (fun i => weight k * dMode k (shiftOuterMode k i))
        (weight k * ∑' i, dMode k i) :=
    ((shiftOuterMode k).hasSum_iff.mpr (hLowered k hk).hasSum).mul_left _
  have hNative (k : ℕ) (hk : k ∈ orders) :
      HasSum (fun i => weight k * dMode k i) (weight k * ∑' i, dMode k i) :=
    (hLowered k hk).hasSum.mul_left _
  have hTransport := (hasSum_sum (s := orders) hShifted).congr_fun
    (fun i => (dJointTerm_upper_eq_aJointTerm s t N P Q R S hS hz i).symm)
  have hValue := hTransport.unique hA
  rw [← hValue]
  exact (hasSum_sum (s := orders) hNative).congr_fun
    (dJointTerm_translatedDetector s t N P Q R S (zR ^ 2) dR (I * zR))

/-- Radial convergence of the transported D product for either fixed pair
field and either parity of the right field and detector. -/
theorem upper_fixed_d_joint_hasSum (s t : Bool) (M K L N : ℕ)
    (P Q : State s) (R S : State t)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {dR zR : ℂ} (hd : dR ≠ 0) (hr : ‖dR‖ < ‖zR‖) :
    HasSum (dJointTerm s t P Q R (translatedDetector t N (zR ^ 2) S) dR (I * zR))
      (∑' i, aJointTerm s t P Q R S dR zR i) := by
  have hz : zR ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hr)
  have hzI : I * zR ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hrad : ‖dR‖ < ‖I * zR‖ := by
    simpa only [norm_mul, Complex.norm_I, one_mul] using hr
  apply upper_fixed_d_hasSum_of_a s t N P Q R S hS hz
  · intro k hk
    have hk' : k ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hgrade := lowered_grade (s := t) (u := S) hS hk'
    exact (fixed_d_joint_hasSum_crossed_a s t M K L (N - 2 * k) P Q R ((L₁ t ^ k) S)
      hP hQ hR hgrade hd hzI hrad).summable
  · exact (fixed_a_joint_summable_of_homogeneous s t M K L N
      P Q R S hP hQ hR hS hd hr).hasSum

/-- For HHBB, the term on the A side is literally the native complex sewing
term. Its upper (2,3) image is HBHB D, with the odd detector translated by y. -/
theorem hhbb_upper_fixed_d_joint_hasSum (M K L N : ℕ)
    (P Q : State false) (R S : State true)
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit L) (hS : S.val ∈ actualGrade ℒ leechUnit N)
    {y : ℂ} (hy₁ : y ≠ 1) (hy : (1 / 2 : ℝ) < y.re) :
    HasSum (dJointTerm false true P Q R (translatedDetector true N y S)
      (Complex.sqrt (1 - y)) (I * Complex.sqrt y))
      (∑' i, NativeMixedComplexSewing.aJointTerm P Q R S
        (Complex.sqrt (1 - y)) (Complex.sqrt y) i) := by
  have hd : Complex.sqrt (1 - y) ≠ 0 := by
    intro h
    exact (sub_ne_zero.mpr hy₁.symm) (by simpa [h] using (sqrt_square (1 - y)).symm)
  have hr : ‖Complex.sqrt (1 - y)‖ < ‖Complex.sqrt y‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [← norm_pow, sqrt_square] using (norm_one_sub_lt_iff y).mpr hy
  have hD := upper_fixed_d_joint_hasSum false true M K L N
    P Q R S hP hQ hR hS hd hr
  rw [sqrt_square] at hD
  exact hD

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
