/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/BBHH/NativeBBHHExchange
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite collision exchange for the two odd inputs of the actual BBHH iterate. -/

import Mathlib.Analysis.Analytic.Binomial
import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHUpperCrossing
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMMSkew

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHExchange

open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeInvolution (FixedCarrier)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockOriginalTranslation (correctedField_translation_physical)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven leechUnit)
open Orbifold.NativeFixedPairField (nu nu_coeff_eq_originalI nu_lower_truncation nu_coeff_odd_zero)
open Orbifold.OriginalMMSkew (originalI_skew)
open OriginalFourMChargeCoset (originalI)
open NativeFixedCrossedProductToIterate (aJointTerm fixed_a_joint_summable_of_homogeneous)
open NativeBBHHUpperCrossing (bbhh_actual_upper_crossing_normalized)
open NativeMixedBProductUpperDisk (upperUnitDisk)
open NativeMixedUpperProductCusp (bJointTerm)
open D5.S3.VertexAlgebra.Analysis.IntegerNewton (choose_succ_mul)
open private fixed_odd_mode_zero fixed_a_off_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

local notation "ℒ" => leechData
local notation "ι" => leechUnit
local notation "T" => LatticeInvolution.fixedTranslation ℒ

private def detectorMode (Q S : TwistedEven) (n : ℤ) : FixedCarrier ℒ →ₗ[ℂ] ℂ :=
  (actualForm ℒ ι S.val).comp
    (((LinearMap.proj (2 * n)).comp HVertexOperator.coeff).comp
      ((correctedField ℒ ι).comp (LatticeInvolution.fixedSpace ℒ).subtype) |>.flip Q.val)

/-- The actual BBHH coefficient in physical powers of the separation and the
outer position. Each physical power doubles in the native root cover. -/
def collisionCoeff (P R : TwistedOdd) (Q S : TwistedEven) (m n : ℤ) : ℂ :=
  detectorMode Q S n ((nu true P).coeff (2 * m) R)

/-- The first possible physical separation exponent from the native pair truncation. -/
def collisionLowerBound (P R : TwistedOdd) : ℤ :=
  (-(maxOddWeight ℒ ι P.val : ℤ) - (maxOddWeight ℒ ι R.val : ℤ) - 5) / 2

private theorem pair_zero_below (P R : TwistedOdd) {k : ℤ}
    (hk : k < collisionLowerBound P R) :
    (nu true P).coeff (2 * k) R = 0 :=
  nu_lower_truncation true P R _ (by unfold collisionLowerBound at hk; omega)

private theorem detector_translate (Q S : TwistedEven) (n : ℤ) (a : FixedCarrier ℒ) :
    detectorMode Q S n (T a) = ((n : ℂ) + 1) * detectorMode Q S (n + 1) a := by
  change actualForm ℒ ι S.val ((correctedField ℒ ι
    (LatticeSugawaraConformal.translation ℒ a.val)).coeff (2 * n) Q.val) = _
  rw [correctedField_translation_physical, map_smul, smul_eq_mul,
    show 2 * n + 2 = 2 * (n + 1) by ring]
  change (((2 * (n + 1) : ℤ) : ℂ) / 2) * detectorMode Q S (n + 1) a = _
  push_cast
  ring

private theorem detector_translate_pow (Q S : TwistedEven) (j : ℕ) (n : ℤ)
    (a : FixedCarrier ℒ) :
    detectorMode Q S n ((T ^ j) a) =
      (j.factorial : ℂ) * Ring.choose ((n : ℂ) + j) j *
        detectorMode Q S (n + j) a := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' T, Module.End.mul_apply, detector_translate, ih]
    have h : (n : ℂ) + ↑(j + 1) = ((n + 1 : ℤ) : ℂ) + j := by push_cast; ring
    have hc := choose_succ_mul ((n : ℂ) + ↑(j + 1)) j
    rw [h] at hc
    rw [show ((n + 1 : ℤ) : ℂ) + j - j = (n : ℂ) + 1 by push_cast; ring] at hc
    rw [Nat.factorial_succ, Nat.cast_mul, h,
      show n + (↑(j + 1) : ℤ) = n + 1 + j by omega]
    push_cast
    calc
      _ = (j.factorial : ℂ) *
          (((n : ℂ) + 1) * Ring.choose (((n + 1 : ℤ) : ℂ) + j) j) *
          detectorMode Q S (n + 1 + j) a := by push_cast; ring
      _ = _ := by rw [← hc]; push_cast; ring

/-- Coefficient of the opposite BBHH iterate after the physical change
`(U, Z) ↦ (-U, Z+U)`. The binomial coefficient expands the second
coordinate, and the half-turn contributes `(-1)^k` in physical degree
`k`. The reindexed sum is finite for arbitrary states, even at poles. -/
theorem collisionCoeff_exchange (P R : TwistedOdd) (Q S : TwistedEven) (m n : ℤ) :
    collisionCoeff P R Q S m n =
      ∑ k ∈ Finset.Icc (collisionLowerBound R P) m,
        (-1 : ℂ) ^ k * Ring.choose ((n + m - k : ℤ) : ℂ) (m - k).toNat *
          collisionCoeff R P Q S k (n + m - k) := by
  let lower := collisionLowerBound R P
  let f (j : ℕ) : FixedCarrier ℒ :=
    (StateFieldResidueReconstruction.epsilon (-m - 1 + j + 1) / (j.factorial : ℂ)) •
      (T ^ j) (originalI ℒ ι leech_spec.2.2.1 (-m - 1 + j) R P)
  have hI (j : ℕ) :
      originalI ℒ ι leech_spec.2.2.1 (-m - 1 + j) R P =
        (nu true R).coeff (2 * (m - j)) P := by
    rw [← nu_coeff_eq_originalI]
    rw [show -2 * (-m - 1 + (j : ℤ)) - 2 = 2 * (m - (j : ℤ)) by ring]
  have hs : Function.support f ⊆ (↑(Finset.range ((m - lower + 1).toNat)) : Set ℕ) := by
    intro j hj
    by_contra h
    have hj' : (m - lower + 1).toNat ≤ j := by
      simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using h
    apply hj
    unfold f
    rw [hI, pair_zero_below R P (show m - (j : ℤ) < lower by omega), map_zero, smul_zero]
  have hp : (nu true P).coeff (2 * m) R = ∑ j ∈ Finset.range ((m - lower + 1).toNat), f j := by
    rw [show 2 * m = -2 * (-m - 1) - 2 by ring, nu_coeff_eq_originalI,
      originalI_skew ℒ ι leech_spec.2.2.1 leech_spec.1,
      finsum_eq_sum_of_support_subset f hs]
  rw [collisionCoeff, hp, map_sum]
  refine Finset.sum_bij (fun j _ => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j _ l _ h
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    refine ⟨(m - k).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have he : (-m - 1 + (j : ℤ) + 1) = -(m - (j : ℤ)) := by ring
    have hs : StateFieldResidueReconstruction.epsilon (-m - 1 + (j : ℤ) + 1) =
        (-1 : ℂ) ^ (m - (j : ℤ)) := by
      rw [he, StateFieldResidueReconstruction.epsilon, zpow_neg, ← inv_zpow]
      norm_num
    dsimp only [f]
    rw [map_smul, smul_eq_mul, detector_translate_pow, hI, hs,
      show n + m - (m - (j : ℤ)) = n + j by ring,
      show (m - (m - (j : ℤ))).toNat = j by omega, Int.cast_add, Int.cast_natCast,
      collisionCoeff]
    field_simp

/-- The two root signs disappear independently. Both indices are even wherever
the native BBHH A term can survive. -/
theorem aJointTerm_eq_zero_of_odd (P R : TwistedOdd) (Q S : TwistedEven)
    (d z : ℂ) (i : ℤ × ℤ) (h : Odd i.1 ∨ Odd i.2) :
    aJointTerm true false P R Q S d z i = 0 := by
  rcases h with h | h
  · simp [aJointTerm, nu_coeff_odd_zero true i.1 P R h]
  · rw [aJointTerm, fixed_odd_mode_zero ((nu true P).coeff i.1 R) i.2 h Q.val, map_zero, zero_mul]

/-- On its even indices the literal BBHH A term uses the physical powers
of the two squared arguments, independent of either root choice. -/
theorem aJointTerm_physical (P R : TwistedOdd) (Q S : TwistedEven)
    {d z U Z : ℂ} (hd : d ^ (2 : ℕ) = U) (hz : z ^ (2 : ℕ) = Z) (m n : ℤ) :
    aJointTerm true false P R Q S d z (2 * m, 2 * n) =
      collisionCoeff P R Q S m n * (U ^ m * Z ^ n) := by
  change collisionCoeff P R Q S m n * (d ^ (2 * m) * z ^ (2 * n)) = _
  rw [zpow_mul, zpow_mul, zpow_ofNat, zpow_ofNat, hd, hz]

/-- In the slit plane the principal square root at the reciprocal is the
reciprocal root. With the extra square root in the weighted BBHH normalization,
the raw homogeneous factor `y ^ e` becomes `y ^ (e+1)`. -/
theorem normalized_exchange_scale {y : ℂ} (hy : y ∈ Complex.slitPlane) (e : ℤ) :
    Complex.sqrt y * y ^ e = y ^ (e + 1) * Complex.sqrt y⁻¹ := by
  have harg := (Complex.mem_slitPlane_iff_arg.mp hy).1
  have hy₀ := (Complex.mem_slitPlane_iff_arg.mp hy).2
  have hs : Complex.sqrt y⁻¹ = (Complex.sqrt y)⁻¹ := by
    unfold Complex.sqrt
    exact Complex.inv_cpow _ _ harg
  have hroot : Complex.sqrt y ≠ 0 := fun h => hy₀ (by simpa [h] using (sqrt_square y).symm)
  rw [hs, zpow_add₀ hy₀, zpow_one]
  have h : y = Complex.sqrt y * Complex.sqrt y := by rw [← pow_two, sqrt_square]
  calc
    _ = y ^ e * ((Complex.sqrt y * Complex.sqrt y) * (Complex.sqrt y)⁻¹) := by
      rw [mul_assoc, mul_inv_cancel₀ hroot, mul_one, mul_comm]
    _ = _ := by rw [← h, mul_assoc]

private theorem hasSum_binomial_zpow (a : ℤ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun j : ℕ => Ring.choose (a : ℂ) j * w ^ j) ((1 + w) ^ a) := by
  have hw' : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal, mem_ball_zero_iff]
    exact hw
  simpa only [binomialSeries, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, Complex.cpow_intCast,
    mul_comm] using (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (a : ℂ))).hasSum hw'

/-- The Taylor summands of the opposite iterate in the coordinate
`w = (X-Z)/Z`, with the overall factor `Z ^ e` removed. -/
def exchangeTaylorTerm (P R : TwistedOdd) (Q S : TwistedEven) (e : ℤ) (w : ℂ)
    (i : ℤ × ℕ) : ℂ :=
  (-1 : ℂ) ^ i.1 * collisionCoeff R P Q S i.1 (e - i.1) *
    Ring.choose ((e - i.1 : ℤ) : ℂ) i.2 * (w ^ i.1 * w ^ i.2)

/-- The exact interchange needed for the analytic exchange. Summing the Taylor
terms by the opposite separation exponent gives the opposite iterate. Summing
by total collision exponent gives the original iterate. -/
theorem collision_exchange_of_summable (P R : TwistedOdd) (Q S : TwistedEven)
    (e : ℤ) {w : ℂ} (hw₀ : w ≠ 0) (hw : ‖w‖ < 1)
    (h : Summable (exchangeTaylorTerm P R Q S e w)) :
    ∃ A : ℂ,
      HasSum (fun m : ℤ => collisionCoeff P R Q S m (e - m) * w ^ m) A ∧
      HasSum (fun k : ℤ => (1 + w) ^ e *
        (collisionCoeff R P Q S k (e - k) * (-w / (1 + w)) ^ k)) A := by
  let f := exchangeTaylorTerm P R Q S e w
  let lower := collisionLowerBound R P
  let shift : ℤ × ℕ ≃ ℤ × ℕ :=
    { toFun := fun i => (i.1 - (i.2 : ℤ), i.2)
      invFun := fun i => (i.1 + (i.2 : ℤ), i.2)
      left_inv := fun (k, j) => by simp
      right_inv := fun (k, j) => by simp }
  have h₁ : 1 + w ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp
    (Complex.mem_slitPlane_of_norm_lt_one hw)).2
  refine ⟨∑' i, f i, (shift.hasSum_iff.mpr h.hasSum).prod_fiberwise ?_,
    h.hasSum.prod_fiberwise ?_⟩
  · intro m
    let p := Finset.range ((m - lower + 1).toNat)
    have hs : Function.support (fun j : ℕ => f (m - (j : ℤ), j)) ⊆ (↑p : Set ℕ) := by
      intro j hj
      by_contra hn
      have hj' : (m - lower + 1).toNat ≤ j := by
        simpa only [p, Finset.mem_coe, Finset.mem_range, not_lt] using hn
      have hz := pair_zero_below R P (show m - (j : ℤ) < lower by omega)
      apply hj
      simp only [f, exchangeTaylorTerm, collisionCoeff, hz, map_zero, mul_zero, zero_mul]
    change HasSum (fun j : ℕ => f (m - (j : ℤ), j)) _
    have hm : HasSum (fun j : ℕ => f (m - (j : ℤ), j))
        (∑ j ∈ p, f (m - (j : ℤ), j)) := by
      refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
      by_contra hn
      exact hj (hs (show j ∈ Function.support (fun j : ℕ => f (m - (j : ℤ), j)) from hn))
    convert hm using 1
    rw [collisionCoeff_exchange, Finset.sum_mul]
    symm
    refine Finset.sum_bij (fun j _ => m - (j : ℤ)) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [p, Finset.mem_range] at hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j _ l _ h
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      exact ⟨(m - k).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      dsimp only [f, exchangeTaylorTerm]
      rw [← zpow_natCast, ← zpow_add₀ hw₀]
      rw [show (m - (j : ℤ)) + j = m by omega,
        show (m - (m - (j : ℤ))).toNat = j by omega,
        show e - m + m - (m - (j : ℤ)) = e - (m - (j : ℤ)) by omega]
      ring
  · intro k
    have hk := (hasSum_binomial_zpow (e - k) hw).mul_left
      ((-1 : ℂ) ^ k * collisionCoeff R P Q S k (e - k) * w ^ k)
    have he : (1 + w) ^ (e - k) = (1 + w) ^ e / (1 + w) ^ k := zpow_sub₀ h₁ _ _
    rw [he] at hk
    convert hk using 1
    · ext j
      unfold exchangeTaylorTerm
      ring
    · rw [div_zpow, neg_eq_neg_one_mul, mul_zpow]
      ring

private theorem norm_binomial_neg (a j : ℕ) :
    ‖Ring.choose (-(↑(a + 1) : ℂ)) j‖ = ((j + a).choose a : ℝ) := by
  rw [Ring.choose_neg, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
    Int.cast_negOnePow_natCast, smul_eq_mul, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul,
    show (↑(a + 1) : ℂ) + j - 1 = (↑(j + a) : ℂ) by push_cast; ring,
    Ring.choose_natCast, Complex.norm_natCast, Nat.choose_symm_add]

private theorem norm_taylor_row (P R : TwistedOdd) (Q S : TwistedEven)
    (e k : ℤ) (w : ℂ) :
    (fun j : ℕ => ‖exchangeTaylorTerm P R Q S e w (k, j)‖) =
      fun j => (‖collisionCoeff R P Q S k (e - k)‖ * ‖w‖ ^ k) *
        ‖Ring.choose ((e - k : ℤ) : ℂ) j * w ^ j‖ := by
  funext j
  simp only [exchangeTaylorTerm, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  ring

private theorem norm_taylor_row_sum (P R : TwistedOdd) (Q S : TwistedEven)
    (e k : ℤ) {w : ℂ} (hw : ‖w‖ < 1) (hk : e < k) :
    HasSum (fun j : ℕ => ‖exchangeTaylorTerm P R Q S e w (k, j)‖)
      ((1 - ‖w‖) ^ e * (‖collisionCoeff R P Q S k (e - k)‖ *
        (‖w‖ / (1 - ‖w‖)) ^ k)) := by
  let a := (k - e - 1).toNat
  have ha : e - k = -(↑(a + 1) : ℤ) := by dsimp [a]; omega
  have ht := (hasSum_choose_mul_geometric_of_norm_lt_one a
      (r := ‖w‖) (by simpa only [Real.norm_of_nonneg (norm_nonneg w)] using hw)).mul_left
      (‖collisionCoeff R P Q S k (e - k)‖ * ‖w‖ ^ k)
  rw [norm_taylor_row]
  convert ht using 1
  · ext j
    rw [norm_mul, norm_pow, ha, Int.cast_neg, Int.cast_natCast, norm_binomial_neg]
  · let d := 1 - ‖w‖
    have hd : d ≠ 0 := by dsimp [d]; linarith
    have hp : d ^ e / d ^ k = 1 / d ^ (a + 1) := by
      rw [← zpow_sub₀ hd, ha, zpow_neg, zpow_natCast, one_div]
    change d ^ e * (_ * (‖w‖ / d) ^ k) = _ * (1 / d ^ (a + 1))
    rw [← hp, div_zpow]
    ring

/-- For homogeneous actual states the Taylor interchange is absolutely
summable when the physical collision ratio satisfies `‖w‖ < 1/2`.
The norm sum of every negative-power row is a negative binomial at `‖w‖`.
The resulting majorant is the opposite native radial series at
`‖w‖ / (1 - ‖w‖)`. -/
theorem exchangeTaylorTerm_summable (M H K J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ ι M) (hR : R.val ∈ actualGrade ℒ ι H)
    (hQ : Q.val ∈ actualGrade ℒ ι K) (hS : S.val ∈ actualGrade ℒ ι J)
    (e : ℤ) {w : ℂ} (hw₀ : w ≠ 0) (hw : ‖w‖ < 1 / 2) :
    Summable (exchangeTaylorTerm P R Q S e w) := by
  let f := exchangeTaylorTerm P R Q S e w
  let lower := collisionLowerBound R P
  have hw₁ : ‖w‖ < 1 := hw.trans (by norm_num)
  apply Summable.of_norm
  refine (summable_prod_of_nonneg (fun i => norm_nonneg (f i))).mpr ⟨?_, ?_⟩
  · intro k
    rw [norm_taylor_row]
    exact (hasSum_binomial_zpow (e-k) hw₁).summable.norm.mul_left _
  · let r := ‖w‖ / (1 - ‖w‖)
    have hden : 0 < 1 - ‖w‖ := by linarith
    have hr₀ : 0 < r := div_pos (norm_pos_iff.mpr hw₀) hden
    have hr₁ : r < 1 := (div_lt_one hden).mpr (by linarith)
    let d := Complex.sqrt (r : ℂ)
    have hd : d ^ (2 : ℕ) = (r : ℂ) := sqrt_square _
    have hd₀ : d ≠ 0 := fun h => by
      rw [h, zero_pow (by decide)] at hd
      exact hr₀.ne' (Complex.ofReal_eq_zero.mp hd.symm)
    have hd₁ : ‖d‖ < ‖(1 : ℂ)‖ := by
      have hnorm := congrArg norm hd
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr₀.le] at hnorm
      rw [norm_one]
      nlinarith [norm_nonneg d]
    have hJoint := fixed_a_joint_summable_of_homogeneous true false H M K J R P Q S
      hR hP hQ hS hd₀ hd₁
    let modes (k : ℤ) : ℤ × ℤ := (2 * k, 2 * (e - k))
    have hInj : Function.Injective modes := by
      intro k l h
      have h' := congrArg Prod.fst h
      dsimp [modes] at h'
      omega
    have hs := (hJoint.comp_injective hInj).norm
    have hmajorant : Summable (fun k : ℤ => (1 - ‖w‖) ^ e *
        (‖collisionCoeff R P Q S k (e - k)‖ * r ^ k)) := by
      refine (hs.mul_left ((1 - ‖w‖) ^ e)).congr fun k => ?_
      simp only [Function.comp_apply, modes, aJointTerm_physical R P Q S hd
        (one_pow 2), one_zpow, mul_one, norm_mul, norm_zpow, Complex.norm_real,
        Real.norm_of_nonneg hr₀.le]
    let shift (n : ℕ) : ℤ := lower + n
    have hinj : Function.Injective shift := by intro i j h; dsimp [shift] at h; omega
    have hoff (k : ℤ) (hk : k ∉ Set.range shift) :
        (∑' j, ‖f (k, j)‖) = 0 := by
      have hk' : k < lower := by
        by_contra! h
        exact hk ⟨(k - lower).toNat, by dsimp [shift]; omega⟩
      have hz := pair_zero_below R P hk'
      simp only [f, exchangeTaylorTerm, collisionCoeff, hz, map_zero, mul_zero,
        zero_mul, norm_zero, tsum_zero]
    have hsums : Summable (fun n : ℕ => ∑' j : ℕ, ‖f (shift n, j)‖) := by
      refine (hmajorant.comp_injective hinj).of_norm_bounded_eventually_nat ?_
      filter_upwards [eventually_ge_atTop ((e - lower + 1).toNat)] with n hn
      have hn' : e < shift n := by dsimp [shift]; omega
      change ‖∑' j, ‖f (shift n, j)‖‖ ≤ _
      rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
        (norm_taylor_row_sum P R Q S e (shift n) hw₁ hn').tsum_eq]
      exact le_rfl
    exact ((hinj.hasSum_iff hoff).mp hsums.hasSum).summable

private theorem native_collision_hasSum (M H K J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ ι M) (hR : R.val ∈ actualGrade ℒ ι H)
    (hQ : Q.val ∈ actualGrade ℒ ι K) (hS : S.val ∈ actualGrade ℒ ι J)
    (hpar : Even ((M : ℤ) + H))
    {e : ℤ} (he : 2 * e = (J : ℤ) - K - (M + H + 6))
    {d z U Z A : ℂ} (hd : d ^ (2 : ℕ) = U) (hz : z ^ (2 : ℕ) = Z) (hZ : Z ≠ 0)
    (hSum : HasSum (fun k : ℤ => collisionCoeff P R Q S k (e - k) * (U / Z) ^ k) A) :
    HasSum (aJointTerm true false P R Q S d z) (Z ^ e * A) := by
  let modes (k : ℤ) : ℤ × ℤ := (2 * k, 2 * (e - k))
  have hinj : Function.Injective modes := by
    intro k l h
    have hh := congrArg Prod.fst h
    dsimp [modes] at hh
    omega
  have hoff (i : ℤ × ℤ) (hi : i ∉ Set.range modes) :
      aJointTerm true false P R Q S d z i = 0 := by
    by_cases hm : Odd i.1
    · exact aJointTerm_eq_zero_of_odd P R Q S d z i (Or.inl hm)
    obtain ⟨m, hm⟩ := Int.not_odd_iff_even.mp hm
    have hn : i.2 ≠ (J : ℤ) - K - (i.1 + ((M : ℤ) + H + 6)) := by
      intro hn
      exact hi ⟨m, Prod.ext (by dsimp [modes]; omega) (by dsimp [modes]; omega)⟩
    rw [aJointTerm, fixed_a_off_diagonal true false M H K J P R Q S
      hP hR hQ hS hpar i.1 i.2 hn, zero_mul]
  apply (hinj.hasSum_iff hoff).mp
  refine (hSum.mul_left (Z ^ e)).congr_fun fun k => ?_
  change aJointTerm true false P R Q S d z (2 * k, 2 * (e - k)) = _
  rw [aJointTerm_physical P R Q S hd hz, zpow_sub₀ hZ, div_zpow]
  ring

/-- In the common physical collision neighborhood the actual BBHH A iterates
for `(P,R; X-Z,Z)` and `(R,P; Z-X,X)` have the same sum. Each root may
be chosen independently. The Taylor interchange follows from actual radial
summability and the all-state finite exchange of coefficients. -/
theorem bbhh_actual_collision_exchange (M H K J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ ι M) (hR : R.val ∈ actualGrade ℒ ι H)
    (hQ : Q.val ∈ actualGrade ℒ ι K) (hS : S.val ∈ actualGrade ℒ ι J)
    (hpar : Even ((M : ℤ) + H))
    {e : ℤ} (he : 2 * e = (J : ℤ) - K - (M + H + 6))
    {X Z d z d' z' : ℂ} (hZ : Z ≠ 0) (hX : X ≠ 0) (hXZ : X ≠ Z)
    (hnear : ‖(X - Z) / Z‖ < 1 / 2)
    (hd : d ^ (2 : ℕ) = X - Z) (hz : z ^ (2 : ℕ) = Z)
    (hd' : d' ^ (2 : ℕ) = Z - X) (hz' : z' ^ (2 : ℕ) = X) :
    ∃ A : ℂ, HasSum (aJointTerm true false P R Q S d z) A ∧
      HasSum (aJointTerm true false R P Q S d' z') A := by
  let w := (X - Z) / Z
  have hw₀ : w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hXZ) hZ
  obtain ⟨A, ha, hb⟩ := collision_exchange_of_summable P R Q S e hw₀
    (hnear.trans (by norm_num)) (exchangeTaylorTerm_summable M H K J P R Q S hP hR hQ hS e hw₀ hnear)
  refine ⟨Z ^ e * A, native_collision_hasSum M H K J P R Q S hP hR hQ hS hpar he hd hz hZ ha, ?_⟩
  have h₁ : 1 + w = X / Z := by dsimp [w]; field_simp; ring
  have h₂ : -w / (1 + w) = (Z - X) / X := by rw [h₁]; dsimp [w]; field_simp; ring
  rw [h₂, h₁] at hb
  have hScale := hb.mul_left ((X / Z) ^ e)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ (div_ne_zero hX hZ)), one_mul] at hScale
  have he' : 2 * e = (J : ℤ) - K - (H + M + 6) := by rw [he]; ring
  have hpar' : Even ((H : ℤ) + M) := by simpa only [add_comm] using hpar
  have hc := native_collision_hasSum H M K J R P Q S hR hP hQ hS hpar' he' hd' hz' hX hScale
  have hvalue : X ^ e * (((X / Z) ^ e)⁻¹ * A) = Z ^ e * A := by
    rw [div_zpow, inv_div, ← mul_assoc, ← mul_div_assoc, mul_comm (X ^ e),
      mul_div_cancel_right₀ _ (zpow_ne_zero _ hX)]
  rwa [hvalue] at hc

/-- The two principal weighted BBHH collision charts at `y` and `y⁻¹`.
Their physical exchange has factor `y ^ (e+1)`, where `e` is the total
physical Laurent degree of the unweighted iterate. -/
theorem bbhh_actual_normalized_exchange (M H K J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ ι M) (hR : R.val ∈ actualGrade ℒ ι H)
    (hQ : Q.val ∈ actualGrade ℒ ι K) (hS : S.val ∈ actualGrade ℒ ι J)
    (hpar : Even ((M : ℤ) + H))
    {e : ℤ} (he : 2 * e = (J : ℤ) - K - (M + H + 6))
    {y : ℂ} (hy : y ∈ Complex.slitPlane) (hy₁ : y ≠ 1)
    (hnear : ‖(1 - y) / y‖ < 1 / 2) :
    ∃ A : ℂ,
      HasSum (fun i => Complex.sqrt y *
        aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i)
        (y ^ (e + 1) * A) ∧
      HasSum (fun i => Complex.sqrt y⁻¹ *
        aJointTerm true false R P Q S (Complex.sqrt (1 - y⁻¹)) (Complex.sqrt y⁻¹) i) A := by
  let w := (1 - y) / y
  have hy₀ := Complex.slitPlane_ne_zero hy
  have hw₀ : w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy₁.symm) hy₀
  obtain ⟨A, ha, hb⟩ := collision_exchange_of_summable P R Q S e hw₀
    (hnear.trans (by norm_num)) (exchangeTaylorTerm_summable M H K J P R Q S hP hR hQ hS e hw₀ hnear)
  have h₁ : 1 + w = y⁻¹ := by dsimp [w]; field_simp; ring
  have h₂ : -w / (1 + w) = (1 - y⁻¹) / y⁻¹ := by rw [h₁]; dsimp [w]; field_simp; ring
  rw [h₂, h₁] at hb
  have hinv : (y⁻¹ : ℂ) ^ e ≠ 0 := zpow_ne_zero _ (inv_ne_zero hy₀)
  have hb' := hb.mul_left ((y⁻¹ : ℂ) ^ e)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hinv, one_mul] at hb'
  have he' : 2 * e = (J : ℤ) - K - (H + M + 6) := by rw [he]; ring
  have hpar' : Even ((H : ℤ) + M) := by simpa only [add_comm] using hpar
  have hForward := (native_collision_hasSum M H K J P R Q S hP hR hQ hS hpar he
    (sqrt_square (1 - y)) (sqrt_square y) hy₀ ha).mul_left (Complex.sqrt y)
  have hOpposite := (native_collision_hasSum H M K J R P Q S hR hP hQ hS hpar' he'
    (sqrt_square (1 - y⁻¹)) (sqrt_square y⁻¹) (inv_ne_zero hy₀) hb').mul_left (Complex.sqrt y⁻¹)
  rw [show y⁻¹ ^ e * ((y⁻¹ ^ e)⁻¹ * A) = A by
    rw [← mul_assoc, mul_inv_cancel₀ hinv, one_mul] ] at hOpposite
  refine ⟨_, ?_, hOpposite⟩
  rw [← mul_assoc, normalized_exchange_scale hy e, mul_assoc] at hForward
  exact hForward

/-- On the reciprocal upper lens, collision exchange identifies the original
weighted A chart with the opposite native B product. The minus sign is
the existing A-to-B sewing sign. The factor in physical degree is
`y ^ (e+1)` and comes from dilation and the principal square root. -/
theorem bbhh_actual_collision_hasSum_opposite_b (M H K J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ ι M) (hR : R.val ∈ actualGrade ℒ ι H)
    (hQ : Q.val ∈ actualGrade ℒ ι K) (hS : S.val ∈ actualGrade ℒ ι J)
    (hpar : Even ((M : ℤ) + H))
    {e : ℤ} (he : 2 * e = (J : ℤ) - K - (M + H + 6))
    {y : ℂ} (hy : y ∈ Complex.slitPlane) (hy₁ : y ≠ 1)
    (hnear : ‖(1 - y) / y‖ < 1 / 2) (hinv : y⁻¹ ∈ upperUnitDisk)
    (hre : (1 / 2 : ℝ) < (y⁻¹).re) :
    ∃ A : ℂ,
      HasSum (fun i => Complex.sqrt y *
        aJointTerm true false P R Q S (Complex.sqrt (1 - y)) (Complex.sqrt y) i)
        (y ^ (e + 1) * A) ∧
      HasSum (fun i => Complex.sqrt y⁻¹ *
        bJointTerm true true P Q R S 1 (Complex.sqrt y⁻¹) i) (-A) := by
  obtain ⟨A, hForward, hOpposite⟩ :=
    bbhh_actual_normalized_exchange M H K J P R Q S hP hR hQ hS hpar he hy hy₁ hnear
  obtain ⟨C, hA, hB⟩ := bbhh_actual_upper_crossing_normalized R P Q S hinv hre
  have hEq := hOpposite.unique (hA.mul_left (Complex.sqrt y⁻¹))
  refine ⟨A, hForward, ?_⟩
  rw [hEq]
  simpa only [mul_neg] using hB.mul_left (Complex.sqrt y⁻¹)

#print axioms bbhh_actual_collision_hasSum_opposite_b
#print axioms bbhh_actual_collision_exchange
#print axioms bbhh_actual_normalized_exchange
#print axioms collisionCoeff_exchange
#print axioms exchangeTaylorTerm_summable
#print axioms collision_exchange_of_summable
#print axioms aJointTerm_eq_zero_of_odd
#print axioms aJointTerm_physical
#print axioms normalized_exchange_scale

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHExchange
