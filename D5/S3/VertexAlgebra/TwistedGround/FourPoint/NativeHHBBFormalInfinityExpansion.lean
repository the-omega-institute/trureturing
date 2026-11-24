import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! The formal energy expansion of the exchanged native HHBB channel. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal NNReal TensorProduct Topology
open Bornology Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalInfinityExpansion

/-- Reverse all coefficients through the prescribed degree bound, including the padding. -/
def paddedReverse (degree : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (degree + 1), Polynomial.C (P.coeff j) * Polynomial.X ^ (degree - j)

theorem eval_paddedReverse {degree : ℕ} {P : Polynomial ℂ} (hP : P.natDegree ≤ degree)
    {z : ℂ} (hz : z ≠ 0) :
    (paddedReverse degree P).eval z = z ^ degree * P.eval z⁻¹ := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
  simp only [paddedReverse, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : z ^ degree * (z⁻¹) ^ j = z ^ (degree - j) := by
    conv_lhs => rw [← Nat.sub_add_cancel hjd, pow_add]
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]
  rw [← hpow, mul_left_comm]

/-- Invert the exterior coordinate and extend the cleared identity through the center. -/
theorem eventually_eq_paddedReverse {GInf : ℂ → ℂ} {P : Polynomial ℂ} {degree poleOrder : ℕ}
    (hP : P.natDegree ≤ degree) (hG : ContinuousAt GInf 0)
    (hExterior : ∀ᶠ y in cobounded ℂ,
      P.eval y = y ^ degree * (GInf y⁻¹ * (y⁻¹ - 1) ^ poleOrder)) :
    ∀ᶠ z in 𝓝 (0 : ℂ), GInf z * (z - 1) ^ poleOrder = (paddedReverse degree P).eval z := by
  have hp : (fun z : ℂ => GInf z * (z - 1) ^ poleOrder) =ᶠ[𝓝[≠] (0 : ℂ)]
      (paddedReverse degree P).eval := by
    filter_upwards [(tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hExterior,
      self_mem_nhdsWithin] with z hz hn
    have hz₀ : z ≠ 0 := by simpa using hn
    rw [eval_paddedReverse hP hz₀, hz, inv_inv, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hz₀, one_pow, one_mul]
  have hContinuous : ContinuousAt (fun z : ℂ => GInf z * (z - 1) ^ poleOrder) 0 :=
    hG.mul ((continuousAt_id.sub continuousAt_const).pow _)
  have hCenter := tendsto_nhds_unique_of_eventuallyEq
    hContinuous.continuousWithinAt (paddedReverse degree P).continuous.continuousWithinAt hp
  filter_upwards [eventually_nhdsWithin_iff.mp hp] with z hz
  by_cases hz₀ : z = 0
  · simpa only [hz₀] using hCenter
  · exact hz (by simpa using hz₀)

private theorem hasFPowerSeriesAt_of_hasSum_unitBall {a : ℕ → ℂ} {f : ℂ → ℂ}
    (h : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => a n * z ^ n) (f z)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  let r : ℝ≥0 := 1 / 2
  have hr : (r : ℝ) < 1 := by norm_num [r]
  have hs := (h (r : ℝ) (by
    simpa [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg r.2] using hr)).summable
  obtain ⟨C, hC⟩ := (isBounded_range_of_tendsto _ hs.tendsto_atTop_zero).exists_norm_le
  refine ⟨(r : ℝ≥0∞), ?_, by norm_num [r], ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ C
    intro n
    simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg r.2] using hC _ (Set.mem_range_self n)
  · intro z hz
    rw [eball_coe] at hz
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      h z (ball_subset_ball hr.le hz)

open PowerSeries (coeff)

-- Clearing one factor at a time uses the coefficient shift under multiplication by X.
private theorem mk_eq_mul_invOneSubPow {a : ℕ → ℂ} {f : ℂ → ℂ} {Q : Polynomial ℂ}
    {poleOrder : ℕ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => a n * z ^ n) (f z))
    (hGerm : ∀ᶠ z in 𝓝 (0 : ℂ), f z * (1 - z) ^ poleOrder = Q.eval z) :
    PowerSeries.mk a = Q.toPowerSeries * ↑(PowerSeries.invOneSubPow ℂ poleOrder) := by
  let S := PowerSeries.mk a
  have hMultiply (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (m : ℕ) :
      HasSum (fun n => coeff n (S * (1 - PowerSeries.X) ^ m) * z ^ n)
        (f z * (1 - z) ^ m) := by
    induction m with
    | zero => simpa [S] using hsum z hz
    | succ m ih =>
      let T := S * (1 - PowerSeries.X) ^ m
      have hCoeff (n : ℕ) : coeff (n + 1) (T * PowerSeries.X) = coeff n T := by
        simpa only [pow_one] using PowerSeries.coeff_mul_X_pow T 1 n
      have hShift : HasSum (fun n => coeff n (T * PowerSeries.X) * z ^ n)
          ((f z * (1 - z) ^ m) * z) := by
        rw [← hasSum_nat_add_iff' 1]
        simp only [Finset.sum_range_one, PowerSeries.coeff_zero_mul_X, zero_mul, sub_zero,
          hCoeff, pow_succ]
        simpa only [T, mul_assoc] using ih.mul_right z
      simpa only [pow_succ, ← mul_assoc, mul_sub, mul_one, map_sub, sub_mul, T] using ih.sub hShift
  have hPolynomial (z : ℂ) : HasSum (fun n => Q.coeff n * z ^ n) (Q.eval z) := by
    rw [Polynomial.eval_eq_sum_range]
    exact hasSum_sum_of_ne_finset_zero fun n hn => by
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn : Q.natDegree < n)]
  have hTaylor := HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    (hasFPowerSeriesAt_of_hasSum_unitBall fun z hz => hMultiply z hz poleOrder)
    (hasFPowerSeriesAt_of_hasSum_unitBall fun z _ => hPolynomial z) hGerm
  have hClear : S * (1 - PowerSeries.X) ^ poleOrder = Q.toPowerSeries := by
    apply PowerSeries.ext
    intro n
    simpa only [Polynomial.coeff_coe] using
      congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ hTaylor) n
  change S = _
  rw [← hClear, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.inv_val, mul_one]

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedUpperProductCusp (bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeHHBBNormalizedGlobalMeromorphic (hhbb_marked_normalized_global_meromorphic)
open NativeHHBBPolynomialFromInfinity (hhbb_marked_upper_common_rational)

local notation "ℒ" => leechData

/-- The exterior identity and the signed formal expansion of the actual D energy diagonal. -/
theorem hhbb_native_d_infinity_powerSeries
    (M K L N : ℕ) (u v : TwistedEven) (w b : TwistedOdd)
    (GInf : ℂ → ℂ) (P : Polynomial ℂ) (degree poleOrder : ℕ)
    (hP : P.natDegree ≤ degree)
    (hsum : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun E : ℕ => dProductCoeff false false M K L N u w v b E * z ^ E) (GInf z))
    (hExterior : ∀ᶠ y in cobounded ℂ,
      P.eval y = y ^ degree * (GInf y⁻¹ * (y⁻¹ - 1) ^ poleOrder)) :
    (∀ᶠ z in 𝓝 (0 : ℂ), GInf z * (z - 1) ^ poleOrder = (paddedReverse degree P).eval z) ∧
    PowerSeries.mk (dProductCoeff false false M K L N u w v b) =
      (Polynomial.C ((-1 : ℂ) ^ poleOrder) * paddedReverse degree P).toPowerSeries *
        ↑(PowerSeries.invOneSubPow ℂ poleOrder) := by
  have hGerm := eventually_eq_paddedReverse hP
    (hasFPowerSeriesAt_of_hasSum_unitBall hsum).continuousAt hExterior
  refine ⟨hGerm, mk_eq_mul_invOneSubPow hsum ?_⟩
  filter_upwards [hGerm] with z hz
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← hz,
    show (1 - z : ℂ) = (-1) * (z - 1) by ring, mul_pow, mul_left_comm]

set_option maxHeartbeats 4000000 in
/-- The marked Leech HHBB numerator gives the exchanged native D formal energy expansion. -/
theorem hhbb_marked_native_d_infinity_powerSeries {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r s : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] s) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let poleOrder := (6 + M + K) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r s z
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j (fun z => (z - 1) ^ poleOrder * GInf z)) *
        Polynomial.X ^ (degree - j)
    (∀ᶠ z in 𝓝 (0 : ℂ), GInf z * (z - 1) ^ poleOrder = (paddedReverse degree P).eval z) ∧
    PowerSeries.mk (dProductCoeff false false M K L N u w v b) =
      (Polynomial.C ((-1 : ℂ) ^ poleOrder) * paddedReverse degree P).toPowerSeries *
        ↑(PowerSeries.invOneSubPow ℂ poleOrder) := by
  intro grade V M K L N poleOrder degree GInf P
  obtain ⟨hDegree, ⟨H, _, hUpper, hRational⟩, _⟩ :=
    hhbb_marked_upper_common_rational slot colour n l hl hpar u v w b p q r s hu hv hw hb
  obtain ⟨H', hHol', _, _, hUpper', ⟨_, _, _, hInf⟩, _, ⟨_, _, _, hSum⟩, _⟩ :=
    hhbb_marked_normalized_global_meromorphic slot colour n l hl hpar u v w b p q r s hu hv hw hb
  let a₀ : ℕ := (5 + K + L) / 2
  let aInf : ℤ := (1 + (N : ℤ) - K) / 2
  let U : Set ℂ := ({0, 1} : Set ℂ)ᶜ
  let E (y : ℂ) := (y ^ a₀ * (1 - y) ^ poleOrder) * H' y
  have hMem {y : ℂ} : y ∈ U ↔ y ≠ 0 ∧ y ≠ 1 := by simp [U]
  have hU : IsPreconnected U := by
    have hCount : ({0, 1} : Set ℂ).Countable :=
      ((Set.finite_singleton (1 : ℂ)).insert 0).countable
    exact (hCount.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])).2
  have hE : AnalyticOnNhd ℂ E U :=
    fun y hy => ((analyticAt_id.pow a₀).mul
      ((analyticAt_const.sub analyticAt_id).pow poleOrder)).mul (hHol' y hy)
  have hEP : Set.EqOn E P.eval U := by
    have hI : I ∈ U := hMem.mpr ⟨Complex.I_ne_zero, fun h => by
      simpa using congrArg Complex.im h⟩
    apply hE.eqOn_of_preconnected_of_eventuallyEq
      ((AnalyticOnNhd.eval_polynomial P).mono (Set.subset_univ _)) hU hI
    have hOpen : IsOpen {y : ℂ | 0 < y.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hOpen.eventually_mem (show I ∈ {y : ℂ | 0 < y.im} by simp)] with y hy
    have hy₀ : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hy₁ : y ≠ 1 := by
      rintro rfl
      simp at hy
    have hDenom : y ^ a₀ * (1 - y) ^ poleOrder ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hy₀) (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
    have hAgree : H' y = H y := (hUpper' y hy).trans (hUpper y hy).symm
    change (y ^ a₀ * (1 - y) ^ poleOrder) * H' y = P.eval y
    rw [hAgree, mul_comm]
    exact (eq_div_iff hDenom).mp (hRational y hy₀ hy₁)
  have hWeight : ((a₀ + poleOrder : ℕ) : ℤ) + aInf = degree := by
    have hNonneg (i : Puncture) : 0 ≤ doubledOccupation slot n l i := by
      classical
      unfold doubledOccupation
      apply List.sum_nonneg
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      split <;> omega
    rcases hpar with ⟨hM, hK, hL, hN⟩
    simp only [a₀, aInf, poleOrder, degree, M, K, L, N, grade, Int.natCast_add,
      Int.natCast_ediv, Int.toNat_of_nonneg (hNonneg _)]
    omega
  apply hhbb_native_d_infinity_powerSeries M K L N u v w b GInf P degree poleOrder hDegree hSum
  filter_upwards [tendsto_norm_cobounded_atTop (E := ℂ) |>.eventually_gt_atTop 1] with y hy
  have hy₀ : y ≠ 0 := by
    rintro rfl
    norm_num at hy
  have hy₁ : y ≠ 1 := by
    rintro rfl
    norm_num at hy
  have hFactor : 1 - y = y * (y⁻¹ - 1) := by
    rw [mul_sub, mul_inv_cancel₀ hy₀, mul_one]
  have hPower : y ^ a₀ * y ^ poleOrder * y ^ aInf = y ^ degree := by
    rw [← pow_add, ← zpow_natCast, ← zpow_add₀ hy₀, hWeight, zpow_natCast]
  have hClear : E y = P.eval y := hEP (hMem.mpr ⟨hy₀, hy₁⟩)
  have hInfAt : H' y = y ^ aInf * GInf y⁻¹ := hInf y hy
  rw [← hClear]
  change (y ^ a₀ * (1 - y) ^ poleOrder) * H' y = _
  rw [hInfAt, hFactor, mul_pow]
  calc
    _ = (y ^ a₀ * y ^ poleOrder * y ^ aInf) * (GInf y⁻¹ * (y⁻¹ - 1) ^ poleOrder) := by ring
    _ = _ := by rw [hPower]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalInfinityExpansion
