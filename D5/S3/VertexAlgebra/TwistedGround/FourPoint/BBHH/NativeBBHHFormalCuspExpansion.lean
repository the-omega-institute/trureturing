/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/BBHH/NativeBBHHFormalCuspExpansion
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formal cusp expansions and fixed-iterate coefficient readout for the actual BBHH numerator. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHNormalizedGerm
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalIterateExpansion
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalInfinityExpansion

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology
open Bornology Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHFormalCuspExpansion

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedOdd TwistedEven leechUnit)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeMixedUpperProductCusp (bProductCoeff)
open NativeBBHHNormalizedGerm
  (bbhh_actual_normalized_zero_germ bbhh_actual_normalized_collision_germ
    bbhh_actual_normalized_global_meromorphic bbhh_actual_normalized_common_rational)
open NativeHHBBFormalIterateExpansion (hhbb_iterate_germ_at_zero)
open NativeHHBBFormalInfinityExpansion (paddedReverse eventually_eq_paddedReverse)
open OriginalGaussianSewnAnalytic (coefficient)

open private sqrt_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBNormalizedGlobalMeromorphic
open private energySum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
open private hasFPowerSeriesAt_of_energy_sum numerator_hasFPowerSeriesAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalIterateExpansion
open private mk_eq_mul_invOneSubPow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalInfinityExpansion

/-- The exact numerator of the actual BBHH common rational function, read from
the signed swapped B series at infinity. -/
def bbhhCommonNumerator (M K H J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven) :
    Polynomial ℂ :=
  let a₀ := (5 + H + K) / 2
  let a₁ := (M + H + 6) / 2
  let kInf : ℤ := (1 + (J : ℤ) - H) / 2
  let d := ((a₀ : ℤ) + a₁ + kInf).toNat
  let G (z : ℂ) := (z - 1) ^ a₁ * (-energySum (bProductCoeff true true H M K J P Q R S) z)
  ∑ n ∈ Finset.range (d + 1), Polynomial.C (coefficient n G) * Polynomial.X ^ (d - n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The common numerator gives the three actual BBHH energy series. The
signed products have prefactors `y^(-a₀)` and `y^kInf` in the coordinates
`y` and `y⁻¹`. The plus iterate uses `t = (1-y)/y` and the fixed A mode.
Its binomial exponent includes the extra half-power from `sqrt y`. The
last identity gives the normalized iterate after clearing `t^(-a₁)`. -/
theorem bbhh_actual_formal_cusp_powerSeries_and_coeff (M K H J : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven)
    (hP : P.val ∈ actualGrade leechData leechUnit M) (hQ : Q.val ∈ actualGrade leechData leechUnit K)
    (hR : R.val ∈ actualGrade leechData leechUnit H) (hS : S.val ∈ actualGrade leechData leechUnit J) :
    let a₀ := (5 + H + K) / 2
    let a₁ := (M + H + 6) / 2
    let kInf : ℤ := (1 + (J : ℤ) - H) / 2
    let d := ((a₀ : ℤ) + a₁ + kInf).toNat
    let p := bbhhCommonNumerator M K H J P R Q S
    let β : ℂ := ((J : ℂ) - K + 1) / 2
    let α : ℂ := (a₀ : ℂ) + β
    let c (E : ℕ) := fixedAIterateCoeff true M H K J (fixedAExponent M H E) P R Q.val S.val
    p.natDegree ≤ d ∧
    PowerSeries.mk (fun E => -(bProductCoeff true true M H K J R Q P S E)) =
      p.toPowerSeries * ↑(PowerSeries.invOneSubPow ℂ a₁) ∧
    PowerSeries.mk (fun E => -(bProductCoeff true true H M K J P Q R S E)) =
      (Polynomial.C ((-1 : ℂ) ^ a₁) * paddedReverse d p).toPowerSeries *
        ↑(PowerSeries.invOneSubPow ℂ a₁) ∧
    PowerSeries.mk c =
      (∑ j ∈ p.support, PowerSeries.C (p.coeff j) * PowerSeries.binomialSeries ℂ (α - j)) ∧
    (∀ E : ℕ, c E = ∑ j ∈ p.support, p.coeff j * Ring.choose (α - j) E) ∧
    PowerSeries.binomialSeries ℂ ((a₁ : ℂ) - β) * PowerSeries.mk c =
      ∑ j ∈ p.support, PowerSeries.C (p.coeff j) *
        PowerSeries.binomialSeries ℂ ((a₀ : ℂ) + a₁ - j) := by
  classical
  intro a₀ a₁ kInf d p β α c
  let f (y : ℂ) := p.eval y / (y ^ a₀ * (1 - y) ^ a₁)
  let B₀ (y : ℂ) := -energySum (bProductCoeff true true M H K J R Q P S) y
  let BInf (z : ℂ) := -energySum (bProductCoeff true true H M K J P Q R S) z
  let A := energySum c
  obtain ⟨hd, _, hB, hA, hD⟩ :=
    bbhh_actual_normalized_common_rational M K H J P R Q S hP hQ hR hS
  obtain ⟨L, _, _, _, _, hL₀, hL₁, hLInf, hSumInf, _, _, _⟩ :=
    bbhh_actual_normalized_global_meromorphic M K H J P R Q S hP hQ hR hS
  have hCast₀ : (a₀ : ℤ) = (5 + (H : ℤ) + K) / 2 := by
    simp only [a₀, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hCast₁ : (a₁ : ℤ) = ((M : ℤ) + H + 6) / 2 := by
    simp only [a₁, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hCastD : (d : ℤ) = (a₀ : ℤ) + a₁ + kInf := by
    apply Int.toNat_of_nonneg
    dsimp only [kInf]
    omega

  have hSumA := (bbhh_actual_normalized_collision_germ M K H J P R Q S hP hQ hR hS).2.1
  have hActualA := hasFPowerSeriesAt_of_energy_sum hSumA
  have hChartA : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      f y = (1 - y) ^ (-(a₁ : ℤ)) * (Complex.sqrt y) ^ ((J : ℤ) - K + 1) *
        A ((1 - y) / y) := by
    have hRight : ∀ᶠ y : ℂ in 𝓝 (1 : ℂ), (1 / 2 : ℝ) < y.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem (by norm_num)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hRight, self_mem_nhdsWithin]
      with y hy hy₁
    have hy₀ : y ≠ 0 := by
      rintro rfl
      norm_num at hy
    have hr := sqrt_ne_zero hy₀
    calc
      f y = L y := (hA y hy hy₁).unique (hL₁ y hy hy₁).1
      _ = _ := by
        rw [(hL₁ y hy hy₁).2, hCast₁, zpow_add₀ hr, zpow_one]
        change _ = (1 - y) ^ _ * (Complex.sqrt y ^ ((J : ℤ) - K) * Complex.sqrt y) *
          energySum c ((1 - y) / y)
        ring
  have hGermA := hhbb_iterate_germ_at_zero (H := f) (A := A) p a₀ a₁ K J
    hActualA.analyticAt.continuousAt (Eventually.of_forall fun _ => rfl) hChartA
  have hTaylorA := hActualA.eq_formalMultilinearSeries
    ((numerator_hasFPowerSeriesAt p α).congr hGermA.symm)
  have hCoeffA (E : ℕ) : c E = ∑ j ∈ p.support, p.coeff j * Ring.choose (α - j) E := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun F => FormalMultilinearSeries.coeff F E) hTaylorA
  have hSeriesA : PowerSeries.mk c =
      ∑ j ∈ p.support, PowerSeries.C (p.coeff j) * PowerSeries.binomialSeries ℂ (α - j) := by
    ext E
    simpa only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul,
      PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] using hCoeffA E
  refine ⟨hd, ?_, ?_, hSeriesA, hCoeffA, ?_⟩
  · have hSum₀ :=
      (bbhh_actual_normalized_zero_germ M K H J P R Q S hP hQ hR hS).2.2.1
    apply mk_eq_mul_invOneSubPow hSum₀
    have hGerm₀ : (fun y => B₀ y * (1 - y) ^ a₁) =ᶠ[𝓝[≠] (0 : ℂ)] p.eval := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (ball_mem_nhds (0 : ℂ) zero_lt_one), self_mem_nhdsWithin] with y hy hy₀
      have hy₁ : y ≠ 1 := fun h => by simp [h] at hy
      have hDenom : y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hy₀) (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
      have hVal : f y = y ^ (-(a₀ : ℤ)) * B₀ y :=
        (neg_injective ((hB y hy hy₀).unique (hL₀ y hy hy₀).1)).trans
          (by simpa only [← hCast₀] using (hL₀ y hy hy₀).2)
      have hClear := (div_eq_iff hDenom).mp hVal
      rw [zpow_neg, zpow_natCast] at hClear
      calc
        B₀ y * (1 - y) ^ a₁ =
            (y ^ a₀)⁻¹ * y ^ a₀ * (B₀ y * (1 - y) ^ a₁) := by
          rw [inv_mul_cancel₀ (pow_ne_zero _ hy₀), one_mul]
        _ = _ := by rw [hClear]; ring
    have hCont : ContinuousAt (fun y => B₀ y * (1 - y) ^ a₁) 0 :=
      (hasFPowerSeriesAt_of_energy_sum hSum₀).continuousAt.mul
        ((continuousAt_const.sub continuousAt_id).pow a₁)
    exact (hCont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      p.continuous.continuousAt).mp hGerm₀
  · have hExterior : ∀ᶠ y in cobounded ℂ,
        p.eval y = y ^ d * (BInf y⁻¹ * (y⁻¹ - 1) ^ a₁) := by
      filter_upwards [tendsto_norm_cobounded_atTop (E := ℂ) |>.eventually_gt_atTop 1]
        with y hy
      have hy₀ := norm_pos_iff.mp (zero_lt_one.trans hy)
      have hy₁ : y ≠ 1 := fun h => by simp [h] at hy
      have hDenom : y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hy₀) (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
      have hVal : f y = y ^ kInf * BInf y⁻¹ :=
        (neg_injective ((hD y hy).unique (hLInf y hy).1)).trans (hLInf y hy).2
      have hFactor : 1 - y = y * (y⁻¹ - 1) := by
        rw [mul_sub, mul_inv_cancel₀ hy₀, mul_one]
      have hPow : y ^ a₀ * y ^ a₁ * y ^ kInf = y ^ d := by
        rw [← pow_add, ← zpow_natCast, ← zpow_add₀ hy₀, Nat.cast_add, ← hCastD, zpow_natCast]
      calc
        p.eval y = y ^ kInf * BInf y⁻¹ * (y ^ a₀ * (1 - y) ^ a₁) :=
          (div_eq_iff hDenom).mp hVal
        _ = _ := by rw [hFactor, mul_pow, ← hPow]; ring
    have hGermInf := eventually_eq_paddedReverse (P := p) (degree := d) (GInf := BInf) hd
      (hasFPowerSeriesAt_of_energy_sum hSumInf).continuousAt hExterior
    apply mk_eq_mul_invOneSubPow hSumInf
    filter_upwards [hGermInf] with z hz
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hz,
      show (1 - z : ℂ) = -1 * (z - 1) by ring, mul_pow, mul_left_comm]
  · rw [hSeriesA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← PowerSeries.binomialSeries_add]
    congr 2
    dsimp only [α]
    ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHFormalCuspExpansion
