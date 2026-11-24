import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! The formal zero-cusp expansion of the common rational marked HHBB amplitude. -/

set_option autoImplicit false

open scoped ENNReal NNReal TensorProduct Topology
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalZeroExpansion

open NativeMixedUpperProductCusp (bProductCoeff)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd)
open PowerSeries (coeff)

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
      abs_of_nonneg r.2] using
      hC _ (Set.mem_range_self n)
  · intro z hz
    rw [eball_coe] at hz
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      h z (ball_subset_ball hr.le hz)

/-- Equality of cleared analytic germs yields the corresponding formal expansion. -/
private theorem hhbb_native_b_zero_powerSeries
    (M K L N : ℕ) (u v : TwistedEven) (w b : TwistedOdd)
    (G₀ : ℂ → ℂ) (P : Polynomial ℂ) (poleOrder : ℕ)
    (hsum : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun E : ℕ => -(bProductCoeff false false M K L N v w u b E) * z ^ E) (G₀ z))
    (hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), G₀ z * (1 - z) ^ poleOrder = P.eval z) :
    PowerSeries.mk (fun E : ℕ => -(bProductCoeff false false M K L N v w u b E)) =
      P.toPowerSeries * ↑(PowerSeries.invOneSubPow ℂ poleOrder) := by
  let B : PowerSeries ℂ :=
    PowerSeries.mk (fun E => -(bProductCoeff false false M K L N v w u b E))
  have hProduct (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (m : ℕ) :
      HasSum (fun n => coeff n (B * (1 - PowerSeries.X) ^ m) * z ^ n)
        (G₀ z * (1 - z) ^ m) := by
    induction m with
    | zero => simpa [B] using hsum z hz
    | succ m ih =>
      let S := B * (1 - PowerSeries.X) ^ m
      have hShiftCoeff (n : ℕ) : coeff (n + 1) (S * PowerSeries.X) = coeff n S := by
        simpa only [pow_one] using PowerSeries.coeff_mul_X_pow S 1 n
      have hShift : HasSum (fun n => coeff n (S * PowerSeries.X) * z ^ n)
          ((G₀ z * (1 - z) ^ m) * z) := by
        rw [← hasSum_nat_add_iff' 1]
        simp only [Finset.sum_range_one, PowerSeries.coeff_zero_mul_X, zero_mul, sub_zero,
          hShiftCoeff, pow_succ]
        simpa only [S, mul_assoc] using ih.mul_right z
      simpa only [pow_succ, ← mul_assoc, mul_sub, mul_one, map_sub, sub_mul, S] using ih.sub hShift
  have hPolynomial (z : ℂ) : HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
    rw [Polynomial.eval_eq_sum_range]
    exact hasSum_sum_of_ne_finset_zero fun n hn => by
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn : P.natDegree < n)]
  have hTaylor := HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesAt_of_hasSum_unitBall fun z hz => hProduct z hz poleOrder)
      (hasFPowerSeriesAt_of_hasSum_unitBall fun z _ => hPolynomial z) hgerm
  have hClear : B * (1 - PowerSeries.X) ^ poleOrder = P.toPowerSeries := by
    apply PowerSeries.ext
    intro n
    simpa only [Polynomial.coeff_coe] using
      congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ hTaylor) n
  change B = _
  rw [← hClear, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.inv_val, mul_one]

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedUpperProductCusp (bSewnNumerator)
open NativeHHBBNormalizedGlobalMeromorphic (hhbb_marked_normalized_global_meromorphic)
open NativeHHBBPolynomialFromInfinity (hhbb_marked_upper_common_rational)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (ball_subset_slitDomain)

open private sqrt_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBNormalizedGlobalMeromorphic

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The signed marked B energy series is the zero-cusp expansion of the common rational
amplitude after removing its zero-cusp prefactor. Its numerator is the same polynomial
obtained from the cleared infinity germ. -/
theorem hhbb_marked_b_zero_powerSeries {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a₁ : ℕ := (6 + M + K) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d z
    let G (z : ℂ) := (z - 1) ^ a₁ * GInf z
    let P := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j G) * Polynomial.X ^ (degree - j)
    PowerSeries.mk (fun E : ℕ => -(bProductCoeff false false M K L N v w u b E)) =
      P.toPowerSeries * ↑(PowerSeries.invOneSubPow ℂ a₁) := by
  intro grade V M K L N a₁ degree GInf G P
  obtain ⟨H, _, _, _, hUpper, ⟨⟨hG₀, hZero⟩, _, _⟩, _, ⟨_, hSum, _, _⟩, _⟩ :=
    hhbb_marked_normalized_global_meromorphic slot colour n l hl hpar u v w b p q r d hu hv hw hb
  obtain ⟨_, _, hPhysical, _⟩ :=
    hhbb_marked_upper_common_rational slot colour n l hl hpar u v w b p q r d hu hv hw hb
  let a₀ : ℕ := (5 + K + L) / 2
  let Z := Complex.sqrt
  let G₀ (y : ℂ) := -(I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
  let F (y : ℂ) := -(Z y ^ (-(6 + (K : ℤ) + L)) *
    I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
  have ha₀ : (a₀ : ℤ) = (5 + (K : ℤ) + L) / 2 := by
    norm_num only [a₀, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hClearedUpper (y : ℂ) (hy : y ∈ ball (0 : ℂ) 1) (him : 0 < y.im) :
      G₀ y * (1 - y) ^ a₁ = P.eval y := by
    have hy₀ : y ≠ 0 := by
      rintro rfl
      simp at him
    have hy₁ : y ≠ 1 := by
      rintro rfl
      simp at him
    have hCusp : y ^ a₀ * (Z y * F y) = G₀ y := by
      have hUpper' : H y = Z y * F y := hUpper y him
      have hZero' : H y = y ^ (-((5 + (K : ℤ) + L) / 2)) * G₀ y :=
        hZero y (ball_subset_slitDomain hy) hy₀
      rw [← hUpper', hZero', ← ha₀, ← mul_assoc, ← zpow_natCast y a₀, ← zpow_add₀ hy₀,
        add_neg_cancel, zpow_zero, one_mul]
    have hDenom : Z y * y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sqrt_ne_zero hy₀) (pow_ne_zero _ hy₀))
        (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
    have hF : F y = P.eval y / (Z y * y ^ a₀ * (1 - y) ^ a₁) := hPhysical y him
    calc
      G₀ y * (1 - y) ^ a₁ = (y ^ a₀ * (Z y * F y)) * (1 - y) ^ a₁ := by rw [hCusp]
      _ = F y * (Z y * y ^ a₀ * (1 - y) ^ a₁) := by ring
      _ = P.eval y := (eq_div_iff hDenom).mp hF
  have hClearedAnalytic :
      AnalyticOnNhd ℂ (fun y => G₀ y * (1 - y) ^ a₁) (ball (0 : ℂ) 1) := by
    intro y hy
    exact (hG₀ y (ball_subset_slitDomain hy)).mul ((analyticAt_const.sub analyticAt_id).pow a₁)
  have hPolyAnalytic : AnalyticOnNhd ℂ (fun y => P.eval y) (ball (0 : ℂ) 1) :=
    P.differentiable.differentiableOn.analyticOnNhd isOpen_ball
  let z₀ : ℂ := I / 2
  have hz₀ : z₀ ∈ ball (0 : ℂ) 1 := by
    norm_num [z₀, mem_ball, dist_zero_right, norm_div]
  have hz₀im : 0 < z₀.im := by
    norm_num [z₀, Complex.div_im, Complex.normSq_apply]
  have hImOpen : IsOpen {y : ℂ | 0 < y.im} := isOpen_lt continuous_const Complex.continuous_im
  have hNear : (fun y => G₀ y * (1 - y) ^ a₁) =ᶠ[𝓝 z₀] fun y => P.eval y := by
    filter_upwards [isOpen_ball.eventually_mem hz₀, hImOpen.eventually_mem hz₀im] with y hy him
    exact hClearedUpper y hy him
  have hDisk := hClearedAnalytic.eqOn_of_preconnected_of_eventuallyEq hPolyAnalytic
    isPreconnected_ball hz₀ hNear
  apply hhbb_native_b_zero_powerSeries M K L N u v w b G₀ P a₁ hSum
  filter_upwards [isOpen_ball.eventually_mem (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)]
    with y hy
  exact hDisk hy

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalZeroExpansion
