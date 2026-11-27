/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateSlot12Analytic
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summed upper half-turn exchange of the native Leech A iterate. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Coefficient
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalIterateInversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! The skew triangle sums by absolute antidiagonal regrouping near zero.
The two native energy series are analytic on the full normalized overlap,
where the identity theorem restores the exchange before the Laurent factors
are reinserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Topology
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeMixedIterateInversionCoefficient (aCoeff)
open NativeMixedIterateSlot12Coefficient (aCoeff_slot12_exchange)
open NativeMixedAIterateRadial (aJointTerm)
open NativeMixedIterateInversionGerm (principal_binomial_germ)
open NativeMixedPhysicalIterateInversion (aJoint_hasSum_iff_energy)
open private aCoeff_summable from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateRadialInversion
open private swapped_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
open private binomialCoeff hasSum_binomialCoeff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedProductSlot23Analytic

local notation "ℒ" => leechData
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)
private abbrev detectorPower (H J : ℕ) : ℂ :=
  ((weight J : ℂ) - (weight H : ℂ)) / 2

private theorem skew_phase (M K F : ℕ) :
    I ^ (2 * (F : ℤ) - weight M - weight K) =
      I ^ (-(weight M + weight K)) * (-1 : ℂ) ^ F := by
  rw [show 2 * (F : ℤ) - weight M - weight K =
      -(weight M + weight K) + 2 * (F : ℤ) by ring,
    zpow_add₀ Complex.I_ne_zero, zpow_mul,
    show I ^ (2 : ℤ) = -1 from (zpow_natCast I 2).trans Complex.I_sq,
    zpow_natCast]

private theorem coefficient_reflection (s t : Bool) (M K H J E : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    let b (F : ℕ) := (-1 : ℂ) ^ F *
      aCoeff (!s) t (weight K) (weight M) (weight H) (weight J) F Q (swapInput (s := s) P) R S
    aCoeff s t (weight M) (weight K) (weight H) (weight J) E P Q R S * (-1 : ℂ) ^ E =
      ((-1 : ℂ) ^ (3 + M) * I ^ (-(weight M + weight K))) *
        binomialCoeff (detectorPower H J) b E := by
  dsimp only
  let f (h F : ℕ) :=
    ((-1 : ℂ) ^ F *
      aCoeff (!s) t (weight K) (weight M) (weight H) (weight J) F
        Q (swapInput (s := s) P) R S) *
      (-1 : ℂ) ^ F * (Ring.choose (detectorPower H J - (F : ℂ)) h * (-1 : ℂ) ^ h)
  have hbin :
      binomialCoeff (detectorPower H J) (fun F => (-1 : ℂ) ^ F *
        aCoeff (!s) t (weight K) (weight M) (weight H) (weight J) F Q (swapInput (s := s) P) R S) E =
        ∑ h ∈ Finset.range (E + 1), f h (E - h) := by
    unfold binomialCoeff
    change (∑ p ∈ Finset.HasAntidiagonal.antidiagonal E, f p.2 p.1) = _
    calc
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal E, f p.1 p.2 :=
        Finset.Nat.sum_antidiagonal_swap (f := fun p => f p.1 p.2)
      _ = _ := Finset.Nat.sum_antidiagonal_eq_sum_range_succ f E
  rw [aCoeff_slot12_exchange s t M K (weight H) (weight J) P Q R S E hP hQ, hbin]
  simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hhE := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hsplit : E = (E - h) + h := (Nat.sub_add_cancel hhE).symm
  have hpow : (-1 : ℂ) ^ E = (-1 : ℂ) ^ (E - h) * (-1 : ℂ) ^ h :=
    (congrArg (fun n : ℕ => (-1 : ℂ) ^ n) hsplit).trans (pow_add _ _ _)
  rw [skew_phase, hpow]
  dsimp only [f]
  ring

private def energySum (a : ℕ → ℂ) (u : ℂ) : ℂ := ∑' E : ℕ, a E * u ^ E

private theorem energySum_analyticAt (a : ℕ → ℂ)
    (ha : ∀ u : ℂ, ‖u‖ < 1 → Summable (fun E : ℕ => a E * u ^ E))
    {u : ℂ} (hu : ‖u‖ < 1) : AnalyticAt ℂ (energySum a) u := by
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hp : 1 ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
    have hs := (ha ((r : ℝ) : ℂ) (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using hr')).norm
    exact p.le_radius_of_summable_norm (by
      simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using hs)
  have hu' : u ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    exact mem_ball_zero_iff.mpr hu
  have hAt := (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le hp)).analyticOnNhd u
    (Metric.eball_subset_eball hp hu')
  have hfun : p.sum = energySum a := by
    funext w
    change FormalMultilinearSeries.ofScalarsSum a w = _
    simp only [FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul, energySum]
  simpa only [hfun] using hAt

private theorem norm_lt_one_sub_iff (q : ℂ) :
    ‖q‖ < ‖1 - q‖ ↔ q.re < (1 / 2 : ℝ) := by
  rw [← sq_lt_sq₀ (norm_nonneg q) (norm_nonneg (1 - q)),
    Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

private theorem one_sub_ne_zero_of_lt {q : ℂ} (hq : ‖q‖ < ‖1 - q‖) : 1 - q ≠ 0 :=
  norm_pos_iff.mp ((norm_nonneg q).trans_lt hq)

private theorem energy_reflection_on_overlap (a b : ℕ → ℂ) (δ phase : ℂ)
    (ha : ∀ u : ℂ, ‖u‖ < 1 → Summable (fun E : ℕ => a E * u ^ E))
    (hb : ∀ u : ℂ, ‖u‖ < 1 → Summable (fun F : ℕ => b F * u ^ F))
    (hcoef : ∀ E : ℕ, a E * (-1 : ℂ) ^ E =
      phase * binomialCoeff δ (fun F => (-1 : ℂ) ^ F * b F) E)
    {q : ℂ} (hq : ‖q‖ < 1) (hq' : ‖q‖ < ‖1 - q‖) :
    HasSum (fun E : ℕ => a E * (-q) ^ E)
      (phase * ((1 - q) ^ δ * energySum b (q / (1 - q)))) := by
  let U := Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | w.re < (1 / 2 : ℝ)}
  let f (w : ℂ) := energySum a (-w)
  let g (w : ℂ) := phase * ((1 - w) ^ δ * energySum b (w / (1 - w)))
  have hU : IsPreconnected U :=
    ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (1 / 2 : ℝ))).isPreconnected
  have h0 : (0 : ℂ) ∈ U := by
    exact ⟨mem_ball_self zero_lt_one, by norm_num⟩
  have hf : AnalyticOnNhd ℂ f U := by
    intro w hw
    have hnorm := mem_ball_zero_iff.mp hw.1
    have hneg : ‖-w‖ < 1 := by simpa only [norm_neg] using hnorm
    exact (energySum_analyticAt a ha hneg).comp analyticAt_id.neg
  have hg : AnalyticOnNhd ℂ g U := by
    intro w hw
    have hnorm := mem_ball_zero_iff.mp hw.1
    have hlt := (norm_lt_one_sub_iff w).mpr hw.2
    have hne := one_sub_ne_zero_of_lt hlt
    have hratio : ‖w / (1 - w)‖ < 1 := by
      rwa [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
    have hbin : AnalyticAt ℂ (fun v : ℂ => (1 - v) ^ δ) w :=
      ((principal_binomial_germ δ).1 (-w)
        (mem_ball_zero_iff.mpr (by simpa only [norm_neg] using hnorm))).comp analyticAt_id.neg
    have hratioAt : AnalyticAt ℂ (fun v : ℂ => v / (1 - v)) w :=
      analyticAt_id.div (analyticAt_const.sub analyticAt_id) hne
    have henergy : AnalyticAt ℂ (fun v : ℂ => energySum b (v / (1 - v))) w :=
      AnalyticAt.comp (g := energySum b) (f := fun v : ℂ => v / (1 - v))
        (energySum_analyticAt b hb hratio) hratioAt
    exact analyticAt_const.mul (hbin.mul henergy)
  have hlocal : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    have hhalf := mem_ball_zero_iff.mp hw
    have hw₁ : ‖w‖ < 1 := by linarith
    let r : ℝ := ‖w‖ / (1 - ‖w‖)
    have hr₀ : 0 ≤ r := div_nonneg (norm_nonneg _) (sub_nonneg.mpr hw₁.le)
    have hr₁ : r < 1 := (div_lt_one (sub_pos.mpr hw₁)).mpr (by linarith)
    have hnorm : ‖(r : ℂ)‖ < 1 := by
      rwa [Complex.norm_real, Real.norm_of_nonneg hr₀]
    have hmajor : Summable (fun F : ℕ => ‖(-1 : ℂ) ^ F * b F‖ * r ^ F) := by
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_of_nonneg hr₀] using (hb (r : ℂ) hnorm).norm
    have hsum := (hasSum_binomialCoeff δ (fun F => (-1 : ℂ) ^ F * b F)
      hw₁ hmajor).mul_left phase
    have hrow (F : ℕ) :
        ((-1 : ℂ) ^ F * b F) * (-w / (1 - w)) ^ F =
          b F * (w / (1 - w)) ^ F := by
      rw [neg_div, neg_pow]
      calc
        _ = b F * (((-1 : ℂ) ^ F * (-1 : ℂ) ^ F) * (w / (1 - w)) ^ F) := by ring
        _ = _ := by rw [← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]
    simp only [hrow] at hsum
    have hsum' : HasSum (fun E : ℕ => a E * (-w) ^ E) (g w) := by
      refine hsum.congr_fun fun E => ?_
      rw [neg_pow, ← mul_assoc, hcoef, mul_assoc]
    exact hsum'.tsum_eq
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hU h0 hlocal
  have hqU : q ∈ U := ⟨mem_ball_zero_iff.mpr hq, (norm_lt_one_sub_iff q).mp hq'⟩
  have hs := (ha (-q) (by simpa only [norm_neg] using hq)).hasSum
  change HasSum (fun E : ℕ => a E * (-q) ^ E) (f q) at hs
  change HasSum (fun E : ℕ => a E * (-q) ^ E) (g q)
  rwa [heq hqU] at hs

/-- The normalized native energy series agree across the slot `(1,2)`
half-turn on the full overlap. The normalized variable is `q = (z - x) / z`. -/
theorem aCoeff_slot12_hasSum (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {q : ℂ} (hq : ‖q‖ < 1) (hq' : ‖q‖ < ‖1 - q‖) :
    HasSum (fun E : ℕ => aCoeff s t (weight M) (weight K) (weight H) (weight J) E
        P Q R S * (-q) ^ E)
      (((-1 : ℂ) ^ (3 + M) * I ^ (-(weight M + weight K))) *
        ((1 - q) ^ detectorPower H J *
          ∑' F : ℕ, aCoeff (!s) t (weight K) (weight M) (weight H) (weight J) F
            Q (swapInput (s := s) P) R S * (q / (1 - q)) ^ F)) := by
  exact energy_reflection_on_overlap _ _ _ _
    (fun _ hu => aCoeff_summable s t M K H J P Q R S hP hQ hR hS hu)
    (fun _ hu => aCoeff_summable (!s) t K M H J Q (swapInput (s := s) P) R S
      hQ (swapped_grade hP) hR hS hu)
    (fun E => coefficient_reflection s t M K H J E P Q R S hP hQ) hq hq'

private theorem relative_root_zpow {q : ℂ} (hq : ‖q‖ < ‖1 - q‖) (n : ℤ) :
    ((1 - q) ^ ((2 : ℂ)⁻¹)) ^ n = (1 - q) ^ ((n : ℂ) / 2) := by
  have hre : 0 < (1 - q).re := by
    have h := (norm_lt_one_sub_iff q).mp hq
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have him : (Complex.log (1 - q) * (2 : ℂ)⁻¹).im = (1 - q).arg / 2 := by
    rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.log_im]
    ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hre.le)
  have hmin : -Real.pi < (Complex.log (1 - q) * (2 : ℂ)⁻¹).im := by
    rw [him]
    linarith [Real.pi_pos]
  have hmax : (Complex.log (1 - q) * (2 : ℂ)⁻¹).im ≤ Real.pi := by
    rw [him]
    linarith [Real.pi_pos]
  rw [show (n : ℂ) / 2 = (2 : ℂ)⁻¹ * (n : ℂ) by ring,
    Complex.cpow_mul _ hmin hmax, Complex.cpow_intCast]

/-- The relative root used in the exchange is a lift of the outer coordinate
on the common radial domain. Its ratio to the original outer root is the
principal square root of `x / z`, with value one at `x / z = 1`. -/
theorem slot12_relative_root_sq {x z zRoot : ℂ} (hz : zRoot ^ 2 = z) (hz₀ : z ≠ 0) :
    (zRoot * (1 - (z - x) / z) ^ ((2 : ℂ)⁻¹)) ^ 2 = x := by
  rw [mul_pow, hz, Complex.cpow_ofNat_inv_pow (1 - (z - x) / z) 2]
  field_simp [hz₀]
  exact sub_sub_cancel z x

/-- Upper slot `(1,2)` exchange of the literal native mixed A double sum.
The outer root of the exchanged iterate is `xRoot`, its separation root is
`I * dRoot`, and the detector states retain their order. -/
theorem a_joint_iterate_hasSum_slot12 (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {x z xRoot zRoot dRoot : ℂ}
    (hz : zRoot ^ 2 = z) (hd : dRoot ^ 2 = x - z)
    (hxz : x ≠ z) (hr : ‖x - z‖ < min ‖x‖ ‖z‖)
    (hLift : xRoot = zRoot * (1 - (z - x) / z) ^ ((2 : ℂ)⁻¹)) :
    HasSum (aJointTerm s P Q R.val S.val dRoot zRoot)
      ((-1 : ℂ) ^ (3 + M) *
        ∑' p : ℤ × ℤ,
          aJointTerm (!s) Q (swapInput (s := s) P) R.val S.val (I * dRoot) xRoot p) := by
  let q : ℂ := (z - x) / z
  have hrad := lt_min_iff.mp hr
  have hzPos := (norm_nonneg (x - z)).trans_lt hrad.2
  have hz₀ := norm_pos_iff.mp hzPos
  have hx₀ := norm_pos_iff.mp ((norm_nonneg (x - z)).trans_lt hrad.1)
  have hx : xRoot ^ 2 = x := by rw [hLift, slot12_relative_root_sq hz hz₀]
  have hzR : zRoot ≠ 0 := fun h => hz₀ (by simpa [h] using hz.symm)
  have hxR : xRoot ≠ 0 := fun h => hx₀ (by simpa [h] using hx.symm)
  have hdR : dRoot ≠ 0 := by
    intro h
    exact hxz (sub_eq_zero.mp (by simpa [h] using hd.symm))
  have hu : 1 - q = x / z := by
    dsimp only [q]
    field_simp [hz₀]
    ring
  have hqNorm : ‖q‖ = ‖x - z‖ / ‖z‖ := by
    dsimp only [q]
    rw [norm_div, show z - x = -(x - z) by ring, norm_neg]
  have hq : ‖q‖ < 1 := by
    rw [hqNorm, div_lt_one hzPos]
    exact hrad.2
  have hq' : ‖q‖ < ‖1 - q‖ := by
    rw [hqNorm, hu, norm_div, div_lt_div_iff_of_pos_right hzPos]
    exact hrad.1
  have hsrcRatio : (dRoot / zRoot) ^ 2 = -q := by
    rw [div_pow, hd, hz]
    dsimp only [q]
    rw [← neg_div, neg_sub]
  have hswapRatio : (I * dRoot / xRoot) ^ 2 = q / (1 - q) := by
    rw [div_pow, mul_pow, Complex.I_sq, hd, hx, neg_one_mul, neg_sub, hu]
    dsimp only [q]
    field_simp [hx₀, hz₀]
  have hqSwap : ‖q / (1 - q)‖ < 1 := by
    rwa [norm_div, div_lt_one ((norm_nonneg q).trans_lt hq')]
  let m := weight M + weight K
  let n := weight J - weight H
  let value : ℂ := ∑' F : ℕ, aCoeff (!s) t (weight K) (weight M) (weight H) (weight J) F
    Q (swapInput (s := s) P) R S * (q / (1 - q)) ^ F
  have hswapEnergy := (aCoeff_summable (!s) t K M H J Q (swapInput (s := s) P) R S
    hQ (swapped_grade hP) hR hS hqSwap).hasSum
  have hswap := (aJoint_hasSum_iff_energy (!s) t K M H J Q (swapInput (s := s) P) R S
    hQ (swapped_grade hP) hR hS (mul_ne_zero Complex.I_ne_zero hdR) hxR value).mp
      (by simpa only [hswapRatio] using hswapEnergy)
  change HasSum _ (((I * dRoot) ^ (-(weight K + weight M)) * xRoot ^ n) * value) at hswap
  rw [add_comm (weight K) (weight M)] at hswap
  change HasSum _ (((I * dRoot) ^ (-m) * xRoot ^ n) * value) at hswap
  have hsrc := (aJoint_hasSum_iff_energy s t M K H J P Q R S hP hQ hR hS hdR hzR
    (((-1 : ℂ) ^ (3 + M) * I ^ (-m)) * ((1 - q) ^ detectorPower H J * value))).mp
      (by simpa only [hsrcRatio] using (aCoeff_slot12_hasSum s t M K H J P Q R S
        hP hQ hR hS hq hq'))
  change HasSum _ ((dRoot ^ (-m) * zRoot ^ n) *
    (((-1 : ℂ) ^ (3 + M) * I ^ (-m)) * ((1 - q) ^ detectorPower H J * value))) at hsrc
  have houter : xRoot ^ n = zRoot ^ n * (1 - q) ^ detectorPower H J := by
    have hcast : (n : ℂ) / 2 = detectorPower H J := by
      dsimp only [n, detectorPower]
      rw [Int.cast_sub]
    rw [show xRoot = zRoot * (1 - q) ^ ((2 : ℂ)⁻¹) from hLift, mul_zpow,
      relative_root_zpow hq', hcast]
  rw [hswap.tsum_eq, houter, mul_zpow]
  convert hsrc using 1
  ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateSlot12Analytic
