/- GID: D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MomentTransferWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized profile responses have uniformly vanishing price corrections. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace D5.S3.Arith.Robin.ForwardKernel.MomentTransferWeights

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs MomentTransferDefs

noncomputable section
set_option autoImplicit false

private lemma normalization_factor {θ X x : ℝ} (hX : 1 < X) (hx : X ≤ x) :
    Real.sqrt x * Real.sqrt (x ^ θ * Real.log x) /
        (x ^ θ * Real.sqrt (meanSquareScale θ X)) =
      dyadicU X x ^ dyadicR θ * Real.sqrt (Real.log x / Real.log X) := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := hX0.trans_le hx
  have hlX := Real.log_pos hX
  have hlx := Real.log_pos (hX.trans_le hx)
  have hp := Real.rpow_pos_of_pos hx0 θ
  have hq := Real.rpow_pos_of_pos hX0 (1 - θ)
  have hu := div_pos hx0 hX0
  have hs : 0 < Real.sqrt (meanSquareScale θ X) :=
    Real.sqrt_pos.mpr (mul_pos hq hlX)
  have he : (dyadicU X x ^ dyadicR θ) ^ 2 = x ^ (1 - θ) / X ^ (1 - θ) := by
    rw [dyadicU, dyadicR, kappa, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
    rw [Real.div_rpow hx0.le hX0.le]
  have he' : x ^ (1 - θ) * x ^ θ = x := by
    rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  have hleft : 0 ≤ Real.sqrt x * Real.sqrt (x ^ θ * Real.log x) /
      (x ^ θ * Real.sqrt (meanSquareScale θ X)) := by positivity
  have hright : 0 ≤ dyadicU X x ^ dyadicR θ *
      Real.sqrt (Real.log x / Real.log X) := by
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hleft hright).mp
  simp only [div_pow, mul_pow, Real.sq_sqrt hx0.le,
    Real.sq_sqrt (mul_pos hp hlx).le, he,
    Real.sq_sqrt (div_pos hlx hlX).le,
    Real.sq_sqrt (show 0 ≤ meanSquareScale θ X from (mul_pos hq hlX).le)]
  unfold meanSquareScale
  field_simp [hp.ne', hq.ne', hlX.ne']
  nlinarith [he']

/-- The normalized profile is a unit-interval integral of normalized increments. -/
theorem dyadicZ_eq_weighted_integral
    {E g : ℝ → ℝ} {θ X x : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ : 0 < θ) (hX : 4 ≤ X) (hx : X ≤ x) (hxx : x ≤ 2 * X) :
    dyadicZ E θ g X x =
      dyadicU X x ^ dyadicR θ * Real.sqrt (Real.log x / Real.log X) *
        (∫ s, g s * dyadicB E θ s x * priceRatio x (s * x ^ θ) ∂unitMeasure) := by
  have hx0 : 0 < x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 θ
  have hs := Real.sqrt_pos.mpr (mul_pos hh (Real.log_pos (by linarith : 1 < x)))
  have hn := WeightRemoval.normalized_eq (E := E) (g := g) (θ := θ) hx0
  have he : (∫ s, g s * dyadicB E θ s x * priceRatio x (s * x ^ θ) ∂unitMeasure) =
      (∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure) / Real.sqrt (x ^ θ * Real.log x) := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by dsimp [dyadicB]; ring)
  rw [he, ← normalization_factor (by linarith : 1 < X) hx]
  unfold dyadicZ
  have hn := (div_eq_iff (Real.sqrt_pos.mpr hx0).ne').mp hn
  rw [hn]
  field_simp [hs.ne']
  <;> simp only [mul_comm]

private lemma logarithmic_factor_bounds {X x : ℝ} (hX : 4 ≤ X)
    (hx : X ≤ x) (hxx : x ≤ 2 * X) :
    1 ≤ Real.sqrt (Real.log x / Real.log X) ∧
      Real.sqrt (Real.log x / Real.log X) - 1 ≤ Real.log 2 / Real.log X := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hlX := Real.log_pos (by linarith : 1 < X)
  have hlog : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx
  have hlog' : Real.log x ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne']
    exact Real.log_le_log hx0 hxx
  have hratio : 1 ≤ Real.log x / Real.log X := (le_div_iff₀ hlX).mpr (by simpa)
  have hs : 1 ≤ Real.sqrt (Real.log x / Real.log X) := by
    simpa using Real.sqrt_le_sqrt hratio
  refine ⟨hs, ?_⟩
  have hb : Real.log x / Real.log X ≤ 1 + Real.log 2 / Real.log X := by
    apply (div_le_iff₀ hlX).mpr
    field_simp
    nlinarith
  have hs2 := Real.sq_sqrt (by positivity : 0 ≤ Real.log x / Real.log X)
  nlinarith [sq_nonneg (Real.sqrt (Real.log x / Real.log X) - 1)]

/-- For sublinear windows the logarithmic and price corrections tend uniformly to one. -/
theorem eventually_normalized_price_factor {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop, 0 ≤ η X ∧
        ∀ x ∈ Icc X (2 * X), ∀ s ∈ Icc (0 : ℝ) 1,
          |Real.sqrt (Real.log x / Real.log X) * priceRatio x (s * x ^ θ) - 1| ≤ η X := by
  let η : ℝ → ℝ := fun X => Real.log 2 / Real.log X + 4 * X ^ (θ - 1)
  refine ⟨η, ?_, ?_⟩
  · have hp : Tendsto (fun X : ℝ => X ^ (θ - 1)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hθ1)
    have hl : Tendsto (fun X : ℝ => Real.log 2 / Real.log X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa only [η, mul_zero, add_zero] using hl.add (hp.const_mul 4)
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    have hX0 : 0 < X := by linarith
    have hlX := Real.log_pos (by linarith : 1 < X)
    refine ⟨by dsimp [η]; positivity, ?_⟩
    intro x hx s hs
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hu : 0 ≤ s * x ^ θ := mul_nonneg hs.1 (Real.rpow_nonneg hx0.le _)
    obtain ⟨hρ0, hρ1⟩ := WeightControl.price_bounds (x := x) (by linarith [hx.1]) hu
    obtain ⟨hL, hLerr⟩ := logarithmic_factor_bounds hX hx.1 hx.2
    have hρerr : 1 - priceRatio x (s * x ^ θ) ≤ 4 * X ^ (θ - 1) := by
      apply (WeightControl.priceRatio_sub_one (hX.trans hx.1) hu).2.trans
      calc
        4 * (s * x ^ θ) / x = 4 * s * x ^ (θ - 1) := by
          rw [Real.rpow_sub hx0, Real.rpow_one]; ring
        _ ≤ 4 * x ^ (θ - 1) := by
          nlinarith [Real.rpow_nonneg hx0.le (θ - 1), hs.2]
        _ ≤ 4 * X ^ (θ - 1) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hX0 hx.1 (by linarith)) (by norm_num)
    apply abs_le.mpr
    constructor
    · dsimp [η]
      nlinarith [div_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le hlX.le]
    · dsimp [η]
      nlinarith [Real.rpow_nonneg hX0.le (θ - 1)]

/-- The normalized increments are uniformly bounded on each fixed dyadic rectangle. -/
lemma dyadicB_uniform_bound {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (θ : ℝ) {X : ℝ} (hX : 4 ≤ X) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc X (2 * X),
      |dyadicB E θ s x| ≤ A := by
  have hX0 : 0 < X := by linarith
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE θ (b := 2 * X)
    hX0 (by linarith)
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt (x ^ θ * Real.log x))⁻¹)
      (Icc X (2 * X)) := by
    apply ContinuousOn.inv₀
    · apply ContinuousOn.sqrt
      exact (continuousOn_id.rpow_const (fun x hx => Or.inl (by
        change x ≠ 0; linarith [hx.1]))).mul
        (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
    · intro x hx
      exact (Real.sqrt_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith [hx.1]) θ)
        (Real.log_pos (by linarith [hx.1])))).ne'
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M * |L|, by positivity, ?_⟩
  intro s hs x hx
  have hLb' : |(Real.sqrt (x ^ θ * Real.log x))⁻¹| ≤ L := by
    simpa only [Real.norm_eq_abs] using hL x hx
  have hLb := hLb'.trans (le_abs_self L)
  dsimp [dyadicB]
  rw [div_eq_mul_inv, abs_mul]
  exact mul_le_mul (hMb x hx s hs) hLb (abs_nonneg _) hM

end
end D5.S3.Arith.Robin.ForwardKernel.MomentTransferWeights
