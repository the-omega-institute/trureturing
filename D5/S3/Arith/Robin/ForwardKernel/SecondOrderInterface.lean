/- GID: D5/S3/Arith/Robin/ForwardKernel/SecondOrderInterface
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/SecondOrderInterface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Macroscopic covariance gives uniform second moments and the second order interface. -/

import D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightedCovariance
import D5.S3.Arith.Robin.ForwardKernel.MacroscopicFreezing
import D5.S3.Arith.Robin.ForwardKernel.MomentInterfaceBounds
import D5.S3.Arith.Robin.ForwardKernel.DyadicMacroMoments

/-! The weighted Brownian covariance law and its uniform second moment interface. -/

namespace D5.S3.Arith.Robin.ForwardKernel.SecondOrderInterface

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs VarianceTransfer MomentTransferDefs MacroscopicVarianceDefs
open DyadicProbability DyadicMacroMoments

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Power lengths with a unit parameter have size at most two and derivative at most one. -/
lemma power_length_bounds {θ s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    MacroscopicLengthBounds (fun u : ℝ => s * u ^ θ) 2 1 := by
  have hu0 (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) : 0 < u := by linarith [hu.1]
  have hd (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) :
      HasDerivWithinAt (fun u : ℝ => s * u ^ θ) (s * (θ * u ^ (θ - 1)))
        (Icc (1 : ℝ) 2) u :=
    ((Real.hasDerivAt_rpow_const (Or.inl (hu0 u hu).ne')).const_mul s).hasDerivWithinAt
  refine ⟨contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne (fun u hu => (hu0 u hu).ne')), ?_, ?_⟩
  · intro u hu
    have hpow := Real.rpow_le_self_of_one_le hu.1 hθ1.le
    exact ⟨mul_nonneg hs.1 (Real.rpow_nonneg (hu0 u hu).le _), by
      dsimp
      exact (mul_le_of_le_one_left (Real.rpow_nonneg (hu0 u hu).le _) hs.2).trans (hpow.trans hu.2)⟩
  · intro u hu
    rw [(hd u hu).derivWithin (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2) u hu)]
    have hp : 0 ≤ u ^ (θ - 1) := Real.rpow_nonneg (hu0 u hu).le _
    have hp1 : u ^ (θ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by linarith)
    rw [abs_of_nonneg (mul_nonneg hs.1 (mul_nonneg hθ.le hp))]
    calc
      s * (θ * u ^ (θ - 1)) ≤ 1 * (1 * 1) :=
        mul_le_mul hs.2 (mul_le_mul hθ1.le hp1 hp (by norm_num)) (by positivity) (by norm_num)
      _ = 1 := by ring

/-- The normalized moving increments have an explicit uniform second moment bound. -/
theorem explicit_second_moment_bound {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ 2 ∂dyadicProbabilityMeasure X) ≤ 1760 / Real.log 2 := by
  have hθ := hB.1.trans hB.2.1
  have hθ1 := hB.2.2.1.trans hB.2.2.2
  apply MomentInterfaceBounds.normalized_even_moment_bound (m := 1) hE hθ.le (by norm_num)
  filter_upwards [MacroscopicFreezing.normalized_square_eventually hE hB hV
    (show (1 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with X hb hX
  intro s hs
  have hS : 0 < varianceScale θ X := by
    dsimp [varianceScale]
    exact mul_pos (mul_pos (zero_lt_one.trans hX) (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _)) (Real.log_pos hX)
  have hh := (div_le_iff₀ hS).mp (hb _ (power_length_bounds hθ hθ1 hs))
  have heq : (∫ x in X..(2 * X), |increment E (s * x ^ θ) x| ^ (2 * 1)) =
      ∫ x in X..(2 * X), macroIncrement E (fun u => s * u ^ θ) θ X x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 < x := (zero_lt_one.trans hX).trans_le (uIcc_of_le (by linarith : X ≤ 2 * X) ▸ hx).1
    dsimp [macroIncrement]
    rw [Real.div_rpow hx0.le (zero_lt_one.trans hX).le]
    simp only [Nat.mul_one, sq_abs]
    congr 2
    field_simp [(Real.rpow_pos_of_pos (zero_lt_one.trans hX) θ).ne']
  rw [heq]
  simp only [pow_one]
  convert hh using 1 <;> dsimp [varianceScale] <;> ring


private lemma normalized_difference_le {E : ℝ → ℝ} {θ X s t K : ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ : 0 ≤ θ) (hX : 1 < X)
    (hraw : (∫ x in X..(2*X), (increment E (s*x^θ) x-increment E (t*x^θ) x)^2) ≤
      K * varianceScale θ X) :
    (∫ x, (dyadicB E θ s x-dyadicB E θ t x)^2 ∂dyadicProbabilityMeasure X) ≤ K / Real.log 2 := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hXX : X ≤ 2*X := by linarith
  have hp : Continuous (fun x : ℝ => x^θ) := Real.continuous_rpow_const hθ
  have hi : IntervalIntegrable
      (fun x => (increment E (s*x^θ) x-increment E (t*x^θ) x)^2) volume X (2*X) := by
    have hh := (increment_product_comp_integrableOn (μ := volume) (K := uIcc X (2*X)) hE isCompact_uIcc
      (u := fun x : ℝ => (s-t)*x^θ) (x := fun x : ℝ => x+t*x^θ)
      (v := fun x : ℝ => (s-t)*x^θ) (y := fun x : ℝ => x+t*x^θ)
      (continuous_const.mul hp) (continuous_id.add (continuous_const.mul hp))
      (continuous_const.mul hp) (continuous_id.add (continuous_const.mul hp))).intervalIntegrable
    apply hh.congr
    intro x _
    have he : x+t*x^θ+(s-t)*x^θ=x+s*x^θ := by ring
    simp only [increment, he]
    ring
  have hscale : 0 < varianceScale θ X := by
    dsimp [varianceScale]
    exact mul_pos (mul_pos hX0 (Real.rpow_pos_of_pos hX0 _)) (Real.log_pos hX)
  have hpoint (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      (dyadicB E θ s x-dyadicB E θ t x)^2 / x ≤
        (increment E (s*x^θ) x-increment E (t*x^θ) x)^2 / varianceScale θ X := by
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hsqrt : Real.sqrt (x^θ*Real.log x)^2=x^θ*Real.log x :=
      Real.sq_sqrt (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_pos (hX.trans_le hx.1)).le)
    rw [dyadicB, dyadicB, ← sub_div, div_pow, hsqrt, div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg _) hscale
    dsimp [varianceScale]
    calc
      X*X^θ*Real.log X ≤ x*x^θ*Real.log x :=
        mul_le_mul (mul_le_mul hx.1 (Real.rpow_le_rpow hX0.le hx.1 hθ)
          (Real.rpow_nonneg hX0.le _) hx0.le) (Real.log_le_log hX0 hx.1)
          (Real.log_pos hX).le (by positivity)
      _ = _ := by ring
  rw [dyadicProbabilityMeasure_integral hX0]
  have hh : (∫ x in X..(2*X), (dyadicB E θ s x-dyadicB E θ t x)^2/x) ≤
      (∫ x in X..(2*X), (increment E (s*x^θ) x-increment E (t*x^θ) x)^2) / varianceScale θ X := by
    rw [intervalIntegral.integral_of_le hXX, intervalIntegral.integral_of_le hXX, ← integral_div]
    apply integral_mono_of_nonneg
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact div_nonneg (sq_nonneg _) (hX0.trans hx.1).le)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hXX).mp hi |>.div_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hpoint x ⟨hx.1.le, hx.2⟩
  apply div_le_div_of_nonneg_right (hh.trans ?_) (Real.log_pos (by norm_num)).le
  exact (div_le_iff₀ hscale).2 (by simpa only [mul_comm K] using hraw)

/-- Nearby time parameters have an eventual squared-distance modulus with constant 120/log 2. -/
theorem time_modulus {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |s - t| ≤ δ →
        (∫ x, (dyadicB E θ s x - dyadicB E θ t x) ^ 2 ∂dyadicProbabilityMeasure X) ≤
          120 * δ / Real.log 2 + η := by
  intro δ hδ _hδ1 η hη
  have hθ := hB.1.trans hB.2.1
  have hθ1 := hB.2.2.1.trans hB.2.2.2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε := η*Real.log 2/(2560*δ)
  let τ := η*Real.log 2/(480*δ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hratio : Tendsto (fun X : ℝ => X^θ/X) atTop (𝓝 0) := by
    simpa only [fixedLength, one_mul] using
      FixedLengthCovariance.length_div_tendsto_zero hθ1 1
  have hlo := FixedLengthCovariance.shifted_band (c := 2*δ) (d := 4) (q := 1) (r := 0)
    hB.2.1 hB.2.2.1 hθ1 (by positivity) (by norm_num) (by norm_num) (by norm_num)
  have hhi := FixedLengthCovariance.shifted_band (c := 2*δ) (d := 1/2) (q := 4) (r := 0)
    hB.2.1 hB.2.2.1 hθ1 (by positivity) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (4:ℝ), hlo, hhi,
    LocalVarianceBand.variance_window_eventually hV ε hε,
    hratio.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hratio.eventually (gt_mem_nhds hτ)] with X hX hlo hhi hv hr1 hrτ
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hh : 0 < X^θ := Real.rpow_pos_of_pos hX0 _
  have hhX : X^θ ≤ X := ((div_lt_one hX0).mp hr1).le
  simp only [zero_mul, add_zero, one_mul, fixedLength] at hlo hhi
  intro s hs t ht hst
  let p := fun x : ℝ => x+s*x^θ
  let q := fun x : ℝ => x+t*x^θ
  have hd (v : ℝ) (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      HasDerivWithinAt (fun x : ℝ => x+v*x^θ) (1+v*(θ*x^(θ-1))) (Icc X (2*X)) x :=
    ((hasDerivAt_id x).add ((Real.hasDerivAt_rpow_const (Or.inl (hX0.trans_le hx.1).ne')).const_mul v)).hasDerivWithinAt
  have himg (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      x+v*x^θ ∈ Icc X (2*X+2*X^θ) := by
    have hx0 := hX0.trans_le hx.1
    have hp : x^θ ≤ 2*X^θ := by
      calc
        x^θ ≤ (2*X)^θ := Real.rpow_le_rpow hx0.le hx.2 hθ.le
        _ = (2:ℝ)^θ*X^θ := Real.mul_rpow (by norm_num) hX0.le
        _ ≤ 2*X^θ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hθ1.le) hh.le
    constructor
    · nlinarith [Real.rpow_nonneg hx0.le θ, hv.1, hx.1]
    · nlinarith [hv.2, hx.2, Real.rpow_nonneg hx0.le θ]
  have hraw := LocalVarianceBand.local_endpoint_bound hE hB
    (show X ≤ 2*X by linarith) (show X ≤ 2*X+2*X^θ by linarith)
    (show 0 < 2*δ*X^θ by positivity) (show (0:ℝ)<1 by norm_num)
    hX hε.le (show X/2≤X by linarith) (show 2*X+2*X^θ≤4*X by linarith)
    hlo.1 (by convert hhi.2 using 1 <;> ring) hv
    (fun x hx => (hd s x hx).continuousWithinAt) (fun x hx => (hd t x hx).continuousWithinAt)
    (hd s) (hd t) (by
      intro x hx
      have hp : 0 ≤ θ*x^(θ-1) := mul_nonneg hθ.le (Real.rpow_nonneg (hX0.trans_le hx.1).le _)
      constructor <;> nlinarith [hs.1, ht.1])
    (fun x hx => ⟨himg s hs x hx, himg t ht x hx⟩) (by
      intro x hx
      have hxp : x^θ ≤ 2*X^θ := by
        calc
          x^θ ≤ (2*X)^θ := Real.rpow_le_rpow (hX0.trans_le hx.1).le hx.2 hθ.le
          _ = (2:ℝ)^θ*X^θ := Real.mul_rpow (by norm_num) hX0.le
          _ ≤ 2*X^θ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_self_of_one_le (by norm_num) hθ1.le) hh.le
      have heq : (x+t*x^θ)-(x+s*x^θ)=(t-s)*x^θ := by ring
      rw [heq, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hX0.trans_le hx.1).le _), abs_sub_comm]
      exact (mul_le_mul_of_nonneg_right hst (Real.rpow_nonneg (hX0.trans_le hx.1).le _)).trans
        (by nlinarith))
  have hraw' : (∫ x in X..(2*X), (increment E (s*x^θ) x-increment E (t*x^θ) x)^2) ≤
      (120*δ+η*Real.log 2)*varianceScale θ X := by
    have heq : (fun x => (increment E (s*x^θ) x-increment E (t*x^θ) x)^2) =
        (fun x => (E (x+t*x^θ)-E (x+s*x^θ))^2) := by
      ext x
      dsimp [increment]
      ring
    rw [heq]
    apply hraw.trans
    have hτX : X^θ < τ*X := (div_lt_iff₀ hX0).mp hrτ
    have hεeq : 640*δ*ε=η*Real.log 2/4 := by dsimp [ε]; field_simp; ring
    have hτeq : 240*δ*τ=η*Real.log 2/2 := by dsimp [τ]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hτX.le (show 0≤240*δ by positivity)
    have he : 240*δ*X^θ+640*δ*ε*X ≤ η*Real.log 2*X := by nlinarith
    have hz := mul_le_mul_of_nonneg_left he (mul_nonneg hh.le (Real.log_pos hX1).le)
    dsimp [varianceScale]
    norm_num only [div_one] at hraw ⊢
    nlinarith
  have hn := normalized_difference_le hE hθ.le hX1 hraw'
  apply hn.trans_eq
  field_simp
  <;> ring


private lemma weighted_product_integrable {E ψ : ℝ → ℝ} {θ X s t : ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ : 0 ≤ θ) (hX : 1 < X)
    (hψ : ContinuousOn ψ (Icc X (2*X))) :
    Integrable (fun x => ψ x*dyadicB E θ s x*dyadicB E θ t x)
      (dyadicProbabilityMeasure X) := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hc : ContinuousOn (fun x => ψ x / (Real.sqrt (x^θ*Real.log x)^2*x)) (uIcc X (2*X)) := by
    rw [uIcc_of_le (by linarith : X ≤ 2*X)]
    apply hψ.div
      ((((continuousOn_id.rpow_const (fun x hx => Or.inr hθ)).mul
        (continuousOn_id.log (fun x hx => (hX0.trans_le hx.1).ne'))).sqrt.pow 2).mul continuousOn_id)
    intro x hx
    exact mul_ne_zero (pow_ne_zero _ (Real.sqrt_pos.mpr (mul_pos
      (Real.rpow_pos_of_pos (hX0.trans_le hx.1) _) (Real.log_pos (hX.trans_le hx.1)))).ne')
      (hX0.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x => increment E (s*x^θ) x*increment E (t*x^θ) x) volume X (2*X) :=
    (increment_product_comp_integrableOn hE isCompact_uIcc
      (continuous_const.mul (Real.continuous_rpow_const hθ)) continuous_id
      (continuous_const.mul (Real.continuous_rpow_const hθ)) continuous_id).intervalIntegrable
  apply dyadicProbabilityMeasure_integrable hX0
  convert hi.continuousOn_mul hc using 1
  ext x
  dsimp [dyadicB]
  ring

private lemma macro_probability_identity {E φ : ℝ → ℝ} {θ X s t : ℝ}
    (hX : 1 < X) :
    weightedMacroCovariance E (fun u => s*u^θ) (fun u => t*u^θ)
      (fun u => φ u*u^(-1-θ)) θ X / Real.log 2 =
      ∫ x, (φ (dyadicU X x)*Real.log x/Real.log X)*dyadicB E θ s x*dyadicB E θ t x
        ∂dyadicProbabilityMeasure X := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  rw [dyadicProbabilityMeasure_integral hX0, weightedMacroCovariance,
    ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith : X ≤ 2*X)] at hx
  have hx0 : 0 < x := hX0.trans_le hx.1
  have hden : Real.sqrt (x^θ*Real.log x)^2=x^θ*Real.log x :=
    Real.sq_sqrt (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_pos (hX.trans_le hx.1)).le)
  have hp : (x/X)^(-1-θ) = X*X^θ/(x*x^θ) := by
    rw [Real.div_rpow hx0.le hX0.le]
    have he (v : ℝ) (hv : 0 < v) : v^(-1-θ) = (v*v^θ)⁻¹ := by
      rw [show -1-θ=-(1+θ) by ring, Real.rpow_neg hv.le,
        Real.rpow_add hv, Real.rpow_one]
    rw [he x hx0, he X hX0]
    field_simp
  have hlen (v : ℝ) : X^θ*(v*(x/X)^θ)=v*x^θ := by
    rw [Real.div_rpow hx0.le hX0.le]
    field_simp [(Real.rpow_pos_of_pos hX0 θ).ne']
  dsimp [macroIncrement]
  rw [hlen s, hlen t, hp]
  dsimp [dyadicB, dyadicU, varianceScale]
  have hlog := Real.log_pos (hX.trans_le hx.1)
  have hsqrt : Real.sqrt (x^θ*Real.log x) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hsqrt, (Real.log_pos hX).ne', hX0.ne', hx0.ne',
    (Real.rpow_pos_of_pos hX0 θ).ne', (Real.rpow_pos_of_pos hx0 θ).ne']
  rw [hden]
  ring

private lemma probability_weight_error {E φ : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    {X K : ℝ} (hX : 4 ≤ X) (hφ : ContinuousOn φ (Icc (1:ℝ) 2))
    (hK : 0 ≤ K) (hbφ : ∀ u ∈ Icc (1:ℝ) 2, |φ u| ≤ K)
    (hb : ∀ s ∈ Icc (0:ℝ) 1,
      (∫ x, |dyadicB E θ s x|^2 ∂dyadicProbabilityMeasure X) ≤ 1760/Real.log 2)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |weightedDyadicCovariance E φ θ θ X s t -
      weightedMacroCovariance E (fun u => s*u^θ) (fun u => t*u^θ)
        (fun u => φ u*u^(-1-θ)) θ X / Real.log 2| ≤ 3520*K/Real.log X := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hθ : 0 ≤ θ := (hB.1.trans hB.2.1).le
  have hU : MapsTo (dyadicU X) (Icc X (2*X)) (Icc (1:ℝ) 2) := by
    intro x hx
    exact ⟨(le_div_iff₀ hX0).2 (by simpa [dyadicU] using hx.1),
      (div_le_iff₀ hX0).2 hx.2⟩
  have hc : ContinuousOn (fun x => φ (dyadicU X x)) (Icc X (2*X)) :=
    hφ.comp (continuous_id.div_const X).continuousOn hU
  have hlog : ContinuousOn (fun x => Real.log x/Real.log X) (Icc X (2*X)) :=
    (continuousOn_id.log (fun x hx => (hX0.trans_le hx.1).ne')).div_const _
  have hi := weighted_product_integrable (s := s) (t := t) hE hθ hX1 hc
  have hi' := weighted_product_integrable (s := s) (t := t) hE hθ hX1 (hc.mul hlog)
  have hsq (v : ℝ) : Integrable (fun x => dyadicB E θ v x^2) (dyadicProbabilityMeasure X) := by
    simpa only [one_mul, pow_two] using weighted_product_integrable (ψ := fun _ => 1) (s := v) (t := v) hE hθ hX1 continuousOn_const
  have hiLog : Integrable (fun x => (φ (dyadicU X x)*Real.log x/Real.log X)*
      dyadicB E θ s x*dyadicB E θ t x) (dyadicProbabilityMeasure X) := by
    simpa only [Pi.mul_apply, mul_div_assoc] using hi'
  rw [macro_probability_identity hX1, weightedDyadicCovariance, ← integral_sub hi hiLog]
  have hAE : ∀ᵐ x ∂dyadicProbabilityMeasure X, x ∈ Icc X (2*X) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => ⟨h.1.le, h.2⟩)
  have herr := norm_integral_le_of_norm_le
    (f := fun x => φ (dyadicU X x)*dyadicB E θ s x*dyadicB E θ t x-
      (φ (dyadicU X x)*Real.log x/Real.log X)*dyadicB E θ s x*dyadicB E θ t x)
    (((hsq s).add (hsq t)).const_mul (K*Real.log 2/Real.log X)) (by
      filter_upwards [hAE] with x hx
      have hx0 := hX0.trans_le hx.1
      have hl : 0 ≤ Real.log x-Real.log X := sub_nonneg.mpr (Real.log_le_log hX0 hx.1)
      have hl' : Real.log x-Real.log X ≤ Real.log 2 := by
        have hh := Real.log_le_log hx0 hx.2
        rw [Real.log_mul (by norm_num) hX0.ne'] at hh
        linarith
      have heq : φ (dyadicU X x)*dyadicB E θ s x*dyadicB E θ t x-
          (φ (dyadicU X x)*Real.log x/Real.log X)*dyadicB E θ s x*dyadicB E θ t x =
          φ (dyadicU X x)*(1-Real.log x/Real.log X)*(dyadicB E θ s x*dyadicB E θ t x) := by ring
      rw [Real.norm_eq_abs, heq, abs_mul, abs_mul]
      have hlb : |1-Real.log x/Real.log X| ≤ Real.log 2/Real.log X := by
        rw [show 1-Real.log x/Real.log X=-(Real.log x-Real.log X)/Real.log X by field_simp [(Real.log_pos hX1).ne']; ring,
          abs_div, abs_neg, abs_of_nonneg hl, abs_of_pos (Real.log_pos hX1)]
        exact div_le_div_of_nonneg_right hl' (Real.log_pos hX1).le
      have hp : |dyadicB E θ s x*dyadicB E θ t x| ≤
          dyadicB E θ s x^2+dyadicB E θ t x^2 := by
        simpa using MacroscopicWeightedCovariance.young_abs
          (by norm_num : (0 : ℝ) < 1) (dyadicB E θ s x) (dyadicB E θ t x)
      have hh := mul_le_mul (mul_le_mul (hbφ _ (hU hx)) hlb (abs_nonneg _) hK) hp
        (abs_nonneg _) (mul_nonneg hK (div_nonneg
          (Real.log_pos (by norm_num : (1:ℝ)<2)).le (Real.log_pos hX1).le))
      convert hh using 1 <;> dsimp only [Pi.add_apply] <;> ring)
  rw [Real.norm_eq_abs, integral_const_mul, integral_add' (hsq s) (hsq t)] at herr
  have hbs := hb s hs
  have hbt := hb t ht
  simp only [sq_abs] at hbs hbt
  apply herr.trans
  calc
    _ ≤ (K*Real.log 2/Real.log X)*(1760/Real.log 2+1760/Real.log 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hbs hbt) (div_nonneg
        (mul_nonneg hK (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_pos hX1).le)
    _ = _ := by field_simp; ring


private lemma covariance_pointwise {E φ : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hφ : ContinuousOn φ (Icc (1:ℝ) 2))
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    Tendsto (fun X => weightedDyadicCovariance E φ θ θ X s t) atTop
      (𝓝 (kappa θ*min s t*(∫ u in (1:ℝ)..2, φ u/u)/Real.log 2)) := by
  have hθ := hB.1.trans hB.2.1
  have hθ1 := hB.2.2.1.trans hB.2.2.2
  have hs' := power_length_bounds hθ hθ1 hs
  have ht' := power_length_bounds hθ hθ1 ht
  have hw : ContinuousOn (fun u => φ u*u^(-1-θ)) (Icc (1:ℝ) 2) :=
    hφ.mul (continuousOn_id.rpow_const (fun u hu => Or.inl (by change u ≠ 0; linarith [hu.1])))
  have hm := (MacroscopicWeightedCovariance.weighted_covariance_tendsto hE hB hV
    hs'.1 ht'.1 (fun u hu => (hs'.2.1 u hu).1) (fun u hu => (ht'.2.1 u hu).1) hw).div_const (Real.log 2)
  have heq : (∫ u in (1:ℝ)..2, (φ u*u^(-1-θ))*min (s*u^θ) (t*u^θ)) =
      min s t * ∫ u in (1:ℝ)..2, φ u/u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    dsimp only
    rw [← min_mul_of_nonneg s t (Real.rpow_nonneg hu0.le θ)]
    have hp : u^(-1-θ)*u^θ = 1/u := by
      rw [← Real.rpow_add hu0, show (-1-θ)+θ=(-1:ℝ) by ring, Real.rpow_neg_one]
      simp only [one_div]
    calc
      _ = min s t*φ u*(u^(-1-θ)*u^θ) := by ring
      _ = _ := by rw [hp]; ring
  rw [heq] at hm
  have hm' : Tendsto (fun X => weightedMacroCovariance E (fun u => s*u^θ) (fun u => t*u^θ)
      (fun u => φ u*u^(-1-θ)) θ X / Real.log 2) atTop
      (𝓝 (kappa θ*min s t*(∫ u in (1:ℝ)..2, φ u/u)/Real.log 2)) := by
    convert hm using 1 <;> ring
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  let K := |W| +1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbφ : ∀ u ∈ Icc (1:ℝ) 2, |φ u| ≤ K := by
    intro u hu
    have hh := hW u hu
    rw [Real.norm_eq_abs] at hh
    dsimp [K]
    linarith [le_abs_self W]
  have hz : Tendsto (fun X : ℝ => 3520*K/Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hm') (ε/2) (by positivity),
    hz.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity)),
    explicit_second_moment_bound hE hB hV, eventually_ge_atTop (4:ℝ)] with X hmX hzX hbX hX
  have hh := probability_weight_error hE hB hX hφ hK hbφ hbX hs ht
  rw [Real.dist_eq] at hmX ⊢
  exact (abs_sub_le _ _ _).trans_lt (by linarith)

private lemma covariance_difference_bound {E φ : ℝ → ℝ} {θ X C D K r : ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ : 0 ≤ θ) (hX : 1 < X)
    (hφ : ContinuousOn φ (Icc (1:ℝ) 2)) (hK : 0 ≤ K) (hr : 0 < r)
    (hbφ : ∀ u ∈ Icc (1:ℝ) 2, |φ u| ≤ K)
    (hb : ∀ s ∈ Icc (0:ℝ) 1, (∫ x, dyadicB E θ s x^2 ∂dyadicProbabilityMeasure X) ≤ C)
    {s t u v : ℝ} (_hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Icc (0:ℝ) 1) (_hv : v ∈ Icc (0:ℝ) 1)
    (hsu : (∫ x, (dyadicB E θ s x-dyadicB E θ u x)^2 ∂dyadicProbabilityMeasure X) ≤ D)
    (htv : (∫ x, (dyadicB E θ t x-dyadicB E θ v x)^2 ∂dyadicProbabilityMeasure X) ≤ D) :
    |weightedDyadicCovariance E φ θ θ X s t-weightedDyadicCovariance E φ θ θ X u v| ≤
      K*(2*D/r+2*r*C) := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  let μ := dyadicProbabilityMeasure X
  let B := dyadicB E θ
  have hAE : ∀ᵐ x ∂μ, x ∈ Icc X (2*X) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => ⟨h.1.le, h.2⟩)
  have hU : MapsTo (dyadicU X) (Icc X (2*X)) (Icc (1:ℝ) 2) := by
    intro x hx
    exact ⟨(le_div_iff₀ hX0).2 (by simpa [dyadicU] using hx.1), (div_le_iff₀ hX0).2 hx.2⟩
  have hc : ContinuousOn (fun x => φ (dyadicU X x)) (Icc X (2*X)) :=
    hφ.comp (continuous_id.div_const X).continuousOn hU
  have hm (a : ℝ) : MemLp (B a) 2 μ := by
    apply (memLp_two_iff_integrable_sq (f := B a) (μ := μ)
      (show AEStronglyMeasurable (B a) μ from
        ((dyadicB_measurable hE θ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).2
    simpa only [B, μ, one_mul, pow_two] using
      weighted_product_integrable (ψ := fun _ => 1) (s := a) (t := a) hE hθ hX continuousOn_const
  have hds := ((hm s).sub (hm u)).integrable_sq
  have hdt := ((hm t).sub (hm v)).integrable_sq
  have hbs := (hm t).integrable_sq
  have hbu := (hm u).integrable_sq
  rw [weightedDyadicCovariance, weightedDyadicCovariance, ← integral_sub
    (weighted_product_integrable (s := s) (t := t) hE hθ hX hc)
    (weighted_product_integrable (s := u) (t := v) hE hθ hX hc)]
  have hh := norm_integral_le_of_norm_le
    ((((hds.add hdt).div_const r).add ((hbs.add hbu).const_mul r)).const_mul K) (by
      filter_upwards [hAE] with x hx
      change ‖φ (dyadicU X x)*B s x*B t x-φ (dyadicU X x)*B u x*B v x‖ ≤ _
      have he : φ (dyadicU X x)*B s x*B t x-φ (dyadicU X x)*B u x*B v x =
          φ (dyadicU X x)*((B s x-B u x)*B t x+B u x*(B t x-B v x)) := by ring
      rw [Real.norm_eq_abs, he, abs_mul]
      have h₁ := MacroscopicWeightedCovariance.young_abs hr (B s x-B u x) (B t x)
      have h₂ := MacroscopicWeightedCovariance.young_abs hr (B t x-B v x) (B u x)
      have hp : |(B s x-B u x)*B t x+B u x*(B t x-B v x)| ≤
          ((B s x-B u x)^2+(B t x-B v x)^2)/r+r*(B t x^2+B u x^2) := by
        have hh := (abs_add_le ((B s x-B u x)*B t x) (B u x*(B t x-B v x))).trans
          (add_le_add h₁ (by simpa only [mul_comm] using h₂))
        convert hh using 1 <;> ring
      exact mul_le_mul (hbφ _ (hU hx)) hp (abs_nonneg _) hK)
  simp only [Pi.add_apply, Pi.sub_apply] at hds hdt hh
  have hadd := integral_add' ((hds.add hdt).div_const r) ((hbs.add hbu).const_mul r)
  have hadd₁ := integral_add' hds hdt
  have hadd₂ := integral_add' hbs hbu
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hadd₁ hadd₂
  rw [Real.norm_eq_abs, integral_const_mul, hadd, integral_div, integral_const_mul,
    hadd₁, hadd₂] at hh
  apply hh.trans
  have hsums : (∫ x, (B s x-B u x)^2 ∂μ)+(∫ x, (B t x-B v x)^2 ∂μ) ≤ 2*D := by
    dsimp [B, μ]
    linarith
  have hsum : (∫ x, B t x^2 ∂μ)+(∫ x, B u x^2 ∂μ) ≤ 2*C := by
    have hh₁ := hb t ht
    have hh₂ := hb u hu
    dsimp [B, μ]
    linarith
  calc
    _ ≤ K*(2*D/r+r*(2*C)) := by gcongr
    _ = _ := by ring


/-- Weighted dyadic covariances converge uniformly over both time parameters. -/
theorem weighted_covariance_uniform {E φ : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hφ : ContinuousOn φ (Icc (1 : ℝ) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |weightedDyadicCovariance E φ θ θ X s t - kappa θ * min s t *
          (∫ u in (1 : ℝ)..2, φ u / u) / Real.log 2| < ε := by
  let T := Icc (0:ℝ) 1 × Icc (0:ℝ) 1
  let f := fun (X : ℝ) (st : T) => weightedDyadicCovariance E φ θ θ X st.1 st.2
  let g := fun st : T => kappa θ*min (st.1:ℝ) (st.2:ℝ)*
    (∫ u in (1:ℝ)..2, φ u/u)/Real.log 2
  have hg : Continuous g := by
    exact ((continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inf
      (continuous_subtype_val.comp continuous_snd))).mul continuous_const).div_const _
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  let K := |W| +1
  let C := 1760/Real.log 2
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbφ : ∀ u ∈ Icc (1:ℝ) 2, |φ u| ≤ K := by
    intro u hu
    have hh := hW u hu
    rw [Real.norm_eq_abs] at hh
    dsimp [K]
    linarith [le_abs_self W]
  intro ε hε
  let r := ε/(32*(K+1)*(C+1))
  let D := ε*r/(32*(K+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨δg, hδg, hmodg⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hg)
    (ε/4) (by positivity)
  let δ := min 1 (min δg (D*Real.log 2/240))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδg' : δ ≤ δg := (min_le_right _ _).trans (min_le_left _ _)
  have hδD : δ ≤ D*Real.log 2/240 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨S, hS, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set T)).totallyBounded δ hδ
  have hfinite : ∀ᶠ X : ℝ in atTop, ∀ st ∈ S, |f X st-g st| < ε/4 := by
    apply hS.eventually_all.mpr
    intro st _hst
    exact (Metric.tendsto_nhds.mp (covariance_pointwise hE hB hV hφ st.1.property st.2.property))
      (ε/4) (by positivity)
  filter_upwards [hfinite, explicit_second_moment_bound hE hB hV,
    time_modulus hE hB hV δ hδ hδ1 (D/2) (by positivity),
    eventually_ge_atTop (4:ℝ)] with X hfinite hb hmod hX
  intro s hs t ht
  let st : T := (⟨s, hs⟩, ⟨t, ht⟩)
  obtain ⟨uv, huv, hnear⟩ : ∃ uv ∈ S, dist st uv < δ := by
    rcases Set.mem_iUnion.mp (hcover (Set.mem_univ st)) with ⟨uv, h⟩
    rcases Set.mem_iUnion.mp h with ⟨huv, h⟩
    exact ⟨uv, huv, h⟩
  have hsnear : |s-(uv.1:ℝ)| ≤ δ := by
    exact (show dist st.1 uv.1 ≤ dist st uv from le_max_left _ _).trans hnear.le
  have htnear : |t-(uv.2:ℝ)| ≤ δ := by
    exact (show dist st.2 uv.2 ≤ dist st uv from le_max_right _ _).trans hnear.le
  have hsmallD : 120*δ/Real.log 2+D/2 ≤ D := by
    have hh := (div_le_iff₀ hl2).2 (show 120*δ ≤ D/2*Real.log 2 by nlinarith)
    linarith
  have hdiff := covariance_difference_bound hE (hB.1.trans hB.2.1).le (show 1<X by linarith)
    hφ hK.le hr hbφ (by simpa only [sq_abs] using hb)
    hs ht uv.1.property uv.2.property
    ((hmod s hs uv.1 uv.1.property hsnear).trans hsmallD)
    ((hmod t ht uv.2 uv.2.property htnear).trans hsmallD)
  have hsmall : K*(2*D/r+2*r*C) < ε/2 := by
    have h₁ : K*(2*D/r) < ε/16 := by
      have he : (K+1)*(2*D/r)=ε/16 := by dsimp [D]; field_simp; ring
      have hh : K*(2*D/r)<(K+1)*(2*D/r) := by gcongr; linarith
      linarith
    have h₂ : K*(2*r*C) < ε/16 := by
      have he : (K+1)*(2*r*(C+1))=ε/16 := by dsimp [r]; field_simp; ring
      have hh : K*(2*r*C)<(K+1)*(2*r*(C+1)) := by gcongr <;> linarith
      linarith
    nlinarith
  have hlim := hmodg (show dist st uv < δg from hnear.trans_le hδg')
  have hpoint := hfinite uv huv
  change |f X st-g st| < ε
  rw [Real.dist_eq] at hlim
  have hh := abs_sub_le (f X st) (f X uv) (g st)
  have hh' := abs_sub_le (f X uv) (g uv) (g st)
  have hlim' : |g uv-g st| < ε/4 := by simpa only [abs_sub_comm] using hlim
  exact hh.trans_lt (by change |f X st-f X uv| ≤ _ at hdiff; linarith)

/-- The variance band supplies the second mixed-moment interface with its dyadic power moment. -/
theorem second_moment_interface {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    MomentInterface E θ 2
      (fun s => kappa θ * dyadicMacroMoment (kappa θ) * min (s 0) (s 1)) := by
  refine ⟨⟨1760/Real.log 2, by positivity, explicit_second_moment_bound hE hB hV⟩, ?_, ?_⟩
  · exact measurable_const.mul ((measurable_pi_apply 0).min (measurable_pi_apply 1))
  · intro s hs
    have hφ : ContinuousOn (fun u : ℝ => u^kappa θ) (Icc (1:ℝ) 2) :=
      continuousOn_id.rpow_const (fun u hu => Or.inl (by change u ≠ 0; linarith [hu.1]))
    have hh := covariance_pointwise hE hB hV hφ (hs 0) (hs 1)
    have hmoment : dyadicMacroMoment (kappa θ) =
        (∫ u in (1:ℝ)..2, u^kappa θ/u)/Real.log 2 := by
      simpa only [dyadicMacroMoment, mul_one] using dyadicProbabilityMeasure_integral
        (by norm_num : (0:ℝ)<1) (fun u => u^kappa θ)
    rw [hmoment]
    have heq : (fun X => dyadicMixedMoment E θ X 2 s) =
        (fun X => weightedDyadicCovariance E (fun u => u^kappa θ) θ θ X (s 0) (s 1)) := by
      funext X
      dsimp [dyadicMixedMoment, weightedDyadicCovariance]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [Fin.prod_univ_two]
        have hex : (2:ℝ)*dyadicR θ=kappa θ := by dsimp [dyadicR]; ring
        norm_num only [Nat.cast_ofNat]
        rw [hex]
        ring)
    rw [heq]
    convert hh using 1 <;> ring

end
end D5.S3.Arith.Robin.ForwardKernel.SecondOrderInterface
