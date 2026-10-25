/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Sharp sixth-moment threshold for simultaneous actual Gamma-domain escape. -/

import D5.S3.Weil.ZetaExplicit.VerticalLine
import D5.S3.Weil.ZetaGamma.GammaFacts
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiLacunaryProfile
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.GammaStirlingVert

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

def sourceOfProfile (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  if Real.pi ≤ x then ((x ^ (-9 / 4 : ℝ) : ℝ) : ℂ) * u (Real.log (x / Real.pi))
  else 0

def physicalTerm (F : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (((k + 1 : ℕ) : ℂ) ^ (4 : ℕ)) * F ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x)

def fullTheta (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℕ, physicalTerm F k x

def actualGammaProfile (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  if 0 ≤ t then
    (((Real.pi * Real.exp t) ^ (9 / 4 : ℝ) : ℝ) : ℂ) *
      fullTheta F (Real.pi * Real.exp t)
  else 0

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample


namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol

private def gammaRatio (ξ : ℝ) : ℝ :=
  (ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)

private def gammaDensity (ξ : ℝ) : ℝ :=
  (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) +
    Complex.I * (ξ : ℂ))).re - Real.log Real.pi

def gammaWeight (ξ : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * (gammaRatio ξ * gammaDensity ξ) +
    1 + 4 * Real.sqrt Real.pi

def domainConstant : ℝ :=
  2 * Real.sqrt Real.pi + 4 * (|Real.log Real.pi| + 5)

-- The literal reference Gamma weight is strictly larger than one, and
-- it dominates the positive logarithmic frequency weight up to a finite constant.
theorem actualGammaWeight_bounds (ξ : ℝ) :
    1 < gammaWeight ξ ∧
      max (Real.log |ξ|) 0 ≤ domainConstant * gammaWeight ξ := by
  let s : ℝ := Real.sqrt Real.pi
  let a : ℝ := 2 / s
  let B : ℝ := |Real.log Real.pi| + 5
  have hs : 0 < s := Real.sqrt_pos.2 Real.pi_pos
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < ξ ^ 2 + 25 / 16 := by positivity
  have hR0 : 0 ≤ gammaRatio ξ := by dsimp [gammaRatio]; positivity
  have hR1 : gammaRatio ξ ≤ 1 := by
    dsimp [gammaRatio]
    exact (div_le_one hden).2 (by linarith)
  have hdMu : gammaDensity ξ = 2 * Real.pi * Zeta23.mu (2 * ξ) := by
    have harg : (1 / 4 : ℂ) + Complex.I * ((2 * ξ : ℝ) : ℂ) / 2 =
        ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * (ξ : ℂ)) := by
      push_cast
      ring
    dsimp [gammaDensity, Zeta23.mu]
    rw [harg]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hd : -(2 * Real.pi) < gammaDensity ξ := by
    have hmu : (-1 : ℝ) < Zeta23.mu (2 * ξ) :=
      Zeta23.MuFields.neg_one_lt_mu_zero.trans_le
        (Zeta23.MuFields.mu_zero_le (2 * ξ))
    have hmul := mul_lt_mul_of_pos_left hmu
      (show 0 < 2 * Real.pi by positivity)
    rw [hdMu]
    simpa using hmul
  have hRd : -(2 * Real.pi) < gammaRatio ξ * gammaDensity ξ := by
    by_cases hd0 : 0 ≤ gammaDensity ξ
    · exact lt_of_lt_of_le (by linarith [Real.pi_pos]) (mul_nonneg hR0 hd0)
    · have hd0' : gammaDensity ξ ≤ 0 := le_of_not_ge hd0
      have hmul := mul_le_mul_of_nonpos_right hR1 hd0'
      exact hd.trans_le (by simpa using hmul)
  have hscale : a * (2 * Real.pi) = 4 * s := by
    dsimp [a, s]
    field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']
    <;> nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hp : 1 < gammaWeight ξ := by
    have hmul := mul_lt_mul_of_pos_left hRd ha
    change 1 < a * (gammaRatio ξ * gammaDensity ξ) + 1 + 4 * s
    nlinarith [hmul, hscale]
  refine ⟨hp, ?_⟩
  by_cases hsmall : |ξ| ≤ 1
  · have hlog : Real.log |ξ| ≤ 0 := Real.log_nonpos (abs_nonneg ξ) hsmall
    rw [max_eq_right hlog]
    exact mul_nonneg (by dsimp [domainConstant]; positivity) (by linarith [hp])
  · have hr : 1 < |ξ| := lt_of_not_ge hsmall
    have hsq : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hsq0 : 0 < ξ ^ 2 := by linarith
    have hRquarter : (1 / 4 : ℝ) ≤ gammaRatio ξ := by
      dsimp [gammaRatio]
      apply (le_div_iff₀ hden).2
      nlinarith [hsq]
    have hst := Zeta23.StirlingVert.re_digamma_stirling'
      (a := 1 / 4) (t := ξ) (by norm_num) (by norm_num) (by linarith [hr])
    have herr : 5 / ξ ^ 2 ≤ 5 :=
      (div_le_iff₀ hsq0).2 (by nlinarith [hsq])
    have hdlo : Real.log |ξ| - B ≤ gammaDensity ξ := by
      have hstlo := (abs_le.mp hst).1
      dsimp [gammaDensity, B]
      linarith [hstlo, herr, le_abs_self (Real.log Real.pi)]
    have hlog0 : 0 ≤ Real.log |ξ| := Real.log_nonneg hr.le
    have hRL := mul_le_mul_of_nonneg_right hRquarter hlog0
    have hRB := mul_le_mul_of_nonneg_right hR1 hB
    have hRD := mul_le_mul_of_nonneg_left hdlo hR0
    have hlow : Real.log |ξ| / 4 - B ≤ gammaRatio ξ * gammaDensity ξ := by
      nlinarith [hRL, hRB, hRD]
    have hpmain : a * (Real.log |ξ| / 4 - B) ≤ gammaWeight ξ := by
      have hmul := mul_le_mul_of_nonneg_left hlow ha.le
      change a * (Real.log |ξ| / 4 - B) ≤
        a * (gammaRatio ξ * gammaDensity ξ) + 1 + 4 * s
      linarith [hmul, hs]
    have hdiv : Real.log |ξ| ≤
        (4 * (gammaWeight ξ + a * B)) / a := by
      apply (le_div_iff₀ ha).2
      nlinarith [hpmain]
    have hfour : 4 / a = 2 * s := by
      dsimp [a]
      field_simp [hs.ne']
      <;> ring
    have hL : Real.log |ξ| ≤ 2 * s * gammaWeight ξ + 4 * B := by
      calc
        Real.log |ξ| ≤ (4 * (gammaWeight ξ + a * B)) / a := hdiv
        _ = (4 / a) * gammaWeight ξ + 4 * B := by
          field_simp [ha.ne']
          <;> ring
        _ = 2 * s * gammaWeight ξ + 4 * B := by rw [hfour]
    have hBscale : 4 * B ≤ 4 * B * gammaWeight ξ :=
      le_mul_of_one_le_right (by positivity) (by linarith [hp])
    rw [max_eq_left hlog0]
    change Real.log |ξ| ≤ (2 * s + 4 * B) * gammaWeight ξ
    nlinarith [hL, hBscale]

-- Every constant shift admitted by the literal lower bound remains large
-- enough to dominate log-plus. The constant may depend on that shift.
private theorem actualGammaWeight_shifted_log_bound (c : ℝ)
    (hc : ∀ ξ : ℝ, 1 ≤ gammaWeight ξ + c) (ξ : ℝ) :
    max (Real.log |ξ|) 0 ≤
      (domainConstant * (1 + |c|)) * (gammaWeight ξ + c) := by
  have hC : 0 ≤ domainConstant := by
    unfold domainConstant
    positivity
  have hscale : |c| ≤ |c| * (gammaWeight ξ + c) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hc ξ) (abs_nonneg c)
  have hp : gammaWeight ξ ≤ (1 + |c|) * (gammaWeight ξ + c) := by
    calc
      gammaWeight ξ ≤ (gammaWeight ξ + c) + |c| := by
        linarith [neg_le_abs c]
      _ ≤ (gammaWeight ξ + c) + |c| * (gammaWeight ξ + c) :=
        by linarith [hscale]
      _ = (1 + |c|) * (gammaWeight ξ + c) := by ring
  calc
    max (Real.log |ξ|) 0 ≤ domainConstant * gammaWeight ξ :=
      (actualGammaWeight_bounds ξ).2
    _ ≤ domainConstant * ((1 + |c|) * (gammaWeight ξ + c)) :=
      mul_le_mul_of_nonneg_left hp hC
    _ = (domainConstant * (1 + |c|)) * (gammaWeight ξ + c) := by ring

theorem finiteGammaWeight_continuous : Continuous gammaWeight := by
  have hd : gammaDensity = fun ξ : ℝ => 2 * Real.pi * Zeta23.mu (2 * ξ) := by
    funext ξ
    have harg : (1 / 4 : ℂ) + Complex.I * ((2 * ξ : ℝ) : ℂ) / 2 =
        ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * (ξ : ℂ)) := by
      push_cast
      ring
    dsimp [gammaDensity, Zeta23.mu]
    rw [harg]
    field_simp [Real.pi_ne_zero] <;> ring
  have hc : Continuous gammaDensity := by
    rw [hd]
    exact continuous_const.mul
      (Zeta23.mu_smooth.continuous.comp (continuous_const.mul continuous_id))
  have hr : Continuous gammaRatio := by
    unfold gammaRatio
    exact ((continuous_id.pow 2).add continuous_const).div
      ((continuous_id.pow 2).add continuous_const) (fun ξ => by positivity)
  unfold gammaWeight
  exact ((continuous_const.mul (hr.mul hc)).add continuous_const).add continuous_const

-- Quadratic growth is enough because the finite tent Fourier square has
-- fourth-order decay. Reuse the library's actual digamma strip bound.
theorem finiteGammaWeight_quadratic_upper :
    ∃ G : ℝ, 0 < G ∧ ∀ ξ : ℝ, gammaWeight ξ ≤ G * (1 + ξ ^ 2) := by
  obtain ⟨A, hA, hpsi⟩ := Zeta23.WeilEF.digamma_growth_strip
  let s : ℝ := Real.sqrt Real.pi
  let D : ℝ := 2 * A + |Real.log Real.pi|
  let G : ℝ := (2 / s) * D + 1 + 4 * s
  have hs : 0 < s := Real.sqrt_pos.mpr Real.pi_pos
  have hD : 0 < D := by dsimp [D]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G, hG, ?_⟩
  intro ξ
  let w : ℝ := 1 + ξ ^ 2
  have hw : 1 ≤ w := by dsimp [w]; nlinarith [sq_nonneg ξ]
  have hlog : Real.log (2 + |ξ|) ≤ 2 * w := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |ξ|)
    have hx : |ξ| ≤ 1 + ξ ^ 2 := by
      nlinarith [sq_nonneg (|ξ| - 1 / 2), sq_abs ξ]
    dsimp [w]
    nlinarith [hl, hx, sq_nonneg ξ]
  have hp : ‖Complex.digamma ((1 / 4 : ℂ) + Complex.I * (ξ : ℂ))‖ ≤
      A * Real.log (2 + |ξ|) := by
    simpa using hpsi ((1 / 4 : ℂ) + Complex.I * (ξ : ℂ))
      (by norm_num) (by norm_num)
  have hd : gammaDensity ξ ≤ D * w := by
    have hre := Complex.re_le_norm
      (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (ξ : ℂ)))
    have ha := mul_le_mul_of_nonneg_left hlog hA.le
    have hb := mul_le_mul_of_nonneg_left hw (abs_nonneg (Real.log Real.pi))
    have hquarter : (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) := by norm_num
    dsimp [gammaDensity, D]
    rw [hquarter]
    nlinarith [hp, hre, ha, hb, neg_le_abs (Real.log Real.pi)]
  have hr0 : 0 ≤ gammaRatio ξ := by unfold gammaRatio; positivity
  have hr1 : gammaRatio ξ ≤ 1 := by
    unfold gammaRatio
    exact (div_le_one (by positivity : 0 < ξ ^ 2 + 25 / 16)).mpr (by linarith)
  have hrd : gammaRatio ξ * gammaDensity ξ ≤ D * w := by
    calc
      gammaRatio ξ * gammaDensity ξ ≤ gammaRatio ξ * (D * w) :=
        mul_le_mul_of_nonneg_left hd hr0
      _ ≤ D * w := mul_le_of_le_one_left
        (mul_nonneg hD.le (by linarith [hw])) hr1
  have hmul := mul_le_mul_of_nonneg_left hrd
    (show 0 ≤ 2 / s by positivity)
  have hshift := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ 1 + 4 * s by positivity)
  change (2 / s) * (gammaRatio ξ * gammaDensity ξ) + 1 + 4 * s ≤ G * w
  dsimp [G]
  nlinarith [hmul, hshift]

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol


/- The literal symbol comparison and explicit profile feed the compressed
physical witness, with full theta and the actual positive-log divergence. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped ENNReal

/-- The original physical Hilbert space and sixth moment, without a
coefficient-space or truncated-theta reinterpretation. -/
def originalPhysicalH6 (F : ℝ → ℂ) : Prop :=
  MemLp F 2 (volume.restrict (Ioi Real.pi)) ∧
    Integrable (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi))

/-- Literal actual Gamma form with relative constant shift c, on a source
whose actual profile is L1 as proved for the explicit counterexample.
Admissibility means gammaWeight+c >= 1 everywhere in the theorem below.
Integrable is genuine finite energy, not a totalized integral criterion. -/
def originalGammaFormDomain (c : ℝ) (F : ℝ → ℂ) : Prop :=
  Integrable (fun ξ : ℝ =>
    (Symbol.gammaWeight ξ + c) *
      ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) volume

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample


/- Compression preserves the positive-log Fourier divergence while the
logarithmic support enforces any original sixth-moment ratio cap K>1.
The witness is the same source for all admissible Gamma shifts. -/
namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology

def compressedProfile (κ t : ℝ) : ℂ := counterProfile (t / κ)
def compressedFeature (κ : ℝ) : ℝ → ℂ := sourceOfProfile (compressedProfile κ)

private theorem compressed_zero (κ : ℝ) : compressedProfile κ 0 = 0 := by
  have hz : counterProfile 0 = 0 := profile_zero_off (by norm_num)
  simpa [compressedProfile] using hz

private theorem compressed_continuous (κ : ℝ) : Continuous (compressedProfile κ) :=
  profile_continuous.comp (continuous_id.div_const κ)

private theorem compressed_zero_off {κ : ℝ} (hκ : 0 < κ) {t : ℝ}
    (ht : t ∉ Icc (κ / 4) (3 * κ / 4)) : compressedProfile κ t = 0 := by
  apply profile_zero_off
  intro h
  apply ht
  have ha := (le_div_iff₀ hκ).mp h.1
  have hb := (div_le_iff₀ hκ).mp h.2
  constructor <;> nlinarith [ha, hb]

private theorem compressed_compact {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (compressedProfile κ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
  intro t ht
  by_contra h
  exact ht (compressed_zero_off hκ h)

private theorem compressed_center {κ : ℝ} (hκ : 0 < κ) :
    compressedProfile κ (κ / 2) = 1 := by
  have he : κ / 2 / κ = (1 / 2 : ℝ) := by field_simp [hκ.ne']
  simpa [compressedProfile, he] using profile_center

private theorem compressed_L1 {κ : ℝ} (hκ : 0 < κ) :
    Integrable (compressedProfile κ) volume :=
  (compressed_continuous κ).integrable_of_hasCompactSupport (compressed_compact hκ)

private theorem compressed_profile_memLp {κ : ℝ} (hκ : 0 < κ) :
    MemLp (compressedProfile κ) 2 volume :=
  (compressed_continuous κ).memLp_of_hasCompactSupport (compressed_compact hκ)

private theorem compressed_fourier {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    unitarySourceFourier (compressedProfile κ) ξ =
      (κ : ℂ) * unitarySourceFourier counterProfile (κ * ξ) := by
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hp (t : ℝ) : sourcePhase ξ t = sourcePhase (κ * ξ) (t / κ) := by
    unfold sourcePhase
    congr 1
    push_cast
    field_simp [hκc] <;> ring
  have hi : (∫ t : ℝ, sourcePhase ξ t * compressedProfile κ t) =
      κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * counterProfile t := by
    calc
      _ = ∫ t : ℝ, sourcePhase (κ * ξ) (t / κ) * counterProfile (t / κ) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [compressedProfile, hp]
      _ = κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * counterProfile t := by
        simpa only [abs_of_pos hκ] using
          Measure.integral_comp_div
            (fun t : ℝ => sourcePhase (κ * ξ) t * counterProfile t) κ
  rw [unitarySourceFourier_eq_integral, unitarySourceFourier_eq_integral, hi,
    Complex.real_smul]
  ring

private theorem compressed_fourier_norm_sq {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2 =
      κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2 := by
  rw [compressed_fourier hκ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hκ, mul_pow]

theorem compressed_logplus_comparison {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ξ : ℝ) :
    max (Real.log |κ * ξ|) 0 ≤ max (Real.log |ξ|) 0 := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  have ha : 0 < |κ * ξ| := abs_pos.mpr (mul_ne_zero hκ.ne' hξ)
  have hb : |κ * ξ| ≤ |ξ| := by
    rw [abs_mul, abs_of_pos hκ]
    exact mul_le_of_le_one_left (abs_nonneg ξ) hκ1
  exact max_le_max (Real.log_le_log ha hb) le_rfl

private theorem compressed_positive_log_top {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
      ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2)) = ∞ := by
  let g : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (max (Real.log |ξ|) 0 * ‖unitarySourceFourier counterProfile ξ‖ ^ 2)
  have he : MeasurableEmbedding (fun ξ : ℝ => κ * ξ) :=
    (Homeomorph.mulLeft₀ κ hκ.ne').isClosedEmbedding.measurableEmbedding
  have hc : (∫⁻ ξ : ℝ, g (κ * ξ)) =
      ENNReal.ofReal |κ⁻¹| * ∫⁻ ξ : ℝ, g ξ := by
    rw [← he.lintegral_map g, Real.map_volume_mul_left hκ.ne', lintegral_smul_measure, smul_eq_mul]
  have hn : ENNReal.ofReal |κ⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hκ.ne'))).ne'
  have hs : (∫⁻ ξ : ℝ, g (κ * ξ)) = ∞ := by
    rw [hc]
    have hg : (∫⁻ ξ : ℝ, g ξ) = ∞ := actual_counterProfile_positive_log_top
    rw [hg]
    exact ENNReal.mul_top hn
  have hκ2 : ENNReal.ofReal (κ ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hκ)).ne'
  apply top_unique
  calc
    ∞ = ENNReal.ofReal (κ ^ 2) * ∫⁻ ξ : ℝ, g (κ * ξ) := by simp [hs, hκ2]
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (κ ^ 2) * g (κ * ξ) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2) := by
      apply lintegral_mono
      intro ξ
      dsimp [g]
      rw [← ENNReal.ofReal_mul (sq_nonneg κ)]
      apply ENNReal.ofReal_le_ofReal
      rw [compressed_fourier_norm_sq hκ]
      calc
        κ ^ 2 * (max (Real.log |κ * ξ|) 0 *
            ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) =
            max (Real.log |κ * ξ|) 0 *
              (κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) := by ring
        _ ≤ max (Real.log |ξ|) 0 *
            (κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (compressed_logplus_comparison hκ hκ1 ξ)
            (by positivity)

private theorem compressedFeature_support {κ : ℝ} (hκ : 0 < κ) :
    Function.support (compressedFeature κ) ⊆
      Icc Real.pi (Real.pi * Real.exp (3 * κ / 4)) := by
  intro x hx
  have hπ : Real.pi ≤ x := by
    by_contra h
    exact hx (by simp [compressedFeature, sourceOfProfile, h])
  refine ⟨hπ, ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le Real.pi_pos hπ
  have hprof : compressedProfile κ (Real.log (x / Real.pi)) ≠ 0 := by
    intro hz
    exact hx (by simp [compressedFeature, sourceOfProfile, hπ, hz])
  have ht : Real.log (x / Real.pi) ∈ Icc (κ / 4) (3 * κ / 4) := by
    by_contra h
    exact hprof (compressed_zero_off hκ h)
  have he := Real.exp_le_exp.mpr ht.2
  rw [Real.exp_log (div_pos hxpos Real.pi_pos)] at he
  simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp he

private theorem compressedFeature_compact {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (compressedFeature κ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (compressedFeature_support hκ)

-- Clamp x at pi only for the continuity proof; the literal source definition
-- and all physical/full-theta identities remain unchanged.
theorem compressedFeature_continuous {κ : ℝ} (hκ : 0 < κ) :
    Continuous (compressedFeature κ) := by
  have he : compressedFeature κ = fun x : ℝ =>
      (((max Real.pi x) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) *
        compressedProfile κ (Real.log (max Real.pi x / Real.pi)) := by
    funext x
    by_cases hx : Real.pi ≤ x
    · simp [compressedFeature, sourceOfProfile, hx, max_eq_right hx]
    · simp [compressedFeature, sourceOfProfile, hx,
        max_eq_left (le_of_not_ge hx), Real.pi_ne_zero, compressed_zero]
  rw [he]
  have hm : Continuous (fun x : ℝ => max Real.pi x) := continuous_const.max continuous_id
  have hn (x : ℝ) : max Real.pi x ≠ 0 :=
    (lt_of_lt_of_le Real.pi_pos (le_max_left _ _)).ne'
  have hr := hm.rpow_const (p := (-9 / 4 : ℝ)) (fun x => Or.inl (hn x))
  have hl : Continuous (fun x : ℝ => Real.log (max Real.pi x / Real.pi)) :=
    (hm.div_const Real.pi).log (fun x => div_ne_zero (hn x) Real.pi_ne_zero)
  exact (Complex.continuous_ofReal.comp hr).mul ((compressed_continuous κ).comp hl)

private theorem compressedFeature_zero_le_pi {κ : ℝ} (hκ : 0 < κ)
    {x : ℝ} (hx : x ≤ Real.pi) : compressedFeature κ x = 0 := by
  by_cases he : x = Real.pi
  · subst x
    simp [compressedFeature, sourceOfProfile, Real.pi_ne_zero, compressed_zero]
  · have hn : ¬ Real.pi ≤ x := fun h => he (le_antisymm hx h)
    simp [compressedFeature, sourceOfProfile, hn]

private theorem compressedFeature_real (κ x : ℝ) : (compressedFeature κ x).im = 0 := by
  by_cases hx : Real.pi ≤ x <;>
    simp [compressedFeature, sourceOfProfile, hx, compressedProfile,
      counterProfile, Complex.mul_im]

private theorem compressedFeature_center_ne {κ : ℝ} (hκ : 0 < κ) :
    compressedFeature κ (Real.pi * Real.exp (κ / 2)) ≠ 0 := by
  have hx : Real.pi ≤ Real.pi * Real.exp (κ / 2) := by
    have he := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ κ / 2)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hl : Real.log ((Real.pi * Real.exp (κ / 2)) / Real.pi) = κ / 2 := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  have hn : (Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (mul_pos Real.pi_pos (Real.exp_pos _)) _).ne'
  have hnc : (((Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast hn
  simpa [compressedFeature, sourceOfProfile, hx, hl, compressed_center hκ] using hnc

private theorem compressed_density_compact {κ : ℝ} (hκ : 0 < κ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x : ℝ => w x * ‖compressedFeature κ x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.pi) (b := Real.pi * Real.exp (3 * κ / 4)))
  intro x hx
  by_contra h
  have hz : compressedFeature κ x = 0 := by
    by_contra hn
    exact h (compressedFeature_support hκ hn)
  exact hx (by simp [hz])

private theorem compressed_mass_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => ‖compressedFeature κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => ‖compressedFeature κ x‖ ^ (2 : ℕ)) :=
    (compressedFeature_continuous hκ).norm.pow 2
  have hs := compressed_density_compact hκ (fun _ : ℝ => 1)
  exact hc.integrable_of_hasCompactSupport (by simpa only [one_mul] using hs)

private theorem compressed_sixth_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x‖ ^ 2) :=
    ((continuous_id.div_const Real.pi).pow 6).mul
      ((compressedFeature_continuous hκ).norm.pow 2)
  exact hc.integrable_of_hasCompactSupport
    (compressed_density_compact hκ (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ)))

theorem compressed_original_h6 {κ : ℝ} (hκ : 0 < κ) :
    originalPhysicalH6 (compressedFeature κ) := by
  refine ⟨?_, (compressed_sixth_integrable hκ).integrableOn⟩
  exact ((compressedFeature_continuous hκ).memLp_of_hasCompactSupport
    (compressedFeature_compact hκ)).mono_measure Measure.restrict_le_self

private theorem compressed_mass_Ioi_eq {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2) =
      ∫ x : ℝ, ‖compressedFeature κ x‖ ^ 2 := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi Real.pi
  · simp [hx]
  · have hz := compressedFeature_zero_le_pi hκ (le_of_not_gt hx)
    simp [hx, hz]

private theorem compressed_physical_mass_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < ∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2 := by
  rw [compressed_mass_Ioi_eq hκ]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((compressedFeature_continuous hκ).norm.pow 2) (compressed_mass_integrable hκ)
    (fun x => sq_nonneg _) (x := Real.pi * Real.exp (κ / 2))
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (compressedFeature_center_ne hκ))

private theorem compressed_moment_ratio_bound {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) * ‖compressedFeature κ x‖ ^ 2) ≤
      Real.exp (9 * κ / 2) *
        (∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2) := by
  rw [← integral_const_mul]
  apply integral_mono (compressed_sixth_integrable hκ).integrableOn
    ((compressed_mass_integrable hκ).const_mul _).integrableOn
  intro x
  by_cases hz : compressedFeature κ x = 0
  · simp [hz]
  · have hx := compressedFeature_support hκ hz
    have ha : 0 ≤ x / Real.pi :=
      div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ Real.exp (3 * κ / 4) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      simpa only [mul_comm] using hx.2
    have hc := pow_le_pow_left₀ ha hb 6
    have he : Real.exp (3 * κ / 4) ^ (6 : ℕ) = Real.exp (9 * κ / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      <;> ring
    rw [he] at hc
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem compressedFeature_zero_high {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x : ℝ} (hx : 4 * Real.pi ≤ x) : compressedFeature κ x = 0 := by
  by_contra hn
  have hs := (compressedFeature_support hκ hn).2
  have hl : 3 * κ / 4 < Real.log 4 := by
    linarith [three_quarters_lt_log_four]
  have he : Real.exp (3 * κ / 4) < 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp hl
  nlinarith [mul_lt_mul_of_pos_left he Real.pi_pos]

private theorem compressed_terms_hasSum {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x : ℝ} (hx : Real.pi ≤ x) :
    HasSum (fun k : ℕ => physicalTerm (compressedFeature κ) k x)
      (compressedFeature κ x) := by
  have ht (k : ℕ) (hk : k ≠ 0) : physicalTerm (compressedFeature κ) k x = 0 := by
    have hn : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
    have hn2 : (4 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by nlinarith
    have hy : 4 * Real.pi ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x := by
      nlinarith [mul_le_mul_of_nonneg_right hn2 (le_trans Real.pi_pos.le hx)]
    simp only [physicalTerm, compressedFeature_zero_high hκ hκ1 hy, mul_zero]
  have hf : (fun k : ℕ => physicalTerm (compressedFeature κ) k x) =
      fun k : ℕ => if k = 0 then compressedFeature κ x else 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [physicalTerm]
    · simp [hk, ht k hk]
  rw [hf]
  exact hasSum_ite_eq 0 (compressedFeature κ x)

private theorem compressed_actualProfile_eq {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    actualGammaProfile (compressedFeature κ) = compressedProfile κ := by
  funext t
  by_cases ht : 0 ≤ t
  · have hxpos : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have hx : Real.pi ≤ Real.pi * Real.exp t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr ht) Real.pi_pos.le
    have hf : fullTheta (compressedFeature κ) (Real.pi * Real.exp t) =
        compressedFeature κ (Real.pi * Real.exp t) :=
      (compressed_terms_hasSum hκ hκ1 hx).tsum_eq
    have hl : Real.log ((Real.pi * Real.exp t) / Real.pi) = t := by
      rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
    have hr : (Real.pi * Real.exp t) ^ (9 / 4 : ℝ) *
        (Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hrc : (((Real.pi * Real.exp t) ^ (9 / 4 : ℝ) : ℝ) : ℂ) *
        (((Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    rw [actualGammaProfile, if_pos ht, hf, compressedFeature, sourceOfProfile,
      if_pos hx, hl, ← mul_assoc, hrc, one_mul]
  · have hz : compressedProfile κ t = 0 :=
      compressed_zero_off hκ (fun h => by linarith [h.1])
    simp [actualGammaProfile, ht, hz]

private theorem compressed_profile_exponential_moments {κ : ℝ} (hκ : 0 < κ) (q : ℝ) :
    Integrable (fun t : ℝ => Real.exp (q * t) * ‖compressedProfile κ t‖ ^ 2) volume := by
  have hc : Continuous (fun t : ℝ => Real.exp (q * t) * ‖compressedProfile κ t‖ ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((compressed_continuous κ).norm.pow 2)
  have hs : HasCompactSupport (fun t : ℝ => Real.exp (q * t) *
      ‖compressedProfile κ t‖ ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [compressed_zero_off hκ h])
  exact hc.integrable_of_hasCompactSupport hs

private theorem compressed_profile_mass_moment {κ : ℝ} (hκ : 0 < κ) :
    (0 < ∫ t : ℝ, ‖compressedProfile κ t‖ ^ 2) ∧
    Integrable (fun t : ℝ => t * ‖compressedProfile κ t‖ ^ 2)
      (volume.restrict (Ioi 0)) ∧
    (0 < ∫ t : ℝ in Ioi 0, t * ‖compressedProfile κ t‖ ^ 2) := by
  let q : ℝ → ℝ := fun t => ‖compressedProfile κ t‖ ^ 2
  have hcq : Continuous q := (compressed_continuous κ).norm.pow 2
  have hsq : HasCompactSupport q := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [q, compressed_zero_off hκ h])
  have hiq : Integrable q volume := hcq.integrable_of_hasCompactSupport hsq
  have hp : 0 < ∫ t : ℝ, q t :=
    hcq.integral_pos_of_hasCompactSupport_nonneg_nonzero hsq (fun t => sq_nonneg _)
      (x := κ / 2) (by simp [q, compressed_center hκ])
  have hcs : Continuous (fun t : ℝ => t * q t) := continuous_id.mul hcq
  have hss : HasCompactSupport (fun t : ℝ => t * q t) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [q, compressed_zero_off hκ h])
  have his : Integrable (fun t : ℝ => t * q t) volume :=
    hcs.integrable_of_hasCompactSupport hss
  have hb (t : ℝ) : (κ / 4) * q t ≤ t * q t := by
    by_cases ht : t ∈ Icc (κ / 4) (3 * κ / 4)
    · exact mul_le_mul_of_nonneg_right ht.1 (sq_nonneg _)
    · simp [q, compressed_zero_off hκ ht]
  have hl : (κ / 4) * (∫ t : ℝ, q t) ≤ ∫ t : ℝ, t * q t := by
    simpa only [integral_const_mul] using integral_mono (hiq.const_mul _) his hb
  have he : (∫ t : ℝ in Ioi 0, t * q t) = ∫ t : ℝ, t * q t := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp [ht]
    · have hz : compressedProfile κ t = 0 :=
        compressed_zero_off hκ (fun h => ht (show 0 < t by linarith [h.1, hκ]))
      simp [ht, q, hz]
  refine ⟨hp, his.integrableOn, ?_⟩
  change 0 < ∫ t : ℝ in Ioi 0, t * q t
  rw [he]
  exact lt_of_lt_of_le (mul_pos (by positivity) hp) hl

theorem compressed_not_form_domain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (c : ℝ) (hc : ∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) :
    ¬ originalGammaFormDomain c (compressedFeature κ) := by
  intro hGamma
  let q : ℝ → ℝ := fun ξ =>
    ‖unitarySourceFourier (actualGammaProfile (compressedFeature κ)) ξ‖ ^ 2
  have hq (ξ : ℝ) : 0 ≤ q ξ := sq_nonneg _
  have hFiniteGamma : Integrable
      (fun ξ : ℝ => (Symbol.gammaWeight ξ + c) * q ξ) volume := hGamma
  have hFiniteLog : HasFiniteIntegral (fun ξ : ℝ => max (Real.log |ξ|) 0 * q ξ) volume := by
    apply (hFiniteGamma.const_mul
      (Symbol.domainConstant * (1 + |c|))).hasFiniteIntegral.mono_nonneg
    · exact Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (hq ξ)
    · exact Eventually.of_forall fun ξ => by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right
            (Symbol.actualGammaWeight_shifted_log_bound c hc ξ) (hq ξ)
  have hlt : (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 * q ξ)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (hq ξ))).mp hFiniteLog
  have htop : (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 * q ξ)) = ∞ := by
    dsimp [q]
    rw [compressed_actualProfile_eq hκ hκ1]
    exact compressed_positive_log_top hκ hκ1
  rw [htop] at hlt
  exact (lt_irrefl (∞ : ℝ≥0∞)) hlt

private theorem quarter_compression_bound : Real.exp (9 / 8 : ℝ) < 4 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp
  rw [Real.log_four_eq]
  linarith [Real.log_two_gt_d9]

theorem exists_cap_compression (K : ℝ) (hK : 1 < K) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ Real.exp (9 * κ / 2) < K := by
  by_cases h4 : 4 ≤ K
  · refine ⟨1 / 4, by norm_num, le_rfl, ?_⟩
    simpa only [show 9 * (1 / 4 : ℝ) / 2 = 9 / 8 by norm_num] using
      quarter_compression_bound.trans_le h4
  · let κ : ℝ := min (1 / 4 : ℝ) (Real.log K / 9)
    have hL : 0 < Real.log K := Real.log_pos hK
    have hk : 0 < κ := lt_min (by norm_num) (by positivity)
    have hkc : κ ≤ 1 / 4 := min_le_left _ _
    have hkl : κ ≤ Real.log K / 9 := min_le_right _ _
    refine ⟨κ, hk, hkc, ?_⟩
    calc
      Real.exp (9 * κ / 2) < Real.exp (Real.log K) :=
        Real.exp_lt_exp.mpr (by nlinarith [hkl])
      _ = K := Real.exp_log (by linarith)

/-- The compressed actual physical source meets every prescribed original
sixth-moment cap K>1 and escapes every admissible constant Gamma shift.
For K>=4, κ=1/4 gives logarithmic support [1/16,3/16] and
M/H<=exp(9/8)<4. -/
private theorem fixed_cap_escape_construct (K : ℝ) (hK : 1 < K) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      Integrable (actualGammaProfile F) volume ∧
      MemLp (actualGammaProfile F) 2 volume ∧
      (∀ q : ℝ, Integrable
        (fun t : ℝ => Real.exp (q * t) * ‖actualGammaProfile F t‖ ^ 2) volume) ∧
      (0 < ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2) ∧
      Integrable (fun t : ℝ => t * ‖actualGammaProfile F t‖ ^ 2)
        (volume.restrict (Ioi 0)) ∧
      (0 < ∫ t : ℝ in Ioi 0, t * ‖actualGammaProfile F t‖ ^ 2) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2)) = ∞) ∧
      (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
        ¬ originalGammaFormDomain c F) := by
  obtain ⟨κ, hk, hkc, hkK⟩ := exists_cap_compression K hK
  have hk1 : κ ≤ 1 := by linarith
  have he := compressed_actualProfile_eq hk hk1
  have hm := compressed_profile_mass_moment hk
  refine ⟨compressedFeature κ, compressed_original_h6 hk,
    compressedFeature_real κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    compressed_physical_mass_pos hk, ?_, ?_, compressed_not_form_domain hk hk1⟩
  · intro x hx
    exact compressed_terms_hasSum hk hk1 hx
  · rw [he]
    exact compressed_L1 hk
  · rw [he]
    exact compressed_profile_memLp hk
  · intro q
    rw [he]
    exact compressed_profile_exponential_moments hk q
  · rw [he]
    exact hm.1
  · rw [he]
    exact hm.2.1
  · rw [he]
    exact hm.2.2
  · exact lt_of_le_of_lt (compressed_moment_ratio_bound hk)
      (mul_lt_mul_of_pos_right hkK (compressed_physical_mass_pos hk))
  · rw [he]
    exact compressed_positive_log_top hk hk1


/-- Sharp original sixth-moment threshold for simultaneous escape from every
admissible constant shift of the actual Gamma form domain. The same witness
works for all shifts, including negative relative shifts with weight >= 1.
It retains literal physical H>0, full theta, actual profile L1/L2 and divergent
extended log-plus integral. The conclusion concerns form-domain membership;
it makes no assertion about the sign of the complete Weil energy or RH. -/
theorem actual_h6_gamma_domain_escape_iff (K : ℝ) :
    (∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      Integrable (actualGammaProfile F) volume ∧
      MemLp (actualGammaProfile F) 2 volume ∧
      (∀ q : ℝ, Integrable
        (fun t : ℝ => Real.exp (q * t) * ‖actualGammaProfile F t‖ ^ 2) volume) ∧
      (0 < ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2) ∧
      Integrable (fun t : ℝ => t * ‖actualGammaProfile F t‖ ^ 2)
        (volume.restrict (Ioi 0)) ∧
      (0 < ∫ t : ℝ in Ioi 0, t * ‖actualGammaProfile F t‖ ^ 2) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2)) = ∞) ∧
      (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
        ¬ originalGammaFormDomain c F)) ↔ 1 < K := by
  constructor
  · rintro ⟨F, hH6, _, _, _, _, _, _, _, _, hH, hcap, _, _⟩
    have hmass : Integrable (fun x : ℝ => ‖F x‖ ^ (2 : ℕ))
        (volume.restrict (Ioi Real.pi)) :=
      hH6.1.integrable_norm_pow (p := 2) (by norm_num)
    have hHM : (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ≤
        ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2 := by
      apply integral_mono_ae hmass hH6.2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : Real.pi < x := hx
      have hr : (1 : ℝ) ≤ x / Real.pi := by
        apply (le_div_iff₀ Real.pi_pos).mpr
        simpa only [one_mul] using hx'.le
      have hp : (1 : ℝ) ≤ (x / Real.pi) ^ (6 : ℕ) := one_le_pow₀ hr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (sq_nonneg ‖F x‖)
    have hHK := hHM.trans_lt hcap
    nlinarith [hH]
  · intro hK
    exact fixed_cap_escape_construct K hK

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
