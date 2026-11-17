/- GID: D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Inverse-log-squared curvature of the actual second and fourth cutoffs. -/
import D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! Each layer index is fixed before taking limits. Every root and gain is the
actual library quantity. These estimates do not supply original record clocks,
paid-growth certificates, or the full Robin inequality. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open Real Filter Finset
open scoped Topology
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster

def d (j : ℕ) (X : ℝ) : ℝ :=
  (j : ℝ) * log (cutoff j (referencePrice X)) - log X
def η (j : ℕ) (X : ℝ) : ℝ :=
  log (gain j (cutoff j (referencePrice X)) * cutoff j (referencePrice X) ^ j)
def F (L a : ℝ) : ℝ := a + log (1 + a / L)

/-- Uniform elementary gain normalization. There is no fixed-index constant. -/
theorem normalized_gain_bounds {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 2 ≤ u) :
    1 - 1 / u ≤ gain j u * u ^ j ∧ gain j u * u ^ j ≤ 1 ∧
      -2 / u ≤ log (gain j u * u ^ j) ∧ log (gain j u * u ^ j) ≤ 0 := by
  have hu0 : 0 < u := by linarith
  have hs := powerSum_pos hu0 hj
  have hp := pow_pos hu0 j
  have hg := gain_pos hu0 hj
  have hlow : 1 / (powerSum j u + 1) ≤ gain j u := by
    have hh := one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / powerSum j u by positivity)
    have he : 1 - (1 + 1 / powerSum j u)⁻¹ = 1 / (powerSum j u + 1) := by
      field_simp [hs.ne', (by positivity : powerSum j u + 1 ≠ 0)]
      ring
    simpa only [gain, he] using hh
  have hgeom : (powerSum j u + 1) * (u - 1) = u ^ (j + 1) - 1 := by
    have hh := powerSum_geometric j u
    calc
      (powerSum j u + 1) * (u - 1) = (u - 1) * powerSum j u + (u - 1) := by ring
      _ = u * (u ^ j - 1) + (u - 1) := by rw [hh]
      _ = u ^ (j + 1) - 1 := by rw [pow_succ]; ring
  have hnorm : 1 - 1 / u ≤ u ^ j / (powerSum j u + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < powerSum j u + 1)).mpr
    have he : u * ((1 - 1 / u) * (powerSum j u + 1)) = u ^ j * u - 1 := by
      calc
        u * ((1 - 1 / u) * (powerSum j u + 1)) =
            (powerSum j u + 1) * (u - 1) := by
              field_simp [hu0.ne']
        _ = u ^ (j + 1) - 1 := hgeom
        _ = u ^ j * u - 1 := by rw [pow_succ]
    apply le_of_mul_le_mul_left ?_ hu0
    rw [he]
    linarith
  have hlo : 1 - 1 / u ≤ gain j u * u ^ j := hnorm.trans (by
    simpa only [one_mul, div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hlow hp.le)
  have hhi : gain j u * u ^ j ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (gain_le_inv_pow hu0 hj) hp.le
    simpa only [one_div_mul_cancel hp.ne'] using hh
  have hbase : 0 < 1 - 1 / u := by
    have hh : 1 / u ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hu
    linarith
  have hloglo := log_le_log hbase hlo
  have hbasic := one_sub_inv_le_log_of_pos hbase
  have haux : -2 / u ≤ 1 - (1 - 1 / u)⁻¹ := by
    have he : 1 - (1 - 1 / u)⁻¹ = -1 / (u - 1) := by
      field_simp [hu0.ne', (by linarith : u - 1 ≠ 0)] <;> ring
    rw [he]
    apply (div_le_div_iff₀ hu0 (by linarith : 0 < u - 1)).mpr
    linarith
  refine ⟨hlo, hhi, haux.trans (hbasic.trans hloglo), ?_⟩
  simpa only [log_one] using log_le_log (mul_pos hg hp) hhi

theorem actual_root_equation {j : ℕ} (hj : 2 ≤ j) :
    ∀ᶠ X : ℝ in atTop, 0 < d j X ∧ 2 < cutoff j (referencePrice X) ∧
      F (log X) (d j X) = log (j : ℝ) + η j X := by
  have hjr : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hd := (fixed_layer_root_offset_tendsto hj).eventually
    (eventually_gt_nhds (log_pos hjr))
  filter_upwards [eventually_gt_atTop (1 : ℝ), (root_atTop hj).eventually_gt_atTop 2, hd]
    with X hX hu hdX
  have hLambda : 0 < referencePrice X := by
    dsimp [referencePrice]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))
  have hr := (cutoff_spec hj hLambda).2.2.1 hu
  let u := cutoff j (referencePrice X)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlu : 0 < log u := log_pos (by dsimp [u]; linarith)
  have hL : 0 < log X := log_pos hX
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hgain : gain j u = log u / (X * log X) := by
    change gain j u / log u = 1 / (X * log X) at hr
    exact (div_eq_iff hlu.ne').mp hr |>.trans (by ring)
  have harg : 1 + d j X / log X = (j : ℝ) * log u / log X := by
    dsimp [d, u]
    field_simp [hL.ne']
    ring
  refine ⟨hdX, hu, ?_⟩
  dsimp only [F, η]
  rw [harg, log_div (mul_pos hj0 hlu).ne' hL.ne', log_mul hj0.ne' hlu.ne',
    log_mul (gain_pos hu0 (by omega : 1 ≤ j)).ne' (pow_pos hu0 j).ne',
    hgain, log_div hlu.ne' (mul_pos (by linarith : 0 < X) hL).ne',
    log_mul (by linarith : X ≠ 0) hL.ne', log_pow]
  dsimp [d, u]
  ring

theorem scaled_root_error {j : ℕ} (hj : 2 ≤ j) (n : ℕ) :
    Tendsto (fun X : ℝ => log X ^ n * η j X) atTop (𝓝 0) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsmall : Tendsto (fun X : ℝ => log X ^ n / cutoff j (referencePrice X))
      atTop (𝓝 0) := by
    have hlog := (isLittleO_log_rpow_rpow_atTop n
      (inv_pos.mpr hj0)).tendsto_div_nhds_zero
    simp only [rpow_natCast] at hlog
    have hh := hlog.div (root_ratio hj) (rpow_pos_of_pos hj0 _).ne'
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), (root_atTop hj).eventually_gt_atTop 0]
      with X hX hu
    dsimp only [Function.comp_def, Pi.div_apply]
    field_simp [hX.ne', hu.ne', (rpow_pos_of_pos hX ((j : ℝ)⁻¹)).ne']
  have hbound : ∀ᶠ X : ℝ in atTop,
      |log X ^ n * η j X| ≤ 2 * (log X ^ n / cutoff j (referencePrice X)) := by
    filter_upwards [(root_atTop hj).eventually_ge_atTop 2,
      eventually_ge_atTop (1 : ℝ)] with X hu hX
    obtain ⟨_, _, hlo, hhi⟩ := normalized_gain_bounds (by omega : 1 ≤ j) hu
    rw [abs_mul, abs_of_nonneg (pow_nonneg (log_nonneg hX) n)]
    have he : |η j X| ≤ 2 / cutoff j (referencePrice X) := by
      dsimp [η]
      rw [abs_of_nonpos hhi]
      have hlo' : -(2 / cutoff j (referencePrice X)) ≤
          log (gain j (cutoff j (referencePrice X)) * cutoff j (referencePrice X) ^ j) := by
        simpa only [neg_div] using hlo
      linarith only [hlo']
    have hh := mul_le_mul_of_nonneg_left he (pow_nonneg (log_nonneg hX) n)
    convert hh using 1 <;> ring
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero] using hsmall.const_mul 2

theorem F_secant {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ q : ℝ, 1 ≤ q ∧ q ≤ 1 + 1 / L ∧ F L b - F L a = (b - a) * q := by
  have hder (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (F L) (1 + 1 / (L + x)) x := by
    have hh := (hasDerivAt_id x).add
      (((hasDerivAt_id x).div_const L).const_add 1 |>.log (by positivity : 1 + x / L ≠ 0))
    convert hh using 1
    · funext y
      rfl
    · simp only [id_eq]
      field_simp [hL.ne', (by positivity : L + x ≠ 0)]
  have hordered (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
      ∃ q : ℝ, 1 ≤ q ∧ q ≤ 1 + 1 / L ∧ F L b - F L a = (b - a) * q := by
    have hc : ContinuousOn (F L) (Set.Icc a b) := fun x hx =>
      (hder x (ha.trans hx.1)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope (F L)
      (fun x => 1 + 1 / (L + x)) hab hc
      (fun x hx => hder x ((ha.trans hx.1.le)))
    have hc0 : 0 ≤ c := ha.trans hc.1.le
    refine ⟨1 + 1 / (L + c), ?_, ?_, ?_⟩
    · have hh : 0 ≤ 1 / (L + c) := by positivity
      linarith
    · have hh := one_div_le_one_div_of_le hL (by linarith : L ≤ L + c)
      linarith
    · exact ((eq_div_iff (sub_ne_zero.mpr hab.ne')).mp heq).symm.trans (by ring)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hordered a b ha hab
  · subst b
    exact ⟨1, le_rfl, by linarith [one_div_pos.mpr hL], by ring⟩
  · obtain ⟨q, hq0, hq1, hq⟩ := hordered b a hb hab
    exact ⟨q, hq0, hq1, by linarith only [hq]⟩

private theorem curvature_log_identity {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) :
    2 * F L a - F L (2 * a) = log (1 + a ^ 2 / (L ^ 2 + 2 * a * L)) := by
  have h1 : 0 < 1 + a / L := by positivity
  have h2 : 0 < 1 + 2 * a / L := by positivity
  have hD : 0 < L ^ 2 + 2 * a * L := by positivity
  have he : (1 + a / L) ^ 2 / (1 + 2 * a / L) =
      1 + a ^ 2 / (L ^ 2 + 2 * a * L) := by
    field_simp [hL.ne', hD.ne', h2.ne']
    ring
  rw [← he, log_div (pow_pos h1 2).ne' h2.ne', log_pow]
  dsimp [F]
  ring

/-- Actual j=2/j=4 curvature, with the actual moving cutoff error retained
until after multiplication by log² X. This is a limit in all real X. -/
theorem actual_two_four_curvature_tendsto :
    Tendsto (fun X : ℝ => log X ^ 2 *
      ((4 * log (cutoff 4 (referencePrice X)) - log X) -
        2 * (2 * log (cutoff 2 (referencePrice X)) - log X)))
      atTop (𝓝 (log (2 : ℝ) ^ 2)) := by
  classical
  let a := d 2
  let b := d 4
  let z := fun X : ℝ => a X ^ 2 / (log X ^ 2 + 2 * a X * log X)
  have ha : Tendsto a atTop (𝓝 (log (2 : ℝ))) := fixed_layer_root_offset_tendsto (by norm_num)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have haL : Tendsto (fun X : ℝ => a X / log X) atTop (𝓝 0) :=
    ha.div_atTop tendsto_log_atTop
  have hfac : Tendsto (fun X : ℝ => 1 + 2 * a X / log X) atTop (𝓝 1) := by
    simpa only [mul_div_assoc, mul_zero, add_zero] using
      tendsto_const_nhds.add (haL.const_mul 2)
  have hscaledz : Tendsto (fun X : ℝ => a X ^ 2 / (1 + 2 * a X / log X))
      atTop (𝓝 (log (2 : ℝ) ^ 2)) := by
    change Tendsto ((fun X : ℝ => a X ^ 2) /
      (fun X : ℝ => 1 + 2 * a X / log X)) atTop (𝓝 (log (2 : ℝ) ^ 2))
    simpa only [div_one] using (ha.pow 2).div hfac one_ne_zero
  have hz : Tendsto z atTop (𝓝 0) := by
    have hh := hscaledz.div_atTop
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_log_atTop)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), actual_root_equation (by norm_num : 2 ≤ 2)]
      with X hX haX
    dsimp [z]
    have ha0 : 0 < a X := haX.1
    have hL : 0 < log X := log_pos hX
    have hden : 0 < 1 + 2 * a X / log X := by positivity
    field_simp [hL.ne', hden.ne']
  have hzpos : ∀ᶠ X : ℝ in atTop, 0 < z X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), actual_root_equation (by norm_num : 2 ≤ 2)]
      with X hX haX
    dsimp [z]
    have ha0 : 0 < a X := haX.1
    have hL : 0 < log X := log_pos hX
    have hden : 0 < log X ^ 2 + 2 * a X * log X := by positivity
    exact div_pos (sq_pos_of_pos ha0) hden
  have hzright : Tendsto z atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hzpos⟩
  have hlogquot : Tendsto (fun X : ℝ => log (1 + z X) / z X) atTop (𝓝 1) := by
    have hh := (hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero_right.comp hzright
    simpa only [Function.comp_def, inv_one, log_one, sub_zero,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  have hlograte : Tendsto (fun X : ℝ => log X ^ 2 * log (1 + z X))
      atTop (𝓝 (log (2 : ℝ) ^ 2)) := by
    have hh := hlogquot.mul hscaledz
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hzpos,
      actual_root_equation (by norm_num : 2 ≤ 2)] with X hX hzX haX
    dsimp [z] at hzX ⊢
    have ha0 : 0 < a X := haX.1
    have hL : 0 < log X := log_pos hX
    have hden : 0 < log X ^ 2 + 2 * a X * log X := by positivity
    have hfacden : 0 < 1 + 2 * a X / log X := by positivity
    field_simp [hL.ne', (sq_pos_of_pos ha0).ne', hden.ne', hfacden.ne', hzX.ne']
  let good := fun X : ℝ => 1 < X ∧ 0 < a X ∧ 0 < b X
  have hgood : ∀ᶠ X : ℝ in atTop, good X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), actual_root_equation (by norm_num : 2 ≤ 2),
      actual_root_equation (by norm_num : 2 ≤ 4)] with X hX h2 h4
    exact ⟨hX, h2.1, h4.1⟩
  let q := fun X : ℝ => if h : good X then
    Classical.choose (F_secant (log_pos h.1) (by linarith [h.2.1] : 0 ≤ 2 * a X) h.2.2.le)
    else 1
  have hqspec : ∀ᶠ X : ℝ in atTop, 1 ≤ q X ∧ q X ≤ 1 + 1 / log X ∧
      F (log X) (b X) - F (log X) (2 * a X) = (b X - 2 * a X) * q X := by
    filter_upwards [hgood] with X hX
    simpa only [q, dif_pos hX] using Classical.choose_spec
      (F_secant (log_pos hX.1) (by linarith [hX.2.1] : 0 ≤ 2 * a X) hX.2.2.le)
  have hq : Tendsto q atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (hqspec.mono fun _ h => h.1) (hqspec.mono fun _ h => h.2.1)
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_log_atTop :
        Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0))
  have herr := (scaled_root_error (by norm_num : 2 ≤ 4) 2).sub
    ((scaled_root_error (by norm_num : 2 ≤ 2) 2).const_mul 2)
  simp only [mul_zero, sub_zero] at herr
  have hnum := hlograte.add herr
  simp only [add_zero] at hnum
  have hfinal := hnum.div hq one_ne_zero
  simp only [div_one] at hfinal
  apply hfinal.congr'
  filter_upwards [hgood, hqspec, actual_root_equation (by norm_num : 2 ≤ 2),
    actual_root_equation (by norm_num : 2 ≤ 4)] with X hX hqX h2 h4
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat]
      using (Real.log_pow (2 : ℝ) 2)
  have hcurv := curvature_log_identity (log_pos hX.1) hX.2.1.le
  have he : F (log X) (b X) - F (log X) (2 * a X) =
      log (1 + z X) + η 4 X - 2 * η 2 X := by
    change F (log X) (d 4 X) - F (log X) (2 * d 2 X) = _
    change 2 * F (log X) (d 2 X) - F (log X) (2 * d 2 X) = _ at hcurv
    rw [h2.2.2] at hcurv
    rw [h4.2.2]
    dsimp [z, a]
    linarith only [hcurv, hlog4]
  have hq0 : q X ≠ 0 := by linarith [hqX.1]
  change (log X ^ 2 * log (1 + z X) +
      (log X ^ 2 * η 4 X - 2 * (log X ^ 2 * η 2 X))) / q X = _
  rw [div_eq_iff hq0]
  change log X ^ 2 * log (1 + z X) +
      (log X ^ 2 * η 4 X - 2 * (log X ^ 2 * η 2 X)) =
        (log X ^ 2 * (4 * log (cutoff 4 (referencePrice X)) - log X -
          2 * (2 * log (cutoff 2 (referencePrice X)) - log X))) * q X
  have heq := hqX.2.2.symm.trans he
  have hscaled := congrArg (fun t : ℝ => log X ^ 2 * t) heq
  calc
    log X ^ 2 * log (1 + z X) +
        (log X ^ 2 * η 4 X - 2 * (log X ^ 2 * η 2 X)) =
        log X ^ 2 * ((b X - 2 * a X) * q X) := by
          linarith only [hscaled]
    _ = (log X ^ 2 * (4 * log (cutoff 4 (referencePrice X)) - log X -
          2 * (2 * log (cutoff 2 (referencePrice X)) - log X))) * q X := by
          dsimp [b, a, d]
          ring

#print axioms normalized_gain_bounds
#print axioms actual_two_four_curvature_tendsto
end D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
