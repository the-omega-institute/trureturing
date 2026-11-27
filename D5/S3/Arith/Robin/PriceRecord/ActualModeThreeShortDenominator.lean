/- GID: D5/S3/Arith/Robin/PriceRecord/ActualModeThreeShortDenominator
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualModeThreeShortDenominator
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Exact actual-root transport of the fixed-clock mode-three short-denominator exclusion. -/
import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation

/-! Transport the actual cutoff errors to the exact mode-three logarithmic residual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator

open Real Filter
open scoped Topology
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff (cutoff)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic (fixed_layer_root_offset_tendsto)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
  (d η F actual_root_equation normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation (mode_three_short_denominator_exclusion)

-- Split the logarithms to expose derivatives of the affine arguments.
private def G (s t : ℝ) : ℝ :=
  t * (log 2 + log s - log (s + 1)) - (log 3 + log s - log (s + t))

private theorem log_add_sub_log {s v : ℝ} (hs : 0 < s) (hsv : 0 < s + v) :
    log (s + v) - log s = log (1 + v / s) := by
  rw [← log_div hsv.ne' hs.ne', add_div, div_self hs.ne']

private theorem G_at_actual_cutoff {X : ℝ} (hL : 0 < log X) (ha : 0 < d 2 X)
    (hb : 0 < d 3 X) (h₂ : F (log X) (d 2 X) = log 2 + η 2 X)
    (h₃ : F (log X) (d 3 X) = log 3 + η 3 X) :
    G (log X / d 2 X) (d 3 X / d 2 X) = η 3 X - (d 3 X / d 2 X) * η 2 X := by
  let x := log X / d 2 X
  let t := d 3 X / d 2 X
  change G x t = η 3 X - t * η 2 X
  have hx : 0 < x := div_pos hL ha
  have ht : 0 < t := div_pos hb ha
  have htprod : t * d 2 X = d 3 X := div_mul_cancel₀ _ ha.ne'
  have h₂arg : 1 / x = d 2 X / log X := by
    change 1 / (log X / d 2 X) = _
    rw [one_div, inv_div]
  have h₃arg : t / x = d 3 X / log X := div_div_div_cancel_right₀ ha.ne' _ _
  have h₂form : log 2 - log (1 + d 2 X / log X) = d 2 X - η 2 X := by
    unfold F at h₂
    linarith only [h₂]
  have h₃form : log 3 - log (1 + d 3 X / log X) = d 3 X - η 3 X := by
    unfold F at h₃
    linarith only [h₃]
  calc
    G x t = t * (log 2 - (log (x + 1) - log x)) -
        (log 3 - (log (x + t) - log x)) := by unfold G; ring
    _ = t * (d 2 X - η 2 X) - (d 3 X - η 3 X) := by
      rw [log_add_sub_log hx (add_pos hx zero_lt_one),
        log_add_sub_log hx (add_pos hx ht), h₂arg, h₃arg, h₂form, h₃form]
    _ = η 3 X - t * η 2 X + (t * d 2 X - d 3 X) := by ring
    _ = _ := by rw [htprod, sub_self, add_zero]

private theorem actual_cutoff_error {j : ℕ} {X : ℝ} (hj : 1 ≤ j)
    (hd : 0 ≤ d j X) (hq : 2 ≤ cutoff j (referencePrice X)) :
    |η j X| ≤ 2 * exp (-(log X / (j : ℝ))) := by
  let q := cutoff j (referencePrice X)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  obtain ⟨_, _, hlo, hhi⟩ := normalized_gain_bounds hj hq
  change -2 / q ≤ η j X at hlo
  change η j X ≤ 0 at hhi
  have hclock : log X / (j : ℝ) ≤ log q := by
    change 0 ≤ (j : ℝ) * log q - log X at hd
    exact (div_le_iff₀ hj0).2 (by linarith only [hd])
  have hqExp : exp (log X / (j : ℝ)) ≤ q :=
    (exp_le_exp.mpr hclock).trans_eq (exp_log hq0)
  calc
    |η j X| ≤ 2 / q := by
      rw [abs_of_nonpos hhi]
      linarith only [show -(2 / q) ≤ η j X by simpa only [neg_div] using hlo]
    _ ≤ 2 / exp (log X / (j : ℝ)) :=
      (div_le_div_iff_of_pos_left (by norm_num) hq0 (exp_pos _)).2 hqExp
    _ = _ := by rw [exp_neg, div_eq_mul_inv]

private theorem G_deriv_s {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    HasDerivAt (fun y => G y t) (t * (t - 1) / (s * (s + 1) * (s + t))) s := by
  have hs1 : 0 < s + 1 := add_pos hs zero_lt_one
  have hst : 0 < s + t := add_pos_of_pos_of_nonneg hs ht
  have d₁ : HasDerivAt (fun y : ℝ => log (y + 1)) (s + 1)⁻¹ s := by
    simpa only [id_eq, one_div] using ((hasDerivAt_id s).add_const 1).log hs1.ne'
  have dt : HasDerivAt (fun y : ℝ => log (y + t)) (s + t)⁻¹ s := by
    simpa only [id_eq, one_div] using ((hasDerivAt_id s).add_const t).log hst.ne'
  have h := ((((hasDerivAt_log hs.ne').const_add (log 2)).sub d₁).const_mul t).sub
    (((hasDerivAt_log hs.ne').const_add (log 3)).sub dt)
  have he : t * (s⁻¹ - (s + 1)⁻¹) - (s⁻¹ - (s + t)⁻¹) =
      t * (t - 1) / (s * (s + 1) * (s + t)) := by
    field_simp [hs.ne', hs1.ne', hst.ne'] <;> ring
  rw [← he]
  convert h using 1
  funext y
  rfl

private theorem G_deriv_t {s t : ℝ} (hst : 0 < s + t) :
    HasDerivAt (G s) (log 2 + log s - log (s + 1) + (s + t)⁻¹) t := by
  have dt : HasDerivAt (fun y : ℝ => log (s + y)) (s + t)⁻¹ t := by
    simpa only [id_eq, one_div] using ((hasDerivAt_id t).const_add s).log hst.ne'
  have h := ((hasDerivAt_id t).mul_const (log 2 + log s - log (s + 1))).sub
    ((hasDerivAt_const t (log 3 + log s)).sub dt)
  convert h using 1
  · funext y
    rfl
  · simp

private theorem G_deriv_s_bound {B s t : ℝ} (hB : 1 ≤ B) (hs : B ≤ s)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    |t * (t - 1) / (s * (s + 1) * (s + t))| ≤ 2 / B ^ 3 := by
  have hB0 : 0 < B := by linarith only [hB]
  have hs0 : 0 < s := hB0.trans_le hs
  have ht0 : 0 ≤ t := zero_le_one.trans ht.1
  have ht1 : 0 ≤ t - 1 := sub_nonneg.mpr ht.1
  have hs1 : 0 < s + 1 := add_pos hs0 zero_lt_one
  have hden : 0 < s * (s + 1) * (s + t) :=
    mul_pos (mul_pos hs0 hs1) (add_pos_of_pos_of_nonneg hs0 ht0)
  have hnum : t * (t - 1) ≤ 2 := by
    calc
      _ ≤ 2 * 1 := mul_le_mul ht.2 (by linarith only [ht.2]) ht1 (by norm_num)
      _ = _ := mul_one _
  have hBase : B ^ 3 ≤ s * (s + 1) * (s + t) := calc
    _ = (B * B) * B := by ring
    _ ≤ (s * (s + 1)) * (s + t) :=
      mul_le_mul (mul_le_mul hs (by linarith only [hs]) hB0.le hs0.le)
        (le_trans hs (le_add_of_nonneg_right ht0)) hB0.le
        (mul_pos hs0 hs1).le
  rw [abs_of_nonneg (div_nonneg (mul_nonneg ht0 ht1) hden.le)]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans
    ((div_le_div_iff_of_pos_left (by norm_num) hden (pow_pos hB0 _)).2 hBase)

private theorem G_deriv_t_bound {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    log 2 + log s - log (s + 1) + (s + t)⁻¹ ∈ Set.Icc (0 : ℝ) (log 2) := by
  have hs0 : 0 < s := by linarith only [hs]
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hs1 : 0 < s + 1 := add_pos hs0 zero_lt_one
  have hst : 0 < s + t := add_pos_of_pos_of_nonneg hs0 ht0
  have hlog := log_add_sub_log hs0 hs1
  have harg : 0 < 1 + 1 / s := add_pos zero_lt_one (one_div_pos.mpr hs0)
  have hlogUpper : log (1 + 1 / s) ≤ log 2 :=
    log_le_log harg (by linarith only [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs])
  have hinv : 1 - (1 + 1 / s)⁻¹ = (s + 1)⁻¹ := by
    field_simp [hs0.ne', hs1.ne', harg.ne'] <;> ring
  have hlogLower : (s + 1)⁻¹ ≤ log (1 + 1 / s) := by
    rw [← hinv]
    exact one_sub_inv_le_log_of_pos harg
  have hrecip : (s + t)⁻¹ ≤ (s + 1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hs1 (add_le_add_right ht s)
  exact ⟨by linarith only [hlog, hlogUpper, (inv_pos.mpr hst).le],
    by linarith only [hlog, hlogLower, hrecip]⟩

private theorem G_sub_s_le {B x s t : ℝ} (hB : 1 ≤ B) (hx : B ≤ x) (hs : B ≤ s)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) : |G s t - G x t| ≤ (2 / B ^ 3) * |s - x| := by
  have hB0 : 0 < B := by linarith only [hB]
  have ht0 : 0 ≤ t := zero_le_one.trans ht.1
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (𝕜 := ℝ) B).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => G y t) (f' := fun y => t * (t - 1) / (y * (y + 1) * (y + t)))
      (fun _ hy => (G_deriv_s (hB0.trans_le hy) ht0).hasDerivWithinAt)
      (fun _ hy => by simpa only [Real.norm_eq_abs] using G_deriv_s_bound hB hy ht) hx hs

private theorem G_sub_t_le {s t u : ℝ} (hs : 1 ≤ s) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hu : u ∈ Set.Icc (1 : ℝ) 2) : |G s u - G s t| ≤ |u - t| := by
  have hs0 : 0 < s := by linarith only [hs]
  have hlog2 : log 2 < 1 := log_two_lt_d9.trans (by norm_num)
  have hbound (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) 2) :
      ‖log 2 + log s - log (s + 1) + (s + v)⁻¹‖ ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := G_deriv_t_bound hs hv.1
    rw [Real.norm_eq_abs, abs_of_nonneg hlo]
    exact hhi.trans hlog2.le
  simpa only [Real.norm_eq_abs, one_mul] using
    (convex_Icc (𝕜 := ℝ) (1 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := G s) (f' := fun v => log 2 + log s - log (s + 1) + (s + v)⁻¹)
      (fun v hv => (G_deriv_t (t := v)
        (add_pos_of_pos_of_nonneg hs0 (zero_le_one.trans hv.1))).hasDerivWithinAt) hbound ht hu

private theorem G_at_label {h m p : ℕ} (hh : 0 < (h : ℝ)) (hm : 0 < (m : ℝ)) :
    (h : ℝ) * G ((m : ℝ) / h) ((p : ℝ) / h) =
      (p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) -
        (h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p)) := by
  let s : ℝ := (m : ℝ) / h
  let t : ℝ := (p : ℝ) / h
  change (h : ℝ) * G s t = _
  have hs : 0 < s := div_pos hm hh
  have ht : 0 ≤ t := div_nonneg (Nat.cast_nonneg p) hh.le
  have hs1 : 0 < s + 1 := add_pos hs zero_lt_one
  have hst : 0 < s + t := add_pos_of_pos_of_nonneg hs ht
  have hratio (c v : ℝ) : c * s / (s + v / (h : ℝ)) =
      c * (m : ℝ) / ((m : ℝ) + v) := by
    dsimp only [s]
    rw [← add_div, ← mul_div_assoc, div_div_div_cancel_right₀ hh.ne']
  have h₁ : 2 * s / (s + 1) = 2 * (m : ℝ) / ((m : ℝ) + h) := by
    simpa only [div_self hh.ne'] using hratio 2 (h : ℝ)
  have h₃ : 3 * s / (s + t) = 3 * (m : ℝ) / ((m : ℝ) + p) := hratio 3 (p : ℝ)
  have htprod : (h : ℝ) * t = (p : ℝ) := mul_div_cancel₀ _ hh.ne'
  unfold G
  rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne',
    ← log_mul (by norm_num : (3 : ℝ) ≠ 0) hs.ne',
    ← log_div (mul_pos (by norm_num : (0 : ℝ) < 2) hs).ne' hs1.ne',
    ← log_div (mul_pos (by norm_num : (0 : ℝ) < 3) hs).ne' hst.ne',
    h₁, h₃, mul_sub, ← mul_assoc, htprod]

private theorem scale_label_error {k : ℝ} (hk : 0 < k) (z y : ℝ) :
    k * |y / k - z| = |k * z - y| := calc
  _ = |k * (y / k - z)| := by rw [abs_mul, abs_of_pos hk]
  _ = |y - k * z| := by rw [mul_sub, mul_div_cancel₀ y hk.ne']
  _ = _ := abs_sub_comm _ _

private theorem G_label_error_le {B x t : ℝ} {h m p : ℕ} (hh : 0 < (h : ℝ))
    (hm : 0 < (m : ℝ)) (hB : 1 ≤ B) (hx : B ≤ x) (hs : B ≤ (m : ℝ) / h)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) (hu : (p : ℝ) / h ∈ Set.Icc (1 : ℝ) 2) :
    |(p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) -
        (h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤
      |(h : ℝ) * t - p| + (2 / B ^ 3) * |(h : ℝ) * x - m| + (h : ℝ) * |G x t| := by
  let s : ℝ := (m : ℝ) / h
  let u : ℝ := (p : ℝ) / h
  have hstepT := G_sub_t_le (hB.trans hs) ht hu
  have hstepS := G_sub_s_le hB hx hs ht
  have hsplit : G s u = (G s u - G s t) + (G s t - G x t) + G x t := by ring
  have hgap : |G s u| ≤ |u - t| + (2 / B ^ 3) * |s - x| + |G x t| := calc
    _ = |(G s u - G s t) + (G s t - G x t) + G x t| := congrArg abs hsplit
    _ ≤ |G s u - G s t| + |G s t - G x t| + |G x t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hstepT hstepS) le_rfl
  calc
    _ = (h : ℝ) * |G s u| := by rw [← G_at_label hh hm, abs_mul, abs_of_pos hh]
    _ ≤ (h : ℝ) * (|u - t| + (2 / B ^ 3) * |s - x| + |G x t|) :=
      mul_le_mul_of_nonneg_left hgap hh.le
    _ = (h : ℝ) * |u - t| + (2 / B ^ 3) * ((h : ℝ) * |s - x|) + (h : ℝ) * |G x t| := by ring
    _ = _ := by rw [scale_label_error hh t p, scale_label_error hh x m]

/-- The actual cutoff residual and its label hypotheses hold with a threshold
independent of the natural label `(h, m, p)`. -/
theorem eventually_mode_three_residual_bound {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop,
      let L := log X
      let x := L / d 2 X
      let t := d 3 X / d 2 X
      ∀ h m p : ℕ, 0 < h →
        |(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) →
        |(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2 →
        h < m ∧ h < p ∧ 5 * p ≤ 8 * h ∧ (m : ℝ) ≤ 2 * (h : ℝ) * L ∧
        |(p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) -
            (h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤
          (2 * K + 6) * ((L ^ 2)⁻¹ * exp (-(L / 15)) + (h : ℝ) * exp (-(L / 3))) := by
  have ha₂ : Tendsto (d 2) atTop (𝓝 (log 2)) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  have ha₃ : Tendsto (d 3) atTop (𝓝 (log 3)) :=
    fixed_layer_root_offset_tendsto (by norm_num)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have htlim : Tendsto (fun X : ℝ => d 3 X / d 2 X) atTop (𝓝 (log 3 / log 2)) :=
    ha₃.div ha₂ hlog2.ne'
  have hrlo : (3 / 2 : ℝ) < log 3 / log 2 := (lt_div_iff₀ hlog2).2 (by
    linarith only [log_two_lt_d9, log_three_gt_d9])
  have hrhi : log 3 / log 2 < (159 / 100 : ℝ) := (div_lt_iff₀ hlog2).2 (by
    linarith only [log_two_gt_d9, log_three_lt_d9])
  have halow : (2 / 3 : ℝ) < log 2 := (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans log_two_gt_d9
  have hahi : log 2 < 1 := log_two_lt_d9.trans (by norm_num)
  filter_upwards [actual_root_equation (j := 2) (by norm_num),
    actual_root_equation (j := 3) (by norm_num),
    ha₂.eventually (eventually_gt_nhds halow), ha₂.eventually (eventually_lt_nhds hahi),
    htlim.eventually (eventually_gt_nhds hrlo), htlim.eventually (eventually_lt_nhds hrhi),
    tendsto_log_atTop.eventually_ge_atTop (exp 50),
    tendsto_log_atTop.eventually_ge_atTop (1500 * K)]
    with X haRoot hbRoot haLo haHi htLo htHi hExp hLK
  dsimp only
  let L := log X
  let x := L / d 2 X
  let t := d 3 X / d 2 X
  change (3 / 2 : ℝ) < t at htLo
  change t < (159 / 100 : ℝ) at htHi
  change exp 50 ≤ L at hExp
  change 1500 * K ≤ L at hLK
  have hL16 : 16 ≤ L := by linarith only [hExp, add_one_le_exp (50 : ℝ)]
  have hL : 0 < L := by linarith only [hL16]
  have hLs : 0 < L ^ 2 := sq_pos_of_pos hL
  have hLsq1 : 1 ≤ L ^ 2 := by
    have hL1 : 1 ≤ L := by linarith only [hL16]
    simpa only [one_pow] using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL1 2)
  have hdxlo : L ≤ x := (le_div_iff₀ haRoot.1).2 (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left haHi.le hL.le)
  have hdxhi : x ≤ (3 / 2) * L := (div_le_iff₀ haRoot.1).2 (calc
    L = ((3 / 2) * L) * (2 / 3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left haLo.le (mul_nonneg (by norm_num) hL.le))
  have ht₁₂ : t ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨by linarith only [htLo], by linarith only [htHi]⟩
  have haEq : F L (d 2 X) = log 2 + η 2 X := by
    simpa only [Nat.cast_ofNat] using haRoot.2.2
  have hbEq : F L (d 3 X) = log 3 + η 3 X := by
    simpa only [Nat.cast_ofNat] using hbRoot.2.2
  have hη₂ : |η 2 X| ≤ 2 * exp (-(L / 2)) := by
    simpa only [Nat.cast_ofNat] using
      (actual_cutoff_error (j := 2) (by norm_num) haRoot.1.le haRoot.2.1.le)
  have hη₃ : |η 3 X| ≤ 2 * exp (-(L / 3)) := by
    simpa only [Nat.cast_ofNat] using
      (actual_cutoff_error (j := 3) (by norm_num) hbRoot.1.le hbRoot.2.1.le)
  have hη₂' : |η 2 X| ≤ 2 * exp (-(L / 3)) := hη₂.trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hL])) (by norm_num))
  have hG : |G x t| ≤ 6 * exp (-(L / 3)) := calc
    _ = |η 3 X - t * η 2 X| := congrArg abs (G_at_actual_cutoff hL haRoot.1 hbRoot.1 haEq hbEq)
    _ ≤ |η 3 X| + |t * η 2 X| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (η 3 X) (-(t * η 2 X))
    _ = |η 3 X| + t * |η 2 X| := by rw [abs_mul, abs_of_nonneg (zero_le_one.trans ht₁₂.1)]
    _ ≤ 2 * exp (-(L / 3)) + 2 * (2 * exp (-(L / 3))) := add_le_add hη₃
      ((mul_le_mul_of_nonneg_left hη₂' (zero_le_one.trans ht₁₂.1)).trans
        (mul_le_mul_of_nonneg_right ht₁₂.2 (mul_nonneg (by norm_num) (exp_pos _).le)))
    _ = _ := by ring
  have hEsmall : K * exp (-(L / 15)) ≤ 1 / 100 := by
    have hbound : 100 * K ≤ exp (L / 15) :=
      (show 100 * K ≤ L / 15 + 1 by linarith only [hLK]).trans (add_one_le_exp (L / 15))
    have hmul := mul_le_mul_of_nonneg_right hbound (exp_pos (-(L / 15))).le
    rw [← exp_add, add_neg_cancel, exp_zero] at hmul
    calc
      K * exp (-(L / 15)) = (100 * K * exp (-(L / 15))) / 100 := by ring
      _ ≤ 1 / 100 := div_le_div_of_nonneg_right hmul (by norm_num)
  have hEinvsmall : K * exp (-(L / 15)) / L ^ 2 ≤ 1 / 100 := (div_le_iff₀ hLs).2
    (hEsmall.trans (by linarith only [hLsq1]))
  have hB : 1 ≤ L / 2 := by linarith only [hL16]
  have hCoeff : 2 / (L / 2) ^ 3 ≤ (L ^ 2)⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ (pow_pos (half_pos hL) 3) hLs).2
    have hmul := mul_le_mul_of_nonneg_right hL16 (sq_nonneg L)
    nlinarith only [hmul]
  intro h m p hh hM hP
  change |(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) at hM
  change |(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2 at hP
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hh0 : (0 : ℝ) < h := zero_lt_one.trans_le hh1
  have hlabel (y z : ℝ) (herr : |(h : ℝ) * z - y| ≤ 1 / 100) :
      |y / (h : ℝ) - z| ≤ 1 / 100 := calc
    _ ≤ (h : ℝ) * |y / (h : ℝ) - z| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh1 (abs_nonneg _)
    _ = |(h : ℝ) * z - y| := scale_label_error hh0 z y
    _ ≤ _ := herr
  obtain ⟨hmLo, hmHi⟩ := abs_le.mp (hlabel m x (hM.trans hEsmall))
  obtain ⟨hpLo, hpHi⟩ := abs_le.mp (hlabel p t (hP.trans hEinvsmall))
  have hms : L / 2 ≤ (m : ℝ) / h := by linarith only [hmLo, hdxlo, hL16]
  have hmul : (m : ℝ) / h ≤ 2 * L := by linarith only [hmHi, hdxhi, hL16]
  have hpl : 1 < (p : ℝ) / h := by linarith only [hpLo, htLo]
  have hpu : (p : ℝ) / h ≤ (8 / 5 : ℝ) := by linarith only [hpHi, htHi]
  have hhm : h < m := by
    have hlt : (1 : ℝ) < (m : ℝ) / h := by linarith only [hms, hL16]
    exact_mod_cast (show (h : ℝ) < m by simpa only [one_mul] using (lt_div_iff₀ hh0).1 hlt)
  have hhp : h < p := by
    exact_mod_cast (show (h : ℝ) < p by simpa only [one_mul] using (lt_div_iff₀ hh0).1 hpl)
  have hp85 : 5 * p ≤ 8 * h := by
    have hpR := (div_le_iff₀ hh0).1 hpu
    exact_mod_cast (show 5 * (p : ℝ) ≤ 8 * (h : ℝ) by linarith only [hpR])
  have hmClock : (m : ℝ) ≤ 2 * (h : ℝ) * L :=
    ((div_le_iff₀ hh0).1 hmul).trans_eq (by ring)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (hh.trans hhm)
  refine ⟨hhm, hhp, hp85, hmClock, ?_⟩
  have hR := G_label_error_le (x := x) hh0 hm0 hB (by linarith only [hdxlo, hL]) hms ht₁₂
    (show (p : ℝ) / h ∈ Set.Icc (1 : ℝ) 2 from ⟨hpl.le, hpu.trans (by norm_num)⟩)
  have hS : (2 / (L / 2) ^ 3) * |(h : ℝ) * x - m| ≤ K * ((L ^ 2)⁻¹ * exp (-(L / 15))) := calc
    _ ≤ (L ^ 2)⁻¹ * |(h : ℝ) * x - m| := mul_le_mul_of_nonneg_right hCoeff (abs_nonneg _)
    _ ≤ (L ^ 2)⁻¹ * (K * exp (-(L / 15))) := mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hLs.le)
    _ = _ := by ring
  have hT : |(h : ℝ) * t - p| ≤ K * ((L ^ 2)⁻¹ * exp (-(L / 15))) :=
    hP.trans_eq (by rw [div_eq_mul_inv]; ring)
  have hRemainder : (h : ℝ) * |G x t| ≤ 6 * ((h : ℝ) * exp (-(L / 3))) :=
    (mul_le_mul_of_nonneg_left hG hh0.le).trans_eq (by ring)
  have hParts (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      K * a + K * a + 6 * b ≤ (2 * K + 6) * (a + b) := by
    nlinarith only [mul_nonneg hK hb, ha]
  exact (hR.trans (add_le_add (add_le_add hT hS) hRemainder)).trans
    (hParts _ _ (mul_nonneg (inv_nonneg.mpr hLs.le) (exp_pos _).le)
      (mul_nonneg hh0.le (exp_pos _).le))

/-- Eventual mode-three short-denominator nonresonance for the actual cutoff. -/
theorem eventually_mode_three_short_denominator_exclusion {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop,
      let L := log X
      let x := L / d 2 X
      let t := d 3 X / d 2 X
      ∀ h m p : ℕ, 0 < h → (h : ℝ) ≤ L / (50 * log L) →
        ¬ (|(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) ∧
          |(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2) := by
  let C := 2 * K + 6
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hK]
  filter_upwards [eventually_mode_three_residual_bound hK,
    tendsto_log_atTop.eventually_ge_atTop (exp 50),
    tendsto_log_atTop.eventually_gt_atTop (1500 * log (2 * C))] with X hR hL hLC
  dsimp only at hR ⊢
  intro h m p hh hshort hlabels
  obtain ⟨hhm, hhp, hp85, hmClock, hResidual⟩ := hR h m p hh hlabels.1 hlabels.2
  exact mode_three_short_denominator_exclusion hh hhm hhp hp85 hmClock hL hshort hC hLC hResidual

end D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
