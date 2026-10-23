/- GID: D5/S3/Analytic/IncompleteBetaShape/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Symmetric sliding beta kernels and their strict midpoint monotonicity. -/

import D5.S3.Analytic.KummerRatio.BetaIntegral
import D5.S3.Analytic.KilbasSaigo.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Sliding averages of a symmetric beta weight. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set MeasureTheory
open scoped Real

namespace D5.S3.Analytic.IncompleteBetaShape.Kernel

/-- The symmetric beta weight. -/
def w (b y : ℝ) : ℝ := (y * (1 - y)) ^ (b - 1)

/-- Uniform average of the beta weight on an affine interval. -/
def F (b s v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, w b (s * v + (1 - s) * u)

/-- Average over the beta distribution with shapes c and n+2. -/
def H (c : ℝ) (n : ℕ) (b v : ℝ) : ℝ :=
  (Real.Gamma c * Real.Gamma ((n : ℝ) + 2) / Real.Gamma (c + n + 2))⁻¹ *
    ∫ s in (0 : ℝ)..1,
      s ^ (c - 1) * (1 - s) ^ ((n : ℝ) + 1) * F b s v

private lemma w_nonneg (b : ℝ) {y : ℝ} (hy : y ∈ Icc 0 1) : 0 ≤ w b y :=
  Real.rpow_nonneg (mul_nonneg hy.1 (sub_nonneg.mpr hy.2)) _

private lemma w_symm (b y : ℝ) : w b (1-y) = w b y := by
  unfold w
  congr 1
  ring

private lemma w_integrable {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (w b) volume 0 1 := by
  have hi := D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight_integrable
    (α := 1-b) (a := 2*b-1) (by linarith) (by linarith)
  apply hi.congr
  intro y hy
  rw [Set.uIoc_of_le zero_le_one] at hy
  dsimp [D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight]
  rw [show 2*b-1+(1-b)-1 = b-1 by ring, show -(1-b) = b-1 by ring]
  exact (Real.mul_rpow hy.1.le (sub_nonneg.mpr hy.2)).symm

private lemma integral_w {b : ℝ} (hb : 0 < b) :
    (∫ y in (0:ℝ)..1, w b y) = Real.Gamma b * Real.Gamma b / Real.Gamma (2*b) := by
  have hi := D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.integral_weight
    (α := 1-b) (a := 2*b-1) (by linarith) (by linarith)
  rw [show 2*b-1+(1-b) = b by ring, show 1-(1-b) = b by ring,
    show 2*b-1+1 = 2*b by ring] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro y hy
  dsimp [D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight]
  rw [show 2*b-1+(1-b)-1 = b-1 by ring, show -(1-b) = b-1 by ring]
  exact Real.mul_rpow hy.1.le (sub_nonneg.mpr hy.2.le)

private lemma F_eq_window (b s v : ℝ) (hs : s ≠ 1) :
    F b s v = (1-s)⁻¹ * ∫ y in s*v..s*v+(1-s), w b y := by
  unfold F
  rw [intervalIntegral.integral_comp_add_mul _ (sub_ne_zero.mpr hs.symm)]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]

/-- Reflection in the midpoint preserves the affine uniform average. -/
theorem F_symm (b s v : ℝ) : F b s (1-v) = F b s v := by
  have he : (fun u => w b (s*(1-v)+(1-s)*u)) =
      fun u => w b (s*v+(1-s)*(1-u)) := by
    funext u
    rw [← w_symm b (s*v+(1-s)*(1-u))]
    congr 1
    ring
  unfold F
  rw [he]
  have hr := intervalIntegral.integral_comp_sub_left
    (fun u => w b (s*v+(1-s)*u)) (a := (0:ℝ)) (b := 1) 1
  simpa using hr

/-- Reflection in the midpoint preserves the beta averaged kernel. -/
theorem H_symm (c : ℝ) (n : ℕ) (b v : ℝ) : H c n b (1-v) = H c n b v := by
  unfold H
  simp only [F_symm]

private lemma w_subinterval {b x y : ℝ} (hb : 0 < b)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    IntervalIntegrable (w b) volume x y := by
  exact (w_integrable hb).mono_set (uIcc_subset_uIcc
    (by simpa only [uIcc_of_le zero_le_one] using hx)
    (by simpa only [uIcc_of_le zero_le_one] using hy))

private lemma affine_mem {s v : ℝ} (hs : s ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    s*v ∈ Icc 0 1 ∧ s*v+(1-s) ∈ Icc 0 1 := by
  have hp := mul_nonneg hs.1 hv.1
  have hq := mul_nonneg hs.1 (sub_nonneg.mpr hv.2)
  constructor <;> constructor <;> nlinarith [hs.1, hs.2, hv.1, hv.2]

private lemma F_eq_primitive {b s v : ℝ} (hb : 0 < b)
    (hs : s ∈ Ico 0 1) (hv : v ∈ Icc 0 1) :
    F b s v = (1-s)⁻¹ *
      ((∫ y in (0:ℝ)..s*v+(1-s), w b y) - ∫ y in (0:ℝ)..s*v, w b y) := by
  rw [F_eq_window b s v hs.2.ne]
  congr 1
  have hx := affine_mem ⟨hs.1, hs.2.le⟩ hv
  have hi0 := w_subinterval hb (show (0:ℝ) ∈ Icc 0 1 by norm_num) hx.1
  have hi1 := w_subinterval hb hx.1 hx.2
  linarith [intervalIntegral.integral_add_adjacent_intervals hi0 hi1]

private lemma F_joint_continuousOn {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun x : ℝ × ℝ => F b x.1 x.2) (Ico 0 1 ×ˢ Icc 0 1) := by
  have hP : ContinuousOn (fun x => ∫ y in (0:ℝ)..x, w b y) (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' (w_integrable hb)
        (show (0:ℝ) ∈ uIcc 0 1 by norm_num)
  have hl : Continuous (fun x : ℝ × ℝ => x.1*x.2) := by fun_prop
  have hr : Continuous (fun x : ℝ × ℝ => x.1*x.2+(1-x.1)) := by fun_prop
  have hlP := hP.comp (hl.continuousOn (s := Ico 0 1 ×ˢ Icc 0 1)) (fun x hx =>
    (affine_mem ⟨hx.1.1, hx.1.2.le⟩ hx.2).1)
  have hrP := hP.comp (hr.continuousOn (s := Ico 0 1 ×ˢ Icc 0 1)) (fun x hx =>
    (affine_mem ⟨hx.1.1, hx.1.2.le⟩ hx.2).2)
  have hi : ContinuousOn (fun x : ℝ × ℝ => (1-x.1)⁻¹) (Ico 0 1 ×ˢ Icc 0 1) :=
    (continuousOn_const.sub continuous_fst.continuousOn).inv₀
      (fun x hx => (sub_pos.mpr hx.1.2).ne')
  exact (hi.mul (hrP.sub hlP)).congr (fun x hx => F_eq_primitive hb hx.1 hx.2)

/-- For every genuine affine interval the average is continuous in its location. -/
theorem F_continuousOn {b s : ℝ} (hb : 0 < b) (hs : s ∈ Ico 0 1) :
    ContinuousOn (F b s) (Icc 0 1) := by
  have hc : ContinuousOn (fun v : ℝ => (s,v)) (Icc 0 1) :=
    continuousOn_const.prodMk continuousOn_id
  exact (F_joint_continuousOn hb).comp (f := fun v : ℝ => (s,v)) hc
    (fun v hv => ⟨hs, hv⟩)

private lemma F_nonneg {b s v : ℝ} (hs : s ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    0 ≤ F b s v := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  apply w_nonneg
  have hu0 := mul_nonneg (sub_nonneg.mpr hs.2) hu.1
  have hu1 := mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.mpr hs.2)
  have hx := affine_mem hs hv
  constructor <;> linarith [hx.1.1, hx.2.2]

/-- The full beta integral bounds every affine interval average. -/
theorem F_bound {b s v : ℝ} (hb : 0 < b) (hs : s ∈ Ico 0 1)
    (hv : v ∈ Icc 0 1) :
    |F b s v| ≤ (Real.Gamma b * Real.Gamma b / Real.Gamma (2*b)) / (1-s) := by
  rw [abs_of_nonneg (F_nonneg ⟨hs.1, hs.2.le⟩ hv), F_eq_window b s v hs.2.ne]
  have hx := affine_mem ⟨hs.1, hs.2.le⟩ hv
  have hle : (∫ y in s*v..s*v+(1-s), w b y) ≤ ∫ y in (0:ℝ)..1, w b y := by
    apply intervalIntegral.integral_mono_interval hx.1.1 (by linarith [hs.2]) hx.2.2
      _ (w_integrable hb)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun y hy => w_nonneg b ⟨hy.1.le, hy.2⟩))
  rw [integral_w hb] at hle
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (sub_pos.mpr hs.2).le)

private lemma w_continuousAt (b : ℝ) {y : ℝ} (hy : y ∈ Ioo 0 1) :
    ContinuousAt (w b) y := by
  apply (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).rpow_const
  exact Or.inl (mul_pos hy.1 (sub_pos.mpr hy.2)).ne'

private lemma F_hasDerivAt {b s v : ℝ} (hb : 0 < b) (hs : s ∈ Ioo 0 1)
    (hv : v ∈ Ioo 0 1) :
    HasDerivAt (F b s) (s/(1-s) * (w b (s*v+(1-s)) - w b (s*v))) v := by
  have hl : s*v ∈ Ioo 0 1 := ⟨mul_pos hs.1 hv.1, by nlinarith [hs.2, mul_pos hs.1 (sub_pos.mpr hv.2)]⟩
  have hr : s*v+(1-s) ∈ Ioo 0 1 := ⟨by nlinarith [hs.2, mul_pos hs.1 hv.1], by nlinarith [hs.2, mul_pos hs.1 (sub_pos.mpr hv.2)]⟩
  have hm (x : ℝ) (hx : x ∈ Ioo 0 1) :
      StronglyMeasurableAtFilter (w b) (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (fun y hy => (w_continuousAt b hy).continuousWithinAt) x hx
  have hp (x : ℝ) (hx : x ∈ Ioo 0 1) :=
    intervalIntegral.integral_hasDerivAt_right
      (w_subinterval hb (show (0:ℝ) ∈ Icc 0 1 by norm_num) ⟨hx.1.le, hx.2.le⟩)
      (hm x hx) (w_continuousAt b hx)
  have hd := (((hp _ hr).comp v (((hasDerivAt_id v).const_mul s).add_const (1-s))).sub
    ((hp _ hl).comp v ((hasDerivAt_id v).const_mul s))).const_mul ((1-s)⁻¹)
  have heq : F b s =ᶠ[nhds v] fun x =>
      (1-s)⁻¹ * ((∫ y in (0:ℝ)..s*x+(1-s), w b y) - ∫ y in (0:ℝ)..s*x, w b y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with x hx
    simpa only [add_sub_assoc] using F_eq_primitive hb ⟨hs.1.le,hs.2⟩ ⟨hx.1.le,hx.2.le⟩
  convert hd.congr_of_eventuallyEq heq using 1 <;> (try dsimp) <;> ring

private lemma F_strictMonoOn {b s : ℝ} (hb : 1 < b) (hs : s ∈ Ioo 0 1) :
    StrictMonoOn (F b s) (Ioc 0 (1/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
    ((F_continuousOn (by linarith : 0 < b) ⟨hs.1.le,hs.2⟩).mono
      (by intro v hv; constructor <;> linarith [hv.1,hv.2]))
  intro v hv
  simp only [interior_Ioc, mem_Ioo] at hv
  have hv1 : v ∈ Ioo 0 1 := ⟨hv.1, by linarith [hv.2]⟩
  rw [(F_hasDerivAt (by linarith : 0 < b) hs hv1).deriv]
  apply mul_pos (div_pos hs.1 (sub_pos.mpr hs.2))
  apply sub_pos.mpr
  apply Real.rpow_lt_rpow (mul_nonneg (mul_nonneg hs.1.le hv.1.le) (by nlinarith [hs.2])) _ (by linarith)
  have hid : (s*v+(1-s))*(1-(s*v+(1-s))) - (s*v)*(1-s*v) = s*(1-s)*(1-2*v) := by ring
  have hpos := mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2)) (by linarith [hv.2] : 0 < 1-2*v)
  linarith

private lemma F_strictAntiOn {b s : ℝ} (hb : 0 < b) (hb1 : b < 1) (hs : s ∈ Ioo 0 1) :
    StrictAntiOn (F b s) (Ioc 0 (1/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    ((F_continuousOn hb ⟨hs.1.le,hs.2⟩).mono
      (by intro v hv; constructor <;> linarith [hv.1,hv.2]))
  intro v hv
  simp only [interior_Ioc, mem_Ioo] at hv
  have hv1 : v ∈ Ioo 0 1 := ⟨hv.1, by linarith [hv.2]⟩
  rw [(F_hasDerivAt hb hs hv1).deriv]
  apply mul_neg_of_pos_of_neg (div_pos hs.1 (sub_pos.mpr hs.2))
  apply sub_neg.mpr
  apply Real.rpow_lt_rpow_of_neg (mul_pos (mul_pos hs.1 hv.1) (by nlinarith [hs.2])) _ (by linarith)
  have hid : (s*v+(1-s))*(1-(s*v+(1-s))) - (s*v)*(1-s*v) = s*(1-s)*(1-2*v) := by ring
  have hpos := mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2)) (by linarith [hv.2] : 0 < 1-2*v)
  linarith

private lemma density_continuousOn (c t : ℝ) :
    ContinuousOn (fun s : ℝ => s^(c-1) * (1-s)^t) (Ioo 0 1) :=
  (continuousOn_id.rpow_const (fun _ hs => Or.inl hs.1.ne')).mul
    ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun _ hs => Or.inl (sub_pos.mpr hs.2).ne'))

private lemma weighted_F_continuousOn {b v : ℝ} (hb : 0 < b)
    (hv : v ∈ Icc 0 1) (c t : ℝ) :
    ContinuousOn (fun s : ℝ => s^(c-1)*(1-s)^t * F b s v) (Ioo 0 1) := by
  have hF : ContinuousOn (fun s : ℝ => F b s v) (Ioo 0 1) := by
    have hc : ContinuousOn (fun s : ℝ => (s,v)) (Ioo 0 1) := by fun_prop
    exact (F_joint_continuousOn hb).comp (f := fun s : ℝ => (s,v)) hc
      (fun s hs => ⟨⟨hs.1.le,hs.2⟩,hv⟩)
  exact (density_continuousOn c t).mul hF

private def majorant (c : ℝ) (n : ℕ) (b s : ℝ) : ℝ :=
  (Real.Gamma b * Real.Gamma b / Real.Gamma (2*b)) *
    (s^(c-1) * (1-s)^(n:ℝ))

private lemma majorant_integrable {c : ℝ} (hc : 0 < c) (n : ℕ) (b : ℝ) :
    IntervalIntegrable (majorant c n b) volume 0 1 := by
  unfold majorant
  simpa only [add_sub_cancel_right] using
    (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta
      hc (show 0 < (n:ℝ)+1 by positivity)).const_mul
      (Real.Gamma b * Real.Gamma b / Real.Gamma (2*b))

private lemma weighted_F_bound {b s v : ℝ} (hb : 0 < b)
    (hs : s ∈ Ioo 0 1) (hv : v ∈ Icc 0 1) (c : ℝ) (n : ℕ) :
    ‖s^(c-1)*(1-s)^((n:ℝ)+1) * F b s v‖ ≤ majorant c n b s := by
  have hd : 0 ≤ s^(c-1)*(1-s)^((n:ℝ)+1) :=
    mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (sub_pos.mpr hs.2).le _)
  rw [norm_mul, Real.norm_of_nonneg hd, Real.norm_eq_abs]
  have hle := mul_le_mul_of_nonneg_left (F_bound hb ⟨hs.1.le,hs.2⟩ hv) hd
  have he : s^(c-1)*(1-s)^((n:ℝ)+1) *
      ((Real.Gamma b * Real.Gamma b / Real.Gamma (2*b))/(1-s)) = majorant c n b s := by
    rw [Real.rpow_add_one (sub_pos.mpr hs.2).ne']
    dsimp [majorant]
    field_simp [(sub_pos.mpr hs.2).ne']
  exact he ▸ hle

/-- The unnormalized beta average of the affine kernel is integrable. -/
theorem H_integrand_intervalIntegrable {c b v : ℝ} (hc : 0 < c) (hb : 0 < b)
    (n : ℕ) (hv : v ∈ Icc 0 1) :
    IntervalIntegrable (fun s : ℝ => s^(c-1)*(1-s)^((n:ℝ)+1)*F b s v) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (majorant_integrable hc n b)
  apply hi.mono' ((weighted_F_continuousOn hb hv c ((n:ℝ)+1)).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact weighted_F_bound hb hs hv c n

/-- The averaged kernel is continuous, including both endpoints. -/
theorem H_continuousOn {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (n : ℕ) :
    ContinuousOn (H c n b) (Icc 0 1) := by
  unfold H
  simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply continuousOn_const.mul
  apply continuousOn_of_dominated (bound := majorant c n b)
  · intro v hv
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (H_integrand_intervalIntegrable hc hb n hv)).aestronglyMeasurable
  · intro v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact weighted_F_bound hb hs hv c n
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (majorant_integrable hc n b)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact continuousOn_const.mul (F_continuousOn hb ⟨hs.1.le,hs.2⟩)

/-- The kernel is bounded on the closed unit interval. -/
theorem H_bounded {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, ∀ v ∈ Icc 0 1, ‖H c n b v‖ ≤ C := by
  exact isCompact_Icc.exists_bound_of_continuousOn (H_continuousOn hc hb n)

private lemma normalizer_pos {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < (Real.Gamma c * Real.Gamma ((n:ℝ)+2) / Real.Gamma (c+n+2))⁻¹ :=
  inv_pos.mpr (div_pos (mul_pos (Real.Gamma_pos_of_pos hc)
    (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity)))

/-- For b above one the beta averaged kernel strictly increases toward the midpoint. -/
theorem H_strictMonoOn_of_one_lt {c b : ℝ} (hc : 0 < c) (hb : 1 < b) (n : ℕ) :
    StrictMonoOn (H c n b) (Ioc 0 (1/2)) := by
  intro v hv z hz hvz
  have hv1 : v ∈ Icc 0 1 := ⟨hv.1.le, by linarith [hv.2]⟩
  have hz1 : z ∈ Icc 0 1 := ⟨hz.1.le, by linarith [hz.2]⟩
  have hb0 : 0 < b := by linarith
  unfold H
  apply mul_lt_mul_of_pos_left _ (normalizer_pos hc n)
  rw [← sub_pos]
  rw [← intervalIntegral.integral_sub
    (H_integrand_intervalIntegrable hc hb0 n hz1)
    (H_integrand_intervalIntegrable hc hb0 n hv1)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((H_integrand_intervalIntegrable hc hb0 n hz1).sub
      (H_integrand_intervalIntegrable hc hb0 n hv1)) _ zero_lt_one
  intro s hs
  have hd : 0 < s^(c-1)*(1-s)^((n:ℝ)+1) :=
    mul_pos (Real.rpow_pos_of_pos hs.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _)
  exact sub_pos.mpr (mul_lt_mul_of_pos_left (F_strictMonoOn hb hs hv hz hvz) hd)

/-- For b below one the beta averaged kernel strictly decreases toward the midpoint. -/
theorem H_strictAntiOn_of_lt_one {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hb1 : b < 1) (n : ℕ) : StrictAntiOn (H c n b) (Ioc 0 (1/2)) := by
  intro v hv z hz hvz
  have hv1 : v ∈ Icc 0 1 := ⟨hv.1.le, by linarith [hv.2]⟩
  have hz1 : z ∈ Icc 0 1 := ⟨hz.1.le, by linarith [hz.2]⟩
  unfold H
  apply mul_lt_mul_of_pos_left _ (normalizer_pos hc n)
  rw [← sub_pos]
  rw [← intervalIntegral.integral_sub
    (H_integrand_intervalIntegrable hc hb n hv1)
    (H_integrand_intervalIntegrable hc hb n hz1)]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((H_integrand_intervalIntegrable hc hb n hv1).sub
      (H_integrand_intervalIntegrable hc hb n hz1)) _ zero_lt_one
  intro s hs
  have hd : 0 < s^(c-1)*(1-s)^((n:ℝ)+1) :=
    mul_pos (Real.rpow_pos_of_pos hs.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _)
  exact sub_pos.mpr (mul_lt_mul_of_pos_left (F_strictAntiOn hb hb1 hs hv hz hvz) hd)

end D5.S3.Analytic.IncompleteBetaShape.Kernel
