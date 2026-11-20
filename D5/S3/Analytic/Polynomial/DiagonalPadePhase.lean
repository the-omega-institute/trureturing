/- GID: D5/S3/Analytic/Polynomial/DiagonalPadePhase
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadePhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The analytic phase and exact quantization of central diagonal Padé poles. -/
module

public import D5.S3.Analytic.Polynomial.DiagonalPadeExponential
import all D5.S3.Analytic.HalfIntegerBessel
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Central phase of the diagonal exponential Padé denominator

Escape audit unfinished for the public theorems in this module.
https://github.com/the-omega-institute/trureturing/issues/32304
-/

public section

open Set Metric
open Polynomial (aeval)
open D5.S3.Analytic.Polynomial.DiagonalPadeExponential (denominator denominator_eq_bessel)
open scoped Topology
open D5.S3.Analytic.HalfIntegerBessel
  (order S eta K I F_K F_I S_re_pos eta_eq_log_div hasDerivAt_eta radial_eta_re_atBot
    F_I_div_F_K sectorMass sector_K_estimate sector_I_estimate)

namespace D5.S3.Analytic.Polynomial.DiagonalPadePhase

private theorem order_pos (m : ℕ) : 0 < order m := by
  rw [order]
  positivity

private theorem S_ofReal (x : ℝ) :
    S (x : ℂ) = (Real.sqrt (1 + x ^ 2) : ℂ) := by
  rw [S, show (1 + (x : ℂ) ^ 2) = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 by
    rw [← Complex.ofReal_pow (Real.sqrt (1 + x ^ 2)), Real.sq_sqrt (by positivity)]
    push_cast
    rfl]
  exact Complex.sq_cpow_two_inv (by rw [Complex.ofReal_re]; positivity)

private theorem eta_ofReal {x : ℝ} (hx : 0 < x) :
    eta (x : ℂ) =
      ((Real.sqrt (1 + x ^ 2) + Real.log (x / (1 + Real.sqrt (1 + x ^ 2))) : ℝ) : ℂ) := by
  rw [eta_eq_log_div (by simpa using hx), S_ofReal]
  push_cast [Complex.ofReal_log (show 0 ≤ x / (1 + Real.sqrt (1 + x ^ 2)) by positivity)]
  rfl

private theorem etaReal_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (eta (t : ℂ)).re) (Real.sqrt (1 + x ^ 2) / x) x := by
  have h := (hasDerivAt_eta (w := (x : ℂ)) (by simpa using hx)).comp_ofReal
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  simpa [S_ofReal, ← Complex.ofReal_div, Function.comp_def] using hre

/-- The native phase has exactly one positive real zero. It lies below one and is simple. -/
theorem exists_eta_positive_zero :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ eta (c : ℂ) = 0 ∧
      (∀ x : ℝ, 0 < x → eta (x : ℂ) = 0 → x = c) ∧
      HasDerivAt eta ((Real.sqrt (1 + c ^ 2) / c : ℝ) : ℂ) (c : ℂ) := by
  let f (x : ℝ) := (eta (x : ℂ)).re
  have hdiff (x : ℝ) (hx : 0 < x) := etaReal_hasDerivAt hx
  have hcont : ContinuousOn f (Ioi 0) :=
    fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont
    intro x hx
    have hx' : 0 < x := by simpa [interior_Ioi] using hx
    rw [(hdiff x hx').deriv]
    positivity
  have hlim : Filter.Tendsto f (𝓝[>] 0) Filter.atBot := by
    simpa [f] using radial_eta_re_atBot (u := 1) (by simp)
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < 0 := hlim.eventually (Filter.eventually_lt_atBot 0)
  obtain ⟨a, ha, ha'⟩ := (hnear.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have h1 : 0 < f 1 := by
    dsimp only [f]
    rw [eta_ofReal zero_lt_one, Complex.ofReal_re, one_pow, Real.log_div (by norm_num)
      (by positivity), Real.log_one]
    have hs : 0 < Real.sqrt (1 + 1) := by positivity
    have hb := Real.log_lt_sub_one_of_pos (show 0 < 1 + Real.sqrt (1 + 1) by positivity)
      (ne_of_gt (lt_add_of_pos_right 1 hs))
    linarith
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc ha'.2.le
    (hcont.mono (fun x hx => ha'.1.trans_le hx.1)) ⟨ha.le, h1.le⟩
  have hcp := ha'.1.trans_le hc.1
  refine ⟨c, hcp, hc.2.lt_of_ne ?_, ?_, ?_, ?_⟩
  · rintro rfl
    rw [hc0] at h1
    exact lt_irrefl _ h1
  · rw [eta_ofReal hcp, ← Complex.ofReal_zero, Complex.ofReal_inj]
    simpa only [f, eta_ofReal hcp, Complex.ofReal_re] using hc0
  · intro x hx hz
    apply hmono.injOn hx hcp
    simpa [f, hz] using hc0.symm
  · simpa only [S_ofReal, Complex.ofReal_div] using
      hasDerivAt_eta (w := (c : ℂ)) (by simpa using hcp)

/-- The corrected phase uses the principal logarithm of the regular to decaying amplitude ratio. -/
noncomputable def polePhase (m : ℕ) (w : ℂ) : ℂ :=
  eta w + Complex.log (F_I m w / F_K m w) / (2 * (order m : ℂ))

private theorem sector_re_pos {κ : ℝ} (hκ : 0 < κ) {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    0 < w.re := (mul_nonneg hκ.le (norm_nonneg _)).trans_lt hw

private theorem scale_re_pos {m : ℕ} {w : ℂ} (hw : 0 < w.re) :
    0 < ((order m : ℂ) * w).re := by
  simpa [Complex.mul_re] using mul_pos (order_pos m) hw

private theorem hk_mass {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) {m : ℕ}
    (hm : 40 * sectorMass κ / κ ≤ order m) : 4 * sectorMass κ ≤ order m := by
  have hp : 0 < sectorMass κ := by rw [sectorMass]; positivity
  have hh := (div_le_iff₀ hκ).mp hm
  have hk := mul_le_mul_of_nonneg_left hκ' (order_pos m).le
  linarith

private theorem relative_close {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) {m : ℕ}
    (hm : 40 * sectorMass κ / κ ≤ order m) {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    ‖F_I m w / F_K m w - 1‖ ≤ 20 * sectorMass κ / κ / order m ∧
      20 * sectorMass κ / κ / order m ≤ 1 / 2 := by
  have hw0 : w ≠ 0 := by
    intro hz
    simp [hz] at hw
  refine ⟨?_, ?_⟩
  · convert (sector_I_estimate m hκ (hk_mass hκ hκ' hm) hw0 hw.le).1 using 1
    ring
  · rw [div_le_iff₀ (order_pos m)]
    linarith [show 40 * sectorMass κ / κ = 2 * (20 * sectorMass κ / κ) by ring]

private theorem re_pos_of_close_to_one {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) : 0 < z.re := by
  have hb := (Complex.abs_re_le_norm (z - 1)).trans hz
  simp only [Complex.sub_re, Complex.one_re] at hb
  linarith [(abs_le.mp hb).1]

private theorem sector_K_nonzero {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) {m : ℕ}
    (hm : 40 * sectorMass κ / κ ≤ order m) {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    F_K m w ≠ 0 ∧ K m ((order m : ℂ) * w) ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro hz
    simp [hz] at hw
  obtain ⟨hf, hf', hk⟩ := sector_K_estimate m hκ (hk_mass hκ hκ' hm) hw0 hw.le
  have hr := re_pos_of_close_to_one (hf.trans hf')
  exact ⟨fun he => by simp [he] at hr, hk⟩

private theorem isOpen_sector (κ : ℝ) : IsOpen {w : ℂ | κ * ‖w‖ < w.re} :=
  isOpen_lt (continuous_const.mul continuous_norm) Complex.continuous_re

private theorem analyticOnNhd_eta :
    AnalyticOnNhd ℂ eta {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  exact fun _ hw => (hasDerivAt_eta hw).differentiableAt.differentiableWithinAt

/-- The analytic phase in the open sector has nonzero amplitudes and inverse-square error. -/
theorem polePhase_sector (m : ℕ) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hm : 40 * sectorMass κ / κ ≤ order m) {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    F_K m w ≠ 0 ∧ F_I m w ≠ 0 ∧ 0 < (F_I m w / F_K m w).re ∧
      AnalyticAt ℂ (polePhase m) w ∧
      ‖polePhase m w - eta w‖ ≤ (15 * sectorMass κ / κ) / order m ^ 2 := by
  have hK := sector_K_nonzero hκ hκ' hm hw
  have hclose := relative_close hκ hκ' hm hw
  have hr := re_pos_of_close_to_one (hclose.1.trans hclose.2)
  have hratio : AnalyticAt ℂ (fun v => F_I m v / F_K m v) w := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_sector κ) w hw
    intro v hv
    have hvre := sector_re_pos hκ hv
    have hscaled := scale_re_pos (m := m) hvre
    let arg : ℂ → ℂ := fun t => (order m : ℂ) * t
    have harg : DifferentiableAt ℂ arg v := (differentiableAt_const _).mul differentiableAt_id
    have hI : DifferentiableAt ℂ (fun t => I m (arg t)) v :=
      (HalfIntegerBessel.hasDerivAt_I m hscaled).differentiableAt.comp v harg
    have hK' : DifferentiableAt ℂ (fun t => K m (arg t)) v :=
      (HalfIntegerBessel.hasDerivAt_K m hscaled).differentiableAt.comp v harg
    have hexp : DifferentiableAt ℂ (fun t => Complex.exp (-2 * (order m : ℂ) * eta t)) v :=
      (Complex.differentiable_exp _).comp v
        ((differentiableAt_const _).mul (hasDerivAt_eta hvre).differentiableAt)
    refine ((differentiableAt_const (Real.pi : ℂ)).mul (hexp.mul (hI.div hK'
      (sector_K_nonzero hκ hκ' hm hv).2))).differentiableWithinAt.congr ?_ ?_
    · intro t ht
      simpa [arg, mul_assoc] using F_I_div_F_K m (sector_re_pos hκ ht)
        (sector_K_nonzero hκ hκ' hm ht).2
    · simpa [arg, mul_assoc] using F_I_div_F_K m hvre (sector_K_nonzero hκ hκ' hm hv).2
  have hlog : AnalyticAt ℂ (fun v => Complex.log (F_I m v / F_K m v)) w :=
    hratio.clog (Complex.mem_slitPlane_iff.mpr (Or.inl hr))
  have hν := order_pos m
  refine ⟨hK.1, fun hz => by simp [hz] at hr, hr,
    (analyticOnNhd_eta w (sector_re_pos hκ hw)).add hlog.div_const, ?_⟩
  have hb := Complex.norm_log_one_add_half_le_self (hclose.1.trans hclose.2)
  rw [show 1 + (F_I m w / F_K m w - 1) = F_I m w / F_K m w by ring] at hb
  rw [polePhase, add_sub_cancel_left, norm_div, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg hν.le]
  calc
    _ ≤ ((3 / 2) * (20 * sectorMass κ / κ / order m)) / (2 * order m) :=
      div_le_div_of_nonneg_right
        (hb.trans (mul_le_mul_of_nonneg_left hclose.1 (by norm_num))) (by positivity)
    _ = _ := by ring

/-- The phase value corresponding to the integer pole index. -/
noncomputable def polePhaseLattice (m : ℕ) (j : ℤ) : ℂ :=
  (j : ℂ) * (Real.pi : ℂ) * Complex.I / (order m : ℂ)

/-- On the branch-controlled sector the odd-order zeros are exactly the phase lattice. -/
theorem denominator_zero_iff_polePhase (m : ℕ) (hmOdd : Odd m) {κ : ℝ}
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hm : 40 * sectorMass κ / κ ≤ order m)
    {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
      ∃ j : ℤ, polePhase m w = polePhaseLattice m j := by
  simp only [polePhaseLattice]
  have hwre := sector_re_pos hκ hw
  have hK := (sector_K_nonzero hκ hκ' hm hw).2
  have hre := (polePhase_sector m hκ hκ' hm hw).2.2.1
  have hA : F_I m w / F_K m w ≠ 0 := fun hz => by simp [hz] at hre
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  have hz : 0 < (2 * (order m : ℂ) * w).re := by
    simpa [mul_assoc, Complex.mul_re] using
      mul_pos (show (0 : ℝ) < 2 by norm_num) (scale_re_pos (m := m) hwre)
  obtain ⟨hfactor, heq⟩ := denominator_eq_bessel m hz
  have hhalf : 2 * (order m : ℂ) * w / 2 = (order m : ℂ) * w := by ring
  have hphase :
      Complex.exp (2 * (order m : ℂ) * polePhase m w) =
        (Real.pi : ℂ) * I m ((order m : ℂ) * w) / K m ((order m : ℂ) * w) := by
    rw [polePhase, show (2 * (order m : ℂ) *
      (eta w + Complex.log (F_I m w / F_K m w) / (2 * (order m : ℂ)))) =
      2 * (order m : ℂ) * eta w + Complex.log (F_I m w / F_K m w) by
        field_simp [hν],
      Complex.exp_add, Complex.exp_log hA, F_I_div_F_K m hwre hK]
    rw [show -2 * (order m : ℂ) * eta w = -(2 * (order m : ℂ) * eta w) by ring,
      Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
  rw [heq, hhalf, hmOdd.neg_one_pow, neg_one_mul, neg_mul,
    mul_eq_zero_iff_left (mul_ne_zero hfactor (Complex.exp_ne_zero _)), ← sub_eq_add_neg,
    sub_eq_zero]
  have hbalance :
      K m ((order m : ℂ) * w) = (Real.pi : ℂ) * I m ((order m : ℂ) * w) ↔
        Complex.exp (2 * (order m : ℂ) * polePhase m w) = 1 := by
    rw [hphase, div_eq_iff hK, one_mul, eq_comm]
  rw [hbalance, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, (eq_div_iff hν).2 ?_⟩
    linear_combination hj / 2
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hj]
    field_simp

private theorem closedBall_subset_sector {c : ℝ} (hc : 0 < c) :
    closedBall (c : ℂ) (c / 2) ⊆ {w : ℂ | (1 / 4 : ℝ) * ‖w‖ < w.re} := by
  intro w hw
  have hd : ‖w - (c : ℂ)‖ ≤ c / 2 := mem_closedBall_iff_norm.mp hw
  have hre := Complex.re_le_norm ((c : ℂ) - w)
  rw [norm_sub_rev, Complex.sub_re, Complex.ofReal_re] at hre
  have hnorm : ‖w‖ ≤ c / 2 + c := by
    calc
      ‖w‖ ≤ ‖w - (c : ℂ)‖ + ‖(c : ℂ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - (c : ℂ)) (c : ℂ)
      _ ≤ _ := by simpa [Real.norm_eq_abs, abs_of_pos hc] using add_le_add_right hd c
  change (1 / 4 : ℝ) * ‖w‖ < w.re
  linarith

/-- The value and derivative of the phase perturbation are uniformly inverse-square
in the order on fixed nested disks about a positive real point. -/
theorem polePhase_compact_estimate (m : ℕ) {c : ℝ} (hc : 0 < c)
    (hm : 160 * sectorMass (1 / 4) ≤ order m) :
    (∀ w ∈ closedBall (c : ℂ) (c / 2),
      ‖polePhase m w - eta w‖ ≤ 60 * sectorMass (1 / 4) / order m ^ 2) ∧
    ∀ w ∈ closedBall (c : ℂ) (c / 4),
      ‖deriv (polePhase m) w - deriv eta w‖ ≤
        240 * sectorMass (1 / 4) / (c * order m ^ 2) := by
  let U : Set ℂ := {w | (1 / 4 : ℝ) * ‖w‖ < w.re}
  let e : ℂ → ℂ := fun w => polePhase m w - eta w
  have hthreshold : 40 * sectorMass (1 / 4) / (1 / 4) ≤ order m := by
    convert hm using 1
    ring
  have hphase (w : ℂ) (hw : w ∈ U) :=
    polePhase_sector m (by norm_num) (by norm_num) hthreshold hw
  have ha (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ e w :=
    (hphase w hw).2.2.2.1.sub (analyticOnNhd_eta w (sector_re_pos (by norm_num) hw))
  have hval (w : ℂ) (hw : w ∈ closedBall (c : ℂ) (c / 2)) :
      ‖e w‖ ≤ 60 * sectorMass (1 / 4) / order m ^ 2 := by
    convert (hphase w (closedBall_subset_sector hc hw)).2.2.2.2 using 1
    ring
  refine ⟨hval, ?_⟩
  intro w hw
  have hwU : w ∈ U := closedBall_subset_sector hc
    (closedBall_subset_closedBall (by linarith) hw)
  have hdisk : closedBall w (c / 4) ⊆ closedBall (c : ℂ) (c / 2) := by
    intro v hv
    apply mem_closedBall.mpr
    have htri := dist_triangle v w (c : ℂ)
    have hv' := mem_closedBall.mp hv
    have hw' := mem_closedBall.mp hw
    linarith
  have hderiv : Complex.cderiv (c / 4) e w = deriv e w :=
    Complex.cderiv_eq_deriv (isOpen_sector (1 / 4))
      (fun v hv => (ha v hv).differentiableAt.differentiableWithinAt)
      (by positivity) (fun _ hv => closedBall_subset_sector hc (hdisk hv))
  have hb := Complex.norm_cderiv_le (show 0 < c / 4 by positivity)
    (fun v hv => hval v (hdisk (sphere_subset_closedBall hv)))
  rw [hderiv] at hb
  have hd := ((hphase w hwU).2.2.2.1.differentiableAt.hasDerivAt.sub
    (analyticOnNhd_eta w (sector_re_pos (by norm_num) hwU)).differentiableAt.hasDerivAt).deriv
  rw [show deriv e w = deriv (polePhase m) w - deriv eta w from hd] at hb
  convert hb using 1
  ring

private theorem affine_error_lipschitz {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {a : ℂ} {A : ℝ} (hf : ∀ w ∈ s, AnalyticAt ℂ f w)
    (hd : ∀ w ∈ s, ‖deriv f w - a‖ ≤ A) {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖(f y - f x) - a * (y - x)‖ ≤ A * ‖y - x‖ := by
  have hderiv (w : ℂ) (hw : w ∈ s) :
      HasDerivAt (fun z => f z - a * z) (deriv f w - a) w :=
    (hf w hw).differentiableAt.hasDerivAt.sub (by
      simpa using (hasDerivAt_id w).const_mul a)
  have hb := hs.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hderiv w hw).differentiableAt)
    (fun w hw => (hderiv w hw).deriv ▸ hd w hw) hx hy
  convert hb using 2
  ring

private theorem affine_lower {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {a : ℝ} (ha : 0 < a) (hf : ∀ w ∈ s, AnalyticAt ℂ f w)
    (hd : ∀ w ∈ s, ‖deriv f w - (a : ℂ)‖ ≤ a / 2)
    {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    a / 2 * ‖y - x‖ ≤ ‖f y - f x‖ := by
  have h := affine_error_lipschitz hs hf hd hx hy
  have htri := norm_sub_le (f y - f x) ((f y - f x) - (a : ℂ) * (y - x))
  rw [sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le] at htri
  linarith

private theorem analytic_inverse_on_disk {f : ℂ → ℂ} {c : ℂ} {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hf : ∀ w ∈ closedBall c r, AnalyticAt ℂ f w)
    (hd : ∀ w ∈ closedBall c r, ‖deriv f w - (a : ℂ)‖ ≤ a / 2)
    (hc : ‖f c‖ ≤ a * r / 8) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 (a * r / 8)) ∧
      ∀ z ∈ ball 0 (a * r / 8), g z ∈ ball c r ∧ f (g z) = z ∧
        ∀ w ∈ closedBall c r, f w = z → w = g z := by
  let V := closedBall c r
  let U := ball (0 : ℂ) (a * r / 8)
  have hcV : c ∈ V := mem_closedBall_self hr.le
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hinj : InjOn f V := by
    intro x hx y hy he
    have h := affine_lower (convex_closedBall c r) ha hf hd hx hy
    rw [he, sub_self, norm_zero] at h
    have hzero : ‖y - x‖ ≤ 0 := nonpos_of_mul_nonpos_right h (by positivity)
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp hzero)).symm
  have hex (z : ℂ) (hz : z ∈ U) : ∃ w ∈ ball c r, f w = z := by
    let T (w : ℂ) := w - (f w - z) / (a : ℂ)
    have hlip (x : ℂ) (hx : x ∈ V) (y : ℂ) (hy : y ∈ V) :
        ‖T y - T x‖ ≤ 1 / 2 * ‖y - x‖ := by
      have h := affine_error_lipschitz (convex_closedBall c r) hf hd hx hy
      rw [show T y - T x = -((f y - f x) - (a : ℂ) * (y - x)) / (a : ℂ) by
        dsimp only [T]
        field_simp
        ring, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha.le]
      apply (div_le_iff₀ ha).2
      convert h using 1
      ring
    have hcenter : ‖T c - c‖ ≤ r / 4 := by
      have hz' : ‖z‖ < a * r / 8 := by simpa [U, mem_ball_iff_norm] using hz
      rw [show T c - c = -((f c - z) / (a : ℂ)) by dsimp only [T]; ring,
        norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_le_iff₀ ha]
      have hh := norm_sub_le (f c) z
      linarith
    have hmaps (w : ℂ) (hw : w ∈ V) : T w ∈ ball c r := by
      apply mem_ball_iff_norm.mpr
      have ht := norm_sub_le (T w - T c) (c - T c)
      rw [norm_sub_rev c (T c), show T w - T c - (c - T c) = T w - c by ring] at ht
      have hw' : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
      have hw'' := hlip c hcV w hw
      linarith
    have htV : MapsTo T V V := fun w hw => ball_subset_closedBall (hmaps w hw)
    have hcon : ContractingWith (1 / 2 : NNReal) (htV.restrict T V V) := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      change dist (T x.val) (T y.val) ≤ ((1 / 2 : NNReal) : ℝ) * dist x.val y.val
      simpa [dist_eq_norm] using hlip y y.property x x.property
    obtain ⟨w, hw, hfix, _, _⟩ :=
      hcon.exists_fixedPoint' isClosed_closedBall.isComplete htV hcV (edist_ne_top c (T c))
    have hfix' : T w = w := hfix
    refine ⟨w, hfix' ▸ hmaps w hw, ?_⟩
    have hzero : (f w - z) / (a : ℂ) = 0 := by
      dsimp only [T] at hfix'
      linear_combination -hfix'
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right ha0)
  classical
  let g (z : ℂ) := if h : z ∈ U then (hex z h).choose else c
  have hg (z : ℂ) (hz : z ∈ U) : g z ∈ ball c r ∧ f (g z) = z := by
    simpa only [g, dite_eq_left hz] using (hex z hz).choose_spec
  refine ⟨g, ?_, fun z hz => ⟨(hg z hz).1, (hg z hz).2, ?_⟩⟩
  · intro z hz
    have hgV := ball_subset_closedBall (hg z hz).1
    have hroot := (hg z hz).2
    have hD : deriv f (g z) ≠ 0 := by
      intro hzero
      have hb := hd (g z) hgV
      rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha.le] at hb
      linarith
    have hcomp : AnalyticAt ℂ (g ∘ f) (g z) := by
      have hu : ∀ᶠ w in 𝓝 (g z), f w ∈ U :=
        (hf (g z) hgV).continuousAt ((isOpen_ball).mem_nhds (hroot.symm ▸ hz))
      have hv : ∀ᶠ w in 𝓝 (g z), w ∈ ball c r :=
        isOpen_ball.mem_nhds (hg z hz).1
      have heq : (g ∘ f) =ᶠ[𝓝 (g z)] id := by
        filter_upwards [hu, hv] with w hwu hwv
        exact hinj (ball_subset_closedBall (hg (f w) hwu).1)
          (ball_subset_closedBall hwv) (hg (f w) hwu).2
      exact (analyticAt_congr heq).mpr analyticAt_id
    have hfg := (analyticAt_comp_iff_of_deriv_ne_zero (hf (g z) hgV) hD).mp hcomp
    rwa [hroot] at hfg
  · intro w hw hroot
    exact hinj hw (ball_subset_closedBall (hg z hz).1) (hroot.trans (hg z hz).2.symm)

/-- One fixed inverse disk works for the limiting phase and every sufficiently large order.
The corrected inverse converges uniformly at inverse-square rate. -/
theorem exists_uniform_polePhase_inverse {c : ℝ} (hc : 0 < c) (hzero : eta (c : ℂ) = 0) :
    ∃ r ρ B : ℝ, 0 < r ∧ r ≤ c / 4 ∧ 0 < ρ ∧ 0 < B ∧
      ∃ M : ℕ, 160 * sectorMass (1 / 4) ≤ order M ∧
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 ρ) ∧
        (∀ z ∈ ball 0 ρ, g z ∈ ball (c : ℂ) r ∧ eta (g z) = z ∧
          ∀ w ∈ closedBall (c : ℂ) r, eta w = z → w = g z) ∧
        ∀ m ≥ M, ∃ gm : ℂ → ℂ, AnalyticOnNhd ℂ gm (ball 0 ρ) ∧
          ∀ z ∈ ball 0 ρ, gm z ∈ ball (c : ℂ) r ∧ polePhase m (gm z) = z ∧
            (∀ w ∈ closedBall (c : ℂ) r, polePhase m w = z → w = gm z) ∧
            ‖gm z - g z‖ ≤ B / order m ^ 2 := by
  let a := Real.sqrt (1 + c ^ 2) / c
  let V := sectorMass (1 / 4)
  have ha : 0 < a := by dsimp [a]; positivity
  have hV : 0 < V := by dsimp [V, sectorMass]; positivity
  have hη (w : ℂ) (hw : w ∈ closedBall (c : ℂ) (c / 2)) : AnalyticAt ℂ eta w :=
    analyticOnNhd_eta w (sector_re_pos (by norm_num) (closedBall_subset_sector hc hw))
  have hcη := hη (c : ℂ) (mem_closedBall_self (by positivity))
  have hc' : deriv eta (c : ℂ) = (a : ℂ) := by
    simpa [a, S_ofReal] using (hasDerivAt_eta (w := (c : ℂ)) (by simpa using hc)).deriv
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp
    (hcη.deriv.continuousAt (ball_mem_nhds (deriv eta (c : ℂ)) (show 0 < a / 4 by positivity)))
  let r := min (c / 4) (δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrle : r ≤ c / 4 := min_le_left _ _
  have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
  let ρ := a * r / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : closedBall (c : ℂ) r ⊆ closedBall (c : ℂ) (c / 2) :=
    closedBall_subset_closedBall (by linarith)
  have hderiv (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) : ‖deriv eta w - (a : ℂ)‖ ≤ a / 4 := by
    have ht := hsmall (closedBall_subset_ball hrδ hw)
    rw [Set.mem_preimage, hc', mem_ball_iff_norm] at ht
    exact ht.le
  have hderiv' (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) :
      ‖deriv eta w - (a : ℂ)‖ ≤ a / 2 := (hderiv w hw).trans (by linarith)
  obtain ⟨g, hgA, hg⟩ := analytic_inverse_on_disk hr ha (fun w hw => hη w (hclosed hw))
    hderiv' (by simpa [hzero] using hρ.le)
  let B := 120 * V / a
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max (max 1 (160 * V)) (max (60 * V / ρ) (240 * V / (c * (a / 4)))))
  have hbound (x : ℝ) (hx :
      x ∈ ({1, 160 * V, 60 * V / ρ, 240 * V / (c * (a / 4))} : Set ℝ)) :
      x ≤ (M : ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · exact (h.trans_le ((le_max_left _ _).trans (le_max_left _ _))).trans hM.le
    · exact (h.trans_le ((le_max_right _ _).trans (le_max_left _ _))).trans hM.le
    · exact (h.trans_le ((le_max_left _ _).trans (le_max_right _ _))).trans hM.le
    · exact (h.trans_le ((le_max_right _ _).trans (le_max_right _ _))).trans hM.le
  have horder (m : ℕ) (hm : M ≤ m) : (M : ℝ) ≤ order m := by
    have := Nat.cast_le (α := ℝ).mpr hm
    rw [order]
    linarith
  have hthreshold (m : ℕ) (hm : M ≤ m) : 160 * V ≤ order m :=
    (hbound _ (by simp)).trans (horder m hm)
  refine ⟨r, ρ, B, hr, hrle, hρ, hB, M, hthreshold M le_rfl, g, hgA, hg, ?_⟩
  intro m hm
  have hs := hthreshold m hm
  have hsector : 40 * V / (1 / 4) ≤ order m := by convert hs using 1; ring
  have hpert := polePhase_compact_estimate m hc hs
  have hν := order_pos m
  have hν₁ : 1 ≤ order m := (hbound _ (by simp)).trans (horder m hm)
  have hν₂ : order m ≤ order m ^ 2 := by nlinarith
  have hsmall₁ : 60 * V / order m ^ 2 ≤ ρ := by
    rw [div_le_iff₀ (by positivity)]
    exact mul_comm (order m ^ 2) ρ ▸ (div_le_iff₀ hρ).mp
      (((hbound (60 * V / ρ) (by simp)).trans (horder m hm)).trans hν₂)
  have hsmall₂ : 240 * V / (c * order m ^ 2) ≤ a / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hb := (div_le_iff₀ (show 0 < c * (a / 4) by positivity)).mp
      (((hbound (240 * V / (c * (a / 4))) (by simp)).trans (horder m hm)).trans hν₂)
    convert hb using 1
    ring
  have hA (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) : AnalyticAt ℂ (polePhase m) w :=
    (polePhase_sector m (by norm_num) (by norm_num) hsector
      (closedBall_subset_sector hc (hclosed hw))).2.2.2.1
  have hD (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) :
      ‖deriv (polePhase m) w - (a : ℂ)‖ ≤ a / 2 := by
    have hb := (hpert.2 w (closedBall_subset_closedBall hrle hw)).trans hsmall₂
    have ht := norm_add_le (deriv (polePhase m) w - deriv eta w) (deriv eta w - (a : ℂ))
    rw [sub_add_sub_cancel] at ht
    linarith [hderiv w hw]
  have hcenter : ‖polePhase m (c : ℂ)‖ ≤ ρ := by
    have hb := (hpert.1 (c : ℂ) (mem_closedBall_self (by positivity))).trans hsmall₁
    simpa [hzero] using hb
  obtain ⟨gm, hgmA, hgm⟩ := analytic_inverse_on_disk hr ha hA hD hcenter
  refine ⟨gm, hgmA, fun z hz => ⟨(hgm z hz).1, (hgm z hz).2.1, (hgm z hz).2.2, ?_⟩⟩
  have hgz := ball_subset_closedBall (hg z hz).1
  have hgmz := ball_subset_closedBall (hgm z hz).1
  have hl := affine_lower (convex_closedBall (c : ℂ) r) ha
    (fun w hw => hη w (hclosed hw)) hderiv' hgz hgmz
  have hb : a / 2 * ‖gm z - g z‖ ≤ 60 * V / order m ^ 2 := calc
    _ ≤ ‖eta (gm z) - eta (g z)‖ := hl
    _ = ‖polePhase m (gm z) - eta (gm z)‖ := by
      rw [norm_sub_rev (eta (gm z)), (hg z hz).2.1, (hgm z hz).2.1]
    _ ≤ _ := hpert.1 _ (hclosed hgmz)
  apply (le_div_iff₀ (by positivity : 0 < order m ^ 2)).2
  have hh := (le_div_iff₀ (by positivity : 0 < order m ^ 2)).mp hb
  dsimp [B]
  apply (le_div_iff₀ ha).2
  linarith only [hh, show (‖gm z - g z‖ * order m ^ 2) * a =
    2 * (a / 2 * ‖gm z - g z‖ * order m ^ 2) by ring]

open ComplexConjugate

private theorem conj_two : conj (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2

private theorem slitPlane_arg_ne_pi_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    w.arg ≠ Real.pi :=
  Complex.slitPlane_arg_ne_pi (Complex.mem_slitPlane_iff.mpr (Or.inl hw))

private theorem sqrt_conj {w : ℂ} (hw : w.arg ≠ Real.pi) :
    Complex.sqrt (conj w) = conj (Complex.sqrt w) := by
  simpa [Complex.sqrt, conj_two] using
    Complex.conj_cpow w (2⁻¹ : ℂ) hw

private theorem eta_conj {w : ℂ} (hw : 0 < w.re) :
    eta (conj w) = conj (eta w) := by
  have hs : S (conj w) = conj (S w) := by
    rw [S, S, show 1 + conj w ^ 2 = conj (1 + w ^ 2) by simp]
    exact sqrt_conj (Complex.slitPlane_arg_ne_pi
      (HalfIntegerBessel.one_add_sq_mem_slitPlane hw))
  have hsum : 0 < (1 + S w).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [S_re_pos hw]
  rw [eta, eta, hs, Complex.log_conj w (slitPlane_arg_ne_pi_of_re_pos hw),
    show 1 + conj (S w) = conj (1 + S w) by simp,
    Complex.log_conj _ (slitPlane_arg_ne_pi_of_re_pos hsum)]
  simp

private theorem carrier_aeval_conj (p : Polynomial ℚ) (w : ℂ) :
    aeval (conj w) p = conj (aeval w p) :=
  Polynomial.aeval_algHom_apply (Complex.conjAe.restrictScalars ℚ) w p

private theorem bessel_conj (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    K m (conj z) = conj (K m z) ∧ I m (conj z) = conj (I m z) := by
  have hp : HalfIntegerBessel.prefactor (conj z) = conj (HalfIntegerBessel.prefactor z) := by
    rw [HalfIntegerBessel.prefactor, HalfIntegerBessel.prefactor,
      sqrt_conj (slitPlane_arg_ne_pi_of_re_pos hz)]
    simp
  have hK : K m (conj z) = conj (K m z) := by
    rw [K, K, hp, ← map_neg, Complex.exp_conj, ← map_inv₀, carrier_aeval_conj]
    simp
  have hL : HalfIntegerBessel.L m (conj z) = conj (HalfIntegerBessel.L m z) := by
    rw [HalfIntegerBessel.L, HalfIntegerBessel.L, hp, Complex.exp_conj, ← map_inv₀,
      carrier_aeval_conj]
    simp
  refine ⟨hK, ?_⟩
  rw [I, I, hK, hL]
  simp

private theorem polePhase_conj (m : ℕ) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hm : 40 * sectorMass κ / κ ≤ order m) {w : ℂ} (hw : κ * ‖w‖ < w.re) :
    polePhase m (conj w) = conj (polePhase m w) := by
  have hcw : κ * ‖conj w‖ < (conj w).re := by simpa [Complex.norm_conj] using hw
  have hre := sector_re_pos hκ hw
  have hratio (v : ℂ) (hv : κ * ‖v‖ < v.re) :=
    F_I_div_F_K m (sector_re_pos hκ hv) (sector_K_nonzero hκ hκ' hm hv).2
  have harg : (order m : ℂ) * conj w = conj ((order m : ℂ) * w) := by simp
  obtain ⟨hK, hI⟩ := bessel_conj m (scale_re_pos (m := m) hre)
  have hA : F_I m (conj w) / F_K m (conj w) = conj (F_I m w / F_K m w) := by
    rw [hratio _ hcw, hratio _ hw, harg, hK, hI, eta_conj hre]
    simp only [map_mul, map_div₀, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp [conj_two]
  have hAre := (polePhase_sector m hκ hκ' hm hw).2.2.1
  rw [polePhase, polePhase, eta_conj hre, hA,
    Complex.log_conj _ (slitPlane_arg_ne_pi_of_re_pos hAre)]
  simp [conj_two]

/-- The lattice modulus is the absolute index times the phase spacing. -/
theorem norm_polePhaseLattice (m : ℕ) (j : ℤ) :
    ‖polePhaseLattice m j‖ = |(j : ℝ)| * Real.pi / order m := by
  simp [polePhaseLattice, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (order_pos m)]

private theorem polePhaseLattice_injective (m : ℕ) : Function.Injective (polePhaseLattice m) := by
  intro i j hij
  have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [polePhaseLattice, polePhaseLattice, div_left_inj' hν, mul_left_inj' Complex.I_ne_zero,
    mul_left_inj' hπ] at hij
  exact_mod_cast hij

private theorem eventually_fixed_indices_in_cutoff {t : ℝ} (ht : 0 < t) (J : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ j : ℤ, |(j : ℝ)| ≤ J → ‖polePhaseLattice m j‖ ≤ t := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((J : ℝ) * Real.pi / t)
  refine ⟨M, ?_⟩
  intro m hm j hj
  have hm' : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hMo : (M : ℝ) ≤ order m := by rw [order]; linarith
  have hbound := (div_le_iff₀ ht).mp (hM.le.trans hMo)
  rw [norm_polePhaseLattice, div_le_iff₀ (order_pos m), mul_comm t]
  exact (mul_le_mul_of_nonneg_right hj Real.pi_pos.le).trans hbound

private theorem closedBall_conj {c r : ℝ} {w : ℂ} (hw : w ∈ closedBall (c : ℂ) r) :
    conj w ∈ closedBall (c : ℂ) r := by
  rw [mem_closedBall_iff_norm] at hw ⊢
  simpa only [map_sub, Complex.conj_ofReal, Complex.norm_conj] using
    (show ‖conj (w - (c : ℂ))‖ ≤ r by simpa only [Complex.norm_conj] using hw)

private theorem ball_zero_conj {r : ℝ} {z : ℂ} (hz : z ∈ ball 0 r) :
    conj z ∈ ball 0 r := by
  simpa [mem_ball_iff_norm, Complex.norm_conj] using hz

private theorem re_ge_half_on_disk {c r : ℝ} (hc : 0 < c) (hrc : r ≤ c / 4)
    {w : ℂ} (hw : w ∈ closedBall (c : ℂ) r) : c / 2 ≤ w.re := by
  have h := Complex.re_le_norm ((c : ℂ) - w)
  rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at h
  linarith [mem_closedBall_iff_norm.mp hw]

private theorem log_close_on_disk {c r : ℝ} (hc : 0 < c) (hrc : r ≤ c / 4)
    {x y : ℂ} (hx : x ∈ closedBall (c : ℂ) r) (hy : y ∈ closedBall (c : ℂ) r) :
    ‖Complex.log y - Complex.log x‖ ≤ (2 / c) * ‖y - x‖ := by
  have hlog (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) : HasDerivAt Complex.log w⁻¹ w :=
    Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr
      (Or.inl ((show 0 < c / 2 by positivity).trans_le (re_ge_half_on_disk hc hrc hw))))
  apply (convex_closedBall (c : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hlog w hw).differentiableAt) _ hx hy
  intro w hw
  rw [(hlog w hw).deriv, norm_inv, ← one_div]
  have hp : c / 2 ≤ ‖w‖ := (re_ge_half_on_disk hc hrc hw).trans (Complex.re_le_norm _)
  convert one_div_le_one_div_of_le (by positivity : 0 < c / 2) hp using 1
  ring

private theorem log_inverse_analytic {g : ℂ → ℂ} {c r ρ : ℝ} (hc : 0 < c) (hrc : r ≤ c / 4)
    (hA : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg : MapsTo g (ball 0 ρ) (ball (c : ℂ) r)) :
    AnalyticOnNhd ℂ (fun z => Complex.log (g z)) (ball 0 ρ) := by
  intro z hz
  have hre : 0 < (g z).re := (show 0 < c / 2 by positivity).trans_le
    (re_ge_half_on_disk hc hrc (ball_subset_closedBall (hg hz)))
  exact (hA z hz).clog (Complex.mem_slitPlane_iff.mpr (Or.inl hre))

private theorem eta_inverse_derivatives {g : ℂ → ℂ} {c r ρ : ℝ}
    (hc : 0 < c) (hrc : r ≤ c / 4) (hρ : 0 < ρ) (hgc : g 0 = (c : ℂ))
    (hA : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg : MapsTo g (ball 0 ρ) (ball (c : ℂ) r))
    (hinv : RightInvOn g eta (ball 0 ρ)) :
    deriv g 0 = ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) ∧
      deriv (fun z => Complex.log (g z)) 0 = ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) ∧
      deriv (deriv (fun z => Complex.log (g z))) 0 =
        ((-(c ^ 2 / (1 + c ^ 2) ^ 2) : ℝ) : ℂ) := by
  have hre (z : ℂ) (hz : z ∈ ball 0 ρ) : 0 < (g z).re :=
    (show 0 < c / 2 by positivity).trans_le
      (re_ge_half_on_disk hc hrc (ball_subset_closedBall (hg hz)))
  have hS0 (z : ℂ) (hz : z ∈ ball 0 ρ) : S (g z) ≠ 0 := by
    intro h
    have hp := S_re_pos (hre z hz)
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hd (z : ℂ) (hz : z ∈ ball 0 ρ) :
      HasDerivAt g (g z / S (g z)) z := by
    have hderiv := (hA z hz).differentiableAt.hasDerivAt
    have hcomp := (hasDerivAt_eta (hre z hz)).comp z hderiv
    have heq : (eta ∘ g) =ᶠ[𝓝 z] id :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun _ hu => hinv hu
    have hd' := (hcomp.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
    have hg0 : g z ≠ 0 := by
      intro he
      have hp := hre z hz
      rw [he, Complex.zero_re] at hp
      exact lt_irrefl _ hp
    refine hderiv.congr_deriv ?_
    field_simp [hS0 z hz]
    calc
      deriv g z * S (g z) = (S (g z) / g z * deriv g z) * g z := by
        field_simp [hg0]
      _ = _ := by rw [hd', one_mul]
  have hlog (z : ℂ) (hz : z ∈ ball 0 ρ) :
      HasDerivAt (fun s => Complex.log (g s)) (S (g z))⁻¹ z := by
    have hg0 := Complex.slitPlane_ne_zero
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hre z hz)))
    refine ((Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (hre z hz)))).comp
      z (hd z hz)).congr_deriv ?_
    change (g z)⁻¹ * (g z / S (g z)) = _
    field_simp [hg0]
  have hz : (0 : ℂ) ∈ ball 0 ρ := mem_ball_self hρ
  refine ⟨?_, ?_, ?_⟩
  · simpa [hgc, S_ofReal] using (hd 0 hz).deriv
  · simpa [hgc, S_ofReal, one_div] using (hlog 0 hz).deriv
  have hD := ((HalfIntegerBessel.hasDerivAt_S (hre 0 hz)).comp 0 (hd 0 hz)).inv (hS0 0 hz)
  have heq : (fun z => (S (g z))⁻¹) =ᶠ[𝓝 0] deriv (fun z => Complex.log (g z)) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun z h => (hlog z h).deriv.symm
  rw [(hD.congr_of_eventuallyEq heq.symm).deriv]
  simp only [Function.comp_apply, hgc, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_one]
  have hs : S (c : ℂ) ^ 2 = 1 + (c : ℂ) ^ 2 := HalfIntegerBessel.S_sq _
  rw [← hs]
  field_simp [hgc ▸ hS0 0 hz]

private theorem cauchy_deriv_on_half_disk {f : ℂ → ℂ} {ρ R B : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hf : AnalyticOnNhd ℂ f (ball 0 ρ))
    (hb : ∀ w ∈ closedBall 0 R, ‖f w‖ ≤ B) {z : ℂ} (hz : z ∈ closedBall 0 (R / 2)) :
    ‖deriv f z‖ ≤ B / (R / 2) := by
  have hsubset : closedBall z (R / 2) ⊆ closedBall 0 R := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.mp hz
    linarith
  rw [← Complex.cderiv_eq_deriv isOpen_ball hf.differentiableOn (by positivity)
    (hsubset.trans (closedBall_subset_ball hRρ))]
  exact Complex.norm_cderiv_le (by positivity) (fun w hw => hb w (hsubset (sphere_subset_closedBall hw)))

private theorem real_imaginary_line_deriv {F : ℂ → ℂ} {t : ℝ} {d : ℂ}
    (h : HasDerivAt F d ((t : ℂ) * Complex.I)) :
    HasDerivAt (fun v : ℝ => (F ((v : ℂ) * Complex.I)).re) ((d * Complex.I).re) t := by
  have hline := (hasDerivAt_id (t : ℂ)).mul_const Complex.I
  have hl := (h.comp (t : ℂ) hline).comp_ofReal
  simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hl

private theorem uniform_log_curvature {g : ℂ → ℂ} {c r ρ : ℝ}
    (hc : 0 < c) (hrc : r ≤ c / 4) (hρ : 0 < ρ) (hgc : g 0 = (c : ℂ))
    (hA : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg : MapsTo g (ball 0 ρ) (ball (c : ℂ) r))
    (hinv : RightInvOn g eta (ball 0 ρ)) :
    ∃ t₀ ε : ℝ, 0 < t₀ ∧ t₀ ≤ ρ / 4 ∧ 0 < ε ∧
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (ball 0 ρ) →
        MapsTo f (ball 0 ρ) (ball (c : ℂ) r) →
        (∀ z ∈ ball 0 ρ, f (conj z) = conj (f z)) →
        (∀ z ∈ ball 0 ρ, ‖f z - g z‖ ≤ ε) →
        ∀ t : ℝ, |t| ≤ t₀ →
          c ^ 2 / (4 * (1 + c ^ 2) ^ 2) * t ^ 2 ≤
            (Complex.log (f ((t : ℂ) * Complex.I)) - Complex.log (f 0)).re := by
  let Q := c ^ 2 / (1 + c ^ 2) ^ 2
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let G : ℂ → ℂ := fun z => Complex.log (g z)
  have hGA : AnalyticOnNhd ℂ G (ball 0 ρ) := log_inverse_analytic hc hrc hA hg
  have hG2 : deriv (deriv G) 0 = ((-Q : ℝ) : ℂ) :=
    (eta_inverse_derivatives hc hrc hρ hgc hA hg hinv).2.2
  have hGA2 := hGA.deriv.deriv 0 (mem_ball_self hρ)
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhds_iff.mp
    (hGA2.continuousAt (ball_mem_nhds (deriv (deriv G) 0) (show 0 < Q / 4 by positivity)))
  let t₀ := min (ρ / 16) (δ / 2)
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by positivity)
  have ht₀ρ : t₀ < ρ / 8 := (min_le_left _ _).trans_lt (by linarith)
  have ht₀δ : t₀ < δ := (min_le_right _ _).trans_lt (by linarith)
  let ε := (Q / 4) * (ρ / 8) * (ρ / 4) / (2 / c)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨t₀, ε, ht₀, ht₀ρ.le.trans (by linarith), hε, ?_⟩
  intro f hfA hf hs he
  let F : ℂ → ℂ := fun z => Complex.log (f z)
  let E : ℂ → ℂ := fun z => F z - G z
  have hFA : AnalyticOnNhd ℂ F (ball 0 ρ) := log_inverse_analytic hc hrc hfA hf
  have hEA : AnalyticOnNhd ℂ E (ball 0 ρ) := fun z hz => (hFA z hz).sub (hGA z hz)
  have he₀ (z : ℂ) (hz : z ∈ closedBall 0 (ρ / 2)) : ‖E z‖ ≤ (2 / c) * ε := by
    have hz' : z ∈ ball 0 ρ := closedBall_subset_ball (by linarith) hz
    exact (log_close_on_disk hc hrc (ball_subset_closedBall (hg hz'))
      (ball_subset_closedBall (hf hz'))).trans
        (mul_le_mul_of_nonneg_left (he z hz') (by positivity))
  have he₁ (z : ℂ) (hz : z ∈ closedBall 0 (ρ / 4)) :
      ‖deriv E z‖ ≤ ((2 / c) * ε) / (ρ / 4) := by
    have hh := cauchy_deriv_on_half_disk (R := ρ / 2) (by positivity) (by linarith) hEA he₀
      (z := z) (by rwa [show ρ / 2 / 2 = ρ / 4 by ring])
    simpa only [show ρ / 2 / 2 = ρ / 4 by ring] using hh
  have he₂ (z : ℂ) (hz : z ∈ closedBall 0 (ρ / 8)) :
      ‖deriv (deriv E) z‖ ≤ Q / 4 := by
    have hh := cauchy_deriv_on_half_disk (R := ρ / 4) (by positivity) (by linarith) hEA.deriv he₁
      (z := z) (by rwa [show ρ / 4 / 2 = ρ / 8 by ring])
    refine hh.trans_eq ?_
    dsimp [ε]
    field_simp
    ring
  have hE₂ (z : ℂ) (hz : z ∈ closedBall 0 (ρ / 8)) :
      ‖deriv (deriv F) z - deriv (deriv G) z‖ ≤ Q / 4 := by
    have hz' := closedBall_subset_ball (show ρ / 8 < ρ by linarith) hz
    have hEq : deriv E =ᶠ[𝓝 z] (fun w => deriv F w - deriv G w) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz') fun w hw =>
        ((hFA w hw).differentiableAt.hasDerivAt.sub (hGA w hw).differentiableAt.hasDerivAt).deriv
    have hd := (hFA.deriv z hz').differentiableAt.hasDerivAt.sub
      (hGA.deriv z hz').differentiableAt.hasDerivAt
    rw [← (hd.congr_of_eventuallyEq hEq).deriv]
    exact he₂ z hz
  let W := Icc (-t₀) t₀
  let line (t : ℝ) : ℂ := (t : ℂ) * Complex.I
  have hlineNorm (t : ℝ) : ‖line t‖ = |t| := by simp [line, Real.norm_eq_abs]
  have hline (t : ℝ) (ht : t ∈ W) : line t ∈ closedBall 0 (ρ / 8) := by
    rw [mem_closedBall_iff_norm, sub_zero, hlineNorm]
    exact (abs_le.mpr ht).trans ht₀ρ.le
  have hline' (t : ℝ) (ht : t ∈ W) : line t ∈ ball 0 ρ :=
    closedBall_subset_ball (by linarith) (hline t ht)
  have hupper (t : ℝ) (ht : t ∈ W) : (deriv (deriv F) (line t)).re ≤ -(Q / 2) := by
    have htδ : line t ∈ ball 0 δ := by
      rw [mem_ball_iff_norm, sub_zero, hlineNorm]
      exact (abs_le.mpr ht).trans_lt ht₀δ
    have hb := hnear htδ
    rw [Set.mem_preimage, hG2, mem_ball_iff_norm] at hb
    have hg' := (Complex.re_le_norm _).trans hb.le
    have hf' := (Complex.re_le_norm _).trans (hE₂ (line t) (hline t ht))
    rw [Complex.sub_re, Complex.ofReal_re] at hg'
    rw [Complex.sub_re] at hf'
    linarith
  let q (t : ℝ) := (F (line t)).re - (Q / 4) * t ^ 2
  let q' (t : ℝ) := (deriv F (line t) * Complex.I).re - (Q / 2) * t
  have hq (t : ℝ) (ht : t ∈ W) : HasDerivAt q (q' t) t := by
    have hd := real_imaginary_line_deriv (hFA (line t) (hline' t ht)).differentiableAt.hasDerivAt
    refine (hd.sub (((hasDerivAt_id t).pow 2).const_mul (Q / 4))).congr_deriv ?_
    simp only [q', line, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one, id_eq]
    ring
  have hq' (t : ℝ) (ht : t ∈ W) :
      HasDerivAt q' (-(deriv (deriv F) (line t)).re - Q / 2) t := by
    have h := ((hFA.deriv (line t) (hline' t ht)).differentiableAt.hasDerivAt).mul_const Complex.I
    have hd := real_imaginary_line_deriv h
    refine (hd.sub ((hasDerivAt_id t).const_mul (Q / 2))).congr_deriv ?_
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one, Complex.neg_re, mul_one]
  have hv : ConvexOn ℝ W q :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hq' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => by linarith [hupper t (interior_subset ht)])
  intro t ht
  have htW : t ∈ W := abs_le.mp ht
  have htW' : -t ∈ W := abs_le.mp (by simpa using ht)
  have hsym : q (-t) = q t := by
    have hl : line (-t) = conj (line t) := by simp [line, mul_neg, neg_mul]
    have hfre : 0 < (f (line t)).re := (show 0 < c / 2 by positivity).trans_le
      (re_ge_half_on_disk hc hrc (ball_subset_closedBall (hf (hline' t htW))))
    dsimp only [q, F]
    rw [hl, hs (line t) (hline' t htW), Complex.log_conj _ (slitPlane_arg_ne_pi_of_re_pos hfre),
      Complex.conj_re, neg_sq]
  have hJ := hv.2 htW htW' (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  change q ((1 / 2 : ℝ) * t + 1 / 2 * -t) ≤ 1 / 2 * q t + 1 / 2 * q (-t) at hJ
  rw [show (1 / 2 : ℝ) * t + 1 / 2 * -t = 0 by ring, hsym] at hJ
  have hb : q 0 ≤ q t := by linarith only [hJ]
  have hconst : c ^ 2 / (4 * (1 + c ^ 2) ^ 2) = Q / 4 := by
    dsimp [Q]
    field_simp
  rw [hconst, Complex.sub_re]
  dsimp only [q, F, line] at hb
  simp at hb
  linarith

private theorem first_order_error {f : ℂ → ℂ} {R C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hD : ∀ w ∈ closedBall 0 R, ‖deriv (deriv f) w‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖f z - f 0 - deriv f 0 * z‖ ≤ C * ‖z‖ ^ 2 := by
  let V : Set ℂ := closedBall 0 ‖z‖
  have hV : V ⊆ closedBall 0 R := by
    apply closedBall_subset_closedBall
    simpa only [mem_closedBall_iff_norm, sub_zero] using hz
  have h0 : (0 : ℂ) ∈ V := mem_closedBall_self (norm_nonneg _)
  have hzV : z ∈ V := by simp [V]
  let E (w : ℂ) := f w - f 0 - deriv f 0 * w
  have hE (w : ℂ) (hw : w ∈ V) : HasDerivAt E (deriv f w - deriv f 0) w :=
    ((hf w (hV hw)).differentiableAt.hasDerivAt.sub_const _).sub
      (by simpa using (hasDerivAt_id w).const_mul (deriv f 0))
  have hb (w : ℂ) (hw : w ∈ V) : ‖deriv E w‖ ≤ C * ‖z‖ := by
    have hd := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hf x (hV hx)).deriv.differentiableAt) (fun x hx => hD x (hV hx)) h0 hw
    rw [(hE w hw).deriv, sub_zero] at *
    exact hd.trans (mul_le_mul_of_nonneg_left (by simpa [V, mem_closedBall_iff_norm] using hw) hC)
  have hb' := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hE w hw).differentiableAt) hb h0 hzV
  simpa [E, pow_two, mul_assoc] using hb'

private theorem second_order_error {f : ℂ → ℂ} {R C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hD : ∀ w ∈ closedBall 0 R, ‖deriv (deriv (deriv f)) w‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖f z - f 0 - (deriv f 0 * z + deriv (deriv f) 0 / 2 * z ^ 2)‖ ≤ C * ‖z‖ ^ 3 := by
  let V : Set ℂ := closedBall 0 ‖z‖
  have hV : V ⊆ closedBall 0 R := by
    apply closedBall_subset_closedBall
    simpa only [mem_closedBall_iff_norm, sub_zero] using hz
  have h0 : (0 : ℂ) ∈ V := mem_closedBall_self (norm_nonneg _)
  have hzV : z ∈ V := by simp [V]
  let E (w : ℂ) := f w - f 0 - (deriv f 0 * w + deriv (deriv f) 0 / 2 * w ^ 2)
  have hE (w : ℂ) (hw : w ∈ V) :
      HasDerivAt E (deriv f w - deriv f 0 - deriv (deriv f) 0 * w) w := by
    refine (((hf w (hV hw)).differentiableAt.hasDerivAt.sub_const _).sub
      (((hasDerivAt_id w).const_mul (deriv f 0)).add
        (((hasDerivAt_id w).pow 2).const_mul (deriv (deriv f) 0 / 2)))).congr_deriv ?_
    simp only [mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
    ring
  have hb (w : ℂ) (hw : w ∈ V) : ‖deriv E w‖ ≤ C * ‖z‖ ^ 2 := by
    rw [(hE w hw).deriv]
    exact (first_order_error hC hf.deriv hD (hV hw)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (by simpa [V, mem_closedBall_iff_norm] using hw) 2)
        hC)
  have hb' := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hE w hw).differentiableAt) hb h0 hzV
  simpa [E, pow_succ, mul_assoc] using hb'

private theorem analytic_norm_bound {f : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    ∃ C > 0, ∀ w ∈ closedBall 0 R, ‖f w‖ ≤ C := by
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    ⟨0, mem_closedBall_self hR⟩ hf.continuousOn.norm
  exact ⟨‖f z‖ + 1, by positivity, fun w hw => (hz hw).trans (by linarith)⟩

private theorem centered_error_on_quarter_disk {f g : ℂ → ℂ} {ρ A : ℝ}
    (hρ : 0 < ρ) (hf : AnalyticOnNhd ℂ f (ball 0 ρ)) (hg : AnalyticOnNhd ℂ g (ball 0 ρ))
    (hA : ∀ w ∈ ball 0 ρ, ‖f w - g w‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall 0 (ρ / 4)) :
    ‖(f z - f 0) - (g z - g 0)‖ ≤ (A / (ρ / 4)) * ‖z‖ := by
  let E (w : ℂ) := f w - g w
  have hE : AnalyticOnNhd ℂ E (ball 0 ρ) := fun w hw => (hf w hw).sub (hg w hw)
  have hs : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ := closedBall_subset_ball (by linarith)
  have hb (w : ℂ) (hw : w ∈ closedBall 0 (ρ / 4)) :
      ‖deriv E w‖ ≤ A / (ρ / 4) := by
    have hh := cauchy_deriv_on_half_disk (R := ρ / 2) (by positivity) (by linarith) hE
      (fun v hv => hA v (hs hv)) (z := w) (by rwa [show ρ / 2 / 2 = ρ / 4 by ring])
    simpa only [show ρ / 2 / 2 = ρ / 4 by ring] using hh
  have hh := (convex_closedBall (0 : ℂ) (ρ / 4)).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hE w (closedBall_subset_ball (show ρ / 4 < ρ by linarith) hw)).differentiableAt)
    hb (mem_closedBall_self (by positivity)) hz
  rw [sub_zero, show E z - E 0 = (f z - f 0) - (g z - g 0) by dsimp only [E]; ring] at hh
  exact hh

private theorem uniform_inverse_taylor {g : ℂ → ℂ} {c r ρ : ℝ}
    (hc : 0 < c) (hrc : r ≤ c / 4) (hρ : 0 < ρ) (hgc : g 0 = (c : ℂ))
    (hgA : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg : MapsTo g (ball 0 ρ) (ball (c : ℂ) r))
    (hinv : RightInvOn g eta (ball 0 ρ)) :
    ∃ C > 0, ∀ (f : ℂ → ℂ) (A : ℝ), 0 ≤ A →
      AnalyticOnNhd ℂ f (ball 0 ρ) → MapsTo f (ball 0 ρ) (ball (c : ℂ) r) →
      (∀ z ∈ ball 0 ρ, ‖f z - g z‖ ≤ A) →
      ∀ z ∈ closedBall 0 (ρ / 4),
        ‖f z - f 0 - ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z‖ ≤
          C * (A * ‖z‖ + ‖z‖ ^ 2) ∧
        ‖Complex.log (f z) - Complex.log (f 0) -
          (((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z -
            ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ) * z ^ 2)‖ ≤
          C * (A * ‖z‖ + ‖z‖ ^ 3) := by
  let G (z : ℂ) := Complex.log (g z)
  have hGA : AnalyticOnNhd ℂ G (ball 0 ρ) := log_inverse_analytic hc hrc hgA hg
  obtain ⟨hd, hd', hd''⟩ := eta_inverse_derivatives hc hrc hρ hgc hgA hg hinv
  let R := ρ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : closedBall (0 : ℂ) R ⊆ ball 0 ρ := closedBall_subset_ball (by dsimp [R]; linarith)
  have hg' := hgA.mono hs
  have hG' := hGA.mono hs
  obtain ⟨Cg, hCg, hboundg⟩ := analytic_norm_bound hR.le hg'.deriv.deriv
  obtain ⟨Cl, hCl, hboundl⟩ := analytic_norm_bound hR.le hG'.deriv.deriv.deriv
  let C := max (max Cg Cl) (max (1 / R) (2 / c / R))
  have hCgC : Cg ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hClC : Cl ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hgC : 1 / R ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hGC : (2 / c) / R ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hCg.trans_le hCgC, ?_⟩
  intro f A hA hfA hf hclose z hz
  let F (w : ℂ) := Complex.log (f w)
  have hFA : AnalyticOnNhd ℂ F (ball 0 ρ) := log_inverse_analytic hc hrc hfA hf
  have hclose' (w : ℂ) (hw : w ∈ ball 0 ρ) : ‖F w - G w‖ ≤ (2 / c) * A :=
    (log_close_on_disk hc hrc (ball_subset_closedBall (hg hw))
      (ball_subset_closedBall (hf hw))).trans
        (mul_le_mul_of_nonneg_left (hclose w hw) (by positivity))
  have hcenterg := centered_error_on_quarter_disk hρ hfA hgA hclose hz
  have hcenterl := centered_error_on_quarter_disk hρ hFA hGA hclose' hz
  have htg := first_order_error hCg.le hg' hboundg hz
  have htl := second_order_error hCl.le hG' hboundl hz
  rw [hd] at htg
  rw [show deriv G 0 = _ from hd', show deriv (deriv G) 0 = _ from hd''] at htl
  have hcoef : (((-(c ^ 2 / (1 + c ^ 2) ^ 2) : ℝ) : ℂ)) / 2 =
      -((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_neg]
    congr 1
    field_simp
  rw [hcoef, neg_mul, ← sub_eq_add_neg] at htl
  constructor
  · let P := ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z
    change ‖f z - f 0 - P‖ ≤ _
    calc
      _ = ‖((f z - f 0) - (g z - g 0)) + (g z - g 0 - P)‖ := by congr 1; ring
      _ ≤ ‖(f z - f 0) - (g z - g 0)‖ + ‖g z - g 0 - P‖ := norm_add_le _ _
      _ ≤ (A / R) * ‖z‖ + Cg * ‖z‖ ^ 2 := add_le_add hcenterg htg
      _ = (1 / R) * (A * ‖z‖) + Cg * ‖z‖ ^ 2 := by ring
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right hgC (by positivity))
          (mul_le_mul_of_nonneg_right hCgC (by positivity))
  · let P := ((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z -
      ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ) * z ^ 2
    change ‖F z - F 0 - P‖ ≤ _
    calc
      _ = ‖((F z - F 0) - (G z - G 0)) + (G z - G 0 - P)‖ := by congr 1; ring
      _ ≤ ‖(F z - F 0) - (G z - G 0)‖ + ‖G z - G 0 - P‖ := norm_add_le _ _
      _ ≤ ((2 / c) * A / R) * ‖z‖ + Cl * ‖z‖ ^ 3 := add_le_add hcenterl htl
      _ = ((2 / c) / R) * (A * ‖z‖) + Cl * ‖z‖ ^ 3 := by ring
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right hGC (by positivity))
          (mul_le_mul_of_nonneg_right hClC (by positivity))

/-- For large odd orders a fixed inverse disk gives the central poles, their conjugation,
and uniform Taylor and modulus estimates. Every root in a smaller fixed disk about
the limiting positive zero is represented. -/
theorem exists_central_poles {c : ℝ} (hc : 0 < c) (hzero : eta (c : ℂ) = 0) :
    ∃ r ε ρ B t₀ C : ℝ, 0 < ε ∧ ε ≤ r ∧ r ≤ c / 4 ∧ 0 < ρ ∧ 0 < B ∧
      0 < t₀ ∧ t₀ < ρ ∧ 0 < C ∧
      (∀ J : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ j : ℤ, |(j : ℝ)| ≤ J → ‖polePhaseLattice m j‖ ≤ t₀) ∧
      ∃ M : ℕ, ∀ m ≥ M, Odd m →
        ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 ρ) ∧
          (∀ z ∈ ball 0 ρ, g z ∈ ball (c : ℂ) r ∧ polePhase m (g z) = z ∧
            g (conj z) = conj (g z)) ∧
          0 < (g 0).re ∧ (g 0).im = 0 ∧ ‖g 0 - (c : ℂ)‖ ≤ B / order m ^ 2 ∧
          (∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ →
            aeval (2 * (order m : ℂ) * g (polePhaseLattice m j)) (denominator m) = 0) ∧
          InjOn (fun j : ℤ => 2 * (order m : ℂ) * g (polePhaseLattice m j))
            {j | ‖polePhaseLattice m j‖ ≤ t₀} ∧
          (∀ t : ℝ, |t| ≤ t₀ →
            c ^ 2 / (4 * (1 + c ^ 2) ^ 2) * t ^ 2 ≤
              Real.log (‖g ((t : ℂ) * Complex.I)‖ / ‖g 0‖)) ∧
          (∀ z ∈ closedBall 0 t₀,
            ‖g z - g 0 - ((c / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z‖ ≤
              C * (‖z‖ / order m ^ 2 + ‖z‖ ^ 2) ∧
            ‖Complex.log (g z) - Complex.log (g 0) -
              (((1 / Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) * z -
                ((c ^ 2 / (2 * (1 + c ^ 2) ^ 2) : ℝ) : ℂ) * z ^ 2)‖ ≤
              C * (‖z‖ / order m ^ 2 + ‖z‖ ^ 3)) ∧
          ∀ w ∈ ball (c : ℂ) ε, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
            ∃ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ ∧ w = g (polePhaseLattice m j) := by
  obtain ⟨r, ρ, B, hr, hrc, hρ, hB, M, hM, g, hgA, hg, hm⟩ :=
    exists_uniform_polePhase_inverse hc hzero
  have hz : (0 : ℂ) ∈ ball 0 ρ := mem_ball_self hρ
  have hgc : g 0 = (c : ℂ) := ((hg 0 hz).2.2 _ (mem_closedBall_self hr.le) hzero).symm
  obtain ⟨t₀, E, ht₀, ht₀ρ, hE, hcurve⟩ := uniform_log_curvature hc hrc hρ hgc hgA
    (fun _ hw => (hg _ hw).1) (fun _ hw => (hg _ hw).2.1)
  obtain ⟨C', hC', hTaylor⟩ := uniform_inverse_taylor hc hrc hρ hgc hgA
    (fun _ hw => (hg _ hw).1) (fun _ hw => (hg _ hw).2.1)
  let C := C' * max B 1
  have hC : 0 < C := mul_pos hC' (zero_lt_one.trans_le (le_max_right _ _))
  have htρ : t₀ < ρ := ht₀ρ.trans_lt (by linarith)
  have hcη := (analyticOnNhd_eta (c : ℂ) (by simpa using hc)).continuousAt
  have hηc : eta ⁻¹' ball 0 (t₀ / 2) ∈ 𝓝 (c : ℂ) :=
    hcη (hzero.symm ▸ ball_mem_nhds 0 (by positivity))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hηc
  let ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have hεr : ε ≤ r := min_le_left _ _
  let V := sectorMass (1 / 4)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 1 (60 * V / (t₀ / 2))) (B / E))
  refine ⟨r, ε, ρ, B, t₀, C, hε, hεr, hrc, hρ, hB, ht₀, htρ, hC,
    eventually_fixed_indices_in_cutoff ht₀, max M N, ?_⟩
  intro m hmN hodd
  have hmM : M ≤ m := (le_max_left _ _).trans hmN
  have hmN' : (N : ℝ) ≤ order m := by
    have hcast : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right M N).trans hmN
    rw [order]
    linarith
  have hthreshold := (le_max_left (max 1 (60 * V / (t₀ / 2))) (B / E)).trans hN.le
  have hν : 1 ≤ order m := ((le_max_left _ _).trans hthreshold).trans hmN'
  have hν' : order m ≤ order m ^ 2 := by nlinarith
  have hvalue : 60 * V / order m ^ 2 ≤ t₀ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    exact mul_comm (order m ^ 2) (t₀ / 2) ▸ (div_le_iff₀ (by positivity : 0 < t₀ / 2)).mp
      ((((le_max_right _ _).trans hthreshold).trans hmN').trans hν')
  have hvalue' : B / order m ^ 2 ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    exact mul_comm (order m ^ 2) E ▸ (div_le_iff₀ hE).mp
      ((((le_max_right _ _).trans hN.le).trans hmN').trans hν')
  have hM' : 160 * V ≤ order m := by
    have hmcast : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmM
    exact hM.trans (by simpa only [order, add_le_add_iff_right] using hmcast)
  have hsector : 40 * V / (1 / 4) ≤ order m := by convert hM' using 1; ring
  have hV (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) :
      (1 / 4 : ℝ) * ‖w‖ < w.re :=
    closedBall_subset_sector hc (closedBall_subset_closedBall (by linarith) hw)
  have hzeros (w : ℂ) (hw : w ∈ closedBall (c : ℂ) r) :=
    denominator_zero_iff_polePhase m hodd (by norm_num) (by norm_num) hsector (hV w hw)
  obtain ⟨gm, hgmA, hgm⟩ := hm m hmM
  have hsymm (z : ℂ) (hz : z ∈ ball 0 ρ) : gm (conj z) = conj (gm z) := by
    have hw := ball_subset_closedBall (hgm z hz).1
    have hph := polePhase_conj m (by norm_num) (by norm_num) hsector (hV (gm z) hw)
    rw [(hgm z hz).2.1] at hph
    exact ((hgm (conj z) (ball_zero_conj hz)).2.2.1 _ (closedBall_conj hw) hph).symm
  have hcenter := (hgm 0 hz).2.2.2
  rw [hgc] at hcenter
  have hjρ (j : ℤ) (hj : ‖polePhaseLattice m j‖ ≤ t₀) : polePhaseLattice m j ∈ ball 0 ρ := by
    simpa only [mem_ball_iff_norm, sub_zero] using hj.trans_lt htρ
  refine ⟨gm, hgmA, fun z hz' => ⟨(hgm z hz').1, (hgm z hz').2.1, hsymm z hz'⟩,
    sector_re_pos (by norm_num) (hV (gm 0) (ball_subset_closedBall (hgm 0 hz).1)),
    ?_, hcenter, ?_, ?_, ?_, ?_, ?_⟩
  · have he := hsymm 0 hz
    rw [map_zero] at he
    have hi := congrArg Complex.im he
    rw [Complex.conj_im] at hi
    linarith
  · intro j hj
    exact (hzeros _ (ball_subset_closedBall (hgm _ (hjρ j hj)).1)).mpr
      ⟨j, (hgm _ (hjρ j hj)).2.1⟩
  · intro i hi j hj he
    have hν : (order m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (order_pos m).ne'
    rw [mul_right_inj' (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hν)] at he
    exact polePhaseLattice_injective m ((hgm _ (hjρ i hi)).2.1.symm.trans
      ((congrArg (polePhase m) he).trans (hgm _ (hjρ j hj)).2.1))
  · intro t ht
    have htmem : (t : ℂ) * Complex.I ∈ ball 0 ρ := by
      simp only [mem_ball_iff_norm, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
      exact ht.trans_lt htρ
    have hnorm (z : ℂ) (hzm : z ∈ ball 0 ρ) : ‖gm z‖ ≠ 0 := by
      have hwpos := sector_re_pos (by norm_num)
        (hV (gm z) (ball_subset_closedBall (hgm z hzm).1))
      exact (hwpos.trans_le (Complex.re_le_norm (gm z))).ne'
    rw [Real.log_div (hnorm _ htmem) (hnorm _ hz)]
    simpa only [Complex.sub_re, Complex.log_re] using
      hcurve gm hgmA (fun _ h => (hgm _ h).1) hsymm
        (fun z h => ((hgm z h).2.2.2).trans hvalue') t ht
  · intro z hz'
    obtain ⟨hg', hl'⟩ := hTaylor gm (B / order m ^ 2) (by positivity) hgmA
      (fun _ hx => (hgm _ hx).1) (fun _ hx => (hgm _ hx).2.2.2) z
      (closedBall_subset_closedBall ht₀ρ hz')
    have hscale (k : ℕ) :
        C' * (B / order m ^ 2 * ‖z‖ + ‖z‖ ^ k) ≤ C * (‖z‖ / order m ^ 2 + ‖z‖ ^ k) := by
      have hnorm : 0 ≤ ‖z‖ / order m ^ 2 := by positivity
      have hb := mul_le_mul_of_nonneg_right (le_max_left B (1 : ℝ)) hnorm
      have hpow := mul_le_mul_of_nonneg_right (le_max_right B (1 : ℝ))
        (show 0 ≤ ‖z‖ ^ k by positivity)
      dsimp only [C]
      rw [mul_assoc, show B / order m ^ 2 * ‖z‖ = B * (‖z‖ / order m ^ 2) by ring]
      apply mul_le_mul_of_nonneg_left _ hC'.le
      rw [mul_add]
      rw [one_mul] at hpow
      exact add_le_add hb hpow
    exact ⟨hg'.trans (hscale 2), hl'.trans (hscale 3)⟩
  · intro w hw
    have hwr : w ∈ closedBall (c : ℂ) r :=
      closedBall_subset_closedBall hεr (ball_subset_closedBall hw)
    have hwδ : w ∈ ball (c : ℂ) δ := ball_subset_ball (min_le_right _ _) hw
    have hη : ‖eta w‖ < t₀ / 2 := by simpa [mem_ball_iff_norm] using hδ' hwδ
    have hpert := (polePhase_compact_estimate m hc hM').1 w
      (closedBall_subset_closedBall (show r ≤ c / 2 by linarith) hwr)
    have hp : ‖polePhase m w‖ ≤ t₀ := by
      have ht := norm_sub_le (polePhase m w - eta w) (-eta w)
      rw [norm_neg, sub_neg_eq_add, sub_add_cancel] at ht
      linarith [hpert.trans hvalue]
    rw [hzeros w hwr]
    constructor
    · rintro ⟨j, hj⟩
      have hj' := hj ▸ hp
      exact ⟨j, hj', (hgm _ (hjρ j hj')).2.2.1 w hwr hj⟩
    · rintro ⟨j, hj', rfl⟩
      exact ⟨j, (hgm _ (hjρ j hj')).2.1⟩

end D5.S3.Analytic.Polynomial.DiagonalPadePhase
