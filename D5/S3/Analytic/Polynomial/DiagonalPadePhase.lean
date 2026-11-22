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
import all D5.S3.Analytic.HalfIntegerBesselSector
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

end D5.S3.Analytic.Polynomial.DiagonalPadePhase
