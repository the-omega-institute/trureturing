/- GID: D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ArtificialSourceCellEstimates
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Quartic cell bumps obey uniform Robin-coordinate derivative bounds. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
open D5.S3.Arith.Robin.MellinWeightedVariation
namespace D5.S3.Analytic.Interpolation.ArtificialSourceCellEstimates
local notation "c" => (1 / 128 : ℝ)
local notation "k" => weight
local notation "etaOne" => (fun s : ℝ => 2 * s * (1 - s) * (1 - 2 * s))
local notation "etaTwo" => (fun s : ℝ => 2 - 12 * s + 12 * s ^ 2)
local notation "kernelSlope" => (fun x : ℝ =>
  -(2 * (Real.log x) ^ 2 + 3 * Real.log x + 2) / (x ^ 3 * (Real.log x) ^ 3))
/-- The quartic bump has a double zero at either endpoint. -/
def eta (s : ℝ) : ℝ := s ^ 2 * (1 - s) ^ 2

/-- The local increment budget. -/
def epsilon (a : ℝ) : ℝ := Real.log a * Real.exp (-(Real.log a) ^ (1 / 4 : ℝ))

/-- The cell width for a fixed positive logarithmic excess. -/
def width (δ a : ℝ) : ℝ :=
  a ^ (3 / 4 : ℝ) * Real.exp ((Real.log a) ^ (1 / 4 : ℝ) / 2) /
    Real.sqrt (Real.log a) * (Real.log a) ^ δ

/-- The height of the cell's negative bump. -/
def amplitude (δ a : ℝ) : ℝ := c * (Real.log a) ^ (2 * δ - 1) / Real.sqrt a

local notation "cellSlope" => (fun δ a x : ℝ =>
  -(amplitude δ a / width δ a) * etaOne ((x - a) / width δ a))
local notation "cellSecond" => (fun δ a x : ℝ =>
  -(amplitude δ a / (width δ a) ^ 2) * etaTwo ((x - a) / width δ a))

/-- Polynomial continuation of the bump in one cell. -/
def cellBump (δ a x : ℝ) : ℝ :=
  -amplitude δ a * eta ((x - a) / width δ a)

private theorem eta_derivatives (s : ℝ) :
    HasDerivAt eta (etaOne s) s ∧ HasDerivAt etaOne (etaTwo s) s := by
  constructor
  · convert ((hasDerivAt_id s).pow 2).mul
      (((hasDerivAt_const s 1).sub (hasDerivAt_id s)).pow 2) using 1 <;> first | rfl | (dsimp [eta]; ring)
  · convert ((((hasDerivAt_id s).const_mul 2).mul
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s))).mul
        ((hasDerivAt_const s 1).sub ((hasDerivAt_id s).const_mul 2))) using 1 <;> first | rfl | (dsimp; ring)

private theorem eta_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ eta s ∧ eta s ≤ 1 / 16 ∧ |etaOne s| ≤ 1 / 2 ∧ |etaTwo s| ≤ 2 := by
  have hp : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (by linarith [hs.2])
  have hpq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hfactor : |1 - 2 * s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨by unfold eta; positivity, ?_, ?_, ?_⟩
  · unfold eta
    nlinarith [sq_nonneg (s * (1 - s) - 1 / 4)]
  · dsimp only
    rw [show 2 * s * (1 - s) = 2 * (s * (1 - s)) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (s * (1 - s)))]
    nlinarith [mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * (s * (1 - s)))]
  · exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s - 1 / 2)], by nlinarith⟩

theorem kernel_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt k (kernelSlope x) x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hd := (hasDerivAt_scaleWeight hx0 (by norm_num : (0 : ℝ) < 1)
    (by simpa using hx)).fun_div (hasDerivAt_id x) hx0.ne'
  have hfun : (fun z : ℝ => scaleWeight z 1 / z) = k := by
    ext z
    rw [scaleWeight_eq]
    by_cases hz : z = 0
    · simp [hz, weight]
    · simp [hz]
  dsimp only [id] at hd
  rw [hfun] at hd
  convert! hd using 1 <;> first
  | rfl
  | (unfold scaleDerivative scaleWeight; norm_num; field_simp [hx0.ne', hl.ne'] <;> ring)

private theorem kernel_cell_bounds {a x : ℝ} (ha : 1 < a) (hLa : 1 ≤ Real.log a)
    (hx : x ∈ Icc a (2 * a)) :
    0 < k x ∧ (k x)⁻¹ ≤ 8 * a ^ 2 * Real.log a ∧
      |kernelSlope x| / k x ≤ 7 / a := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hL : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx.1
  have hLx : 1 ≤ Real.log x := hLa.trans hL
  have hl0 : 0 < Real.log x := by linarith
  have hupper : Real.log x ≤ 2 * Real.log a := by
    have h := Real.log_le_log hx0 hx.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at h
    have htwo : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hk : 0 < k x := by unfold weight; positivity
  refine ⟨hk, ?_, ?_⟩
  · have hsq : x ^ 2 ≤ 4 * a ^ 2 := by nlinarith [hx.2]
    have hnum : (Real.log x) ^ 2 / (Real.log x + 1) ≤ Real.log x := by
      apply (div_le_iff₀ (by positivity : 0 < Real.log x + 1)).2
      nlinarith
    calc
      (k x)⁻¹ = x ^ 2 * ((Real.log x) ^ 2 / (Real.log x + 1)) := by
        unfold weight
        field_simp
      _ ≤ x ^ 2 * Real.log x := mul_le_mul_of_nonneg_left hnum (sq_nonneg x)
      _ ≤ (4 * a ^ 2) * (2 * Real.log a) :=
        mul_le_mul hsq hupper hl0.le (by positivity)
      _ = _ := by ring
  · have hnum : 2 * (Real.log x) ^ 2 + 3 * Real.log x + 2 ≤
        7 * Real.log x * (Real.log x + 1) := by nlinarith
    calc
      |kernelSlope x| / k x =
          (2 * (Real.log x) ^ 2 + 3 * Real.log x + 2) /
            (x * Real.log x * (Real.log x + 1)) := by
        rw [abs_of_nonpos (by
          dsimp only
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
            (by positivity) : kernelSlope x ≤ 0)]
        unfold weight
        field_simp [hx0.ne', hl0.ne', (by positivity : Real.log x + 1 ≠ 0)]
        <;> ring
      _ ≤ (7 * Real.log x * (Real.log x + 1)) /
          (x * Real.log x * (Real.log x + 1)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = 7 / x := by field_simp
      _ ≤ 7 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hx.1

private theorem width_exp {δ a : ℝ} (ha : 1 < a) :
    width δ a = Real.exp ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a)) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  simp only [width, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha0,
    Real.rpow_def_of_pos hL, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private theorem amplitude_exp {δ a : ℝ} (ha : 1 < a) :
    amplitude δ a = c * Real.exp ((2 * δ - 1) * Real.log (Real.log a) - Real.log a / 2) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  simp only [amplitude, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha0,
    Real.rpow_def_of_pos hL, div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  congr 1
  ring

private theorem amplitude_width_cancellation {δ a : ℝ} (ha : 1 < a) :
    amplitude δ a / (width δ a) ^ 2 = c * epsilon a / (a ^ 2 * Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  rw [width_exp ha, amplitude_exp ha]
  have hexp : (Real.exp ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a))) ^ 2 =
      Real.exp (2 * ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hcancel : epsilon a / (a ^ 2 * Real.log a) =
      Real.exp (-(Real.log a) ^ (1 / 4 : ℝ) - 2 * Real.log a) := by
    rw [epsilon, Real.exp_sub, show (2 : ℝ) * Real.log a = (2 : ℕ) * Real.log a by norm_num,
      Real.exp_nat_mul, Real.exp_log ha0]
    field_simp
  rw [mul_div_assoc c (epsilon a) (a ^ 2 * Real.log a), hcancel]
  simp only [div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  congr 1
  ring

theorem cell_derivatives {δ a x : ℝ} (hw : 0 < width δ a) :
    HasDerivAt (cellBump δ a) (cellSlope δ a x) x ∧
      HasDerivAt (cellSlope δ a) (cellSecond δ a x) x := by
  have hc := ((hasDerivAt_id x).sub_const a).div_const (width δ a)
  constructor
  · convert ((eta_derivatives ((x - a) / width δ a)).1.comp x hc).const_mul
      (-amplitude δ a) using 1 <;> first | rfl | (dsimp [cellBump]; ring)
  · convert ((eta_derivatives ((x - a) / width δ a)).2.comp x hc).const_mul
      (-(amplitude δ a / width δ a)) using 1 <;> first | rfl | (dsimp; field_simp <;> ring)

theorem cell_estimates {δ a x : ℝ} (ha : 1 < a) (hLa : 1 ≤ Real.log a)
    (hw : 0 < width δ a) (hwa : width δ a ≤ a)
    (hx : x ∈ Icc a (a + width δ a)) :
    |cellSlope δ a x / k x| ≤ 4 * c * epsilon a * width δ a ∧
      |deriv (fun y : ℝ => y - cellSlope δ a y / k y) x - 1| ≤
        44 * c * epsilon a := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < Real.log a := by linarith
  have heps : 0 < epsilon a := by unfold epsilon; positivity
  have hα : 0 ≤ amplitude δ a := by unfold amplitude; positivity
  have hs : (x - a) / width δ a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hw.le
    · apply (div_le_iff₀ hw).2
      linarith [hx.2]
  have hη := eta_bounds hs
  have hk := kernel_cell_bounds ha hLa ⟨hx.1, by linarith [hx.2]⟩
  have hx1 : 1 < x := ha.trans_le hx.1
  have hcancel := amplitude_width_cancellation (δ := δ) ha
  have hfirst : |cellSlope δ a x| ≤ amplitude δ a / (2 * width δ a) := by
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg hα hw.le)]
    calc
      _ ≤ (amplitude δ a / width δ a) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hη.2.2.1 (div_nonneg hα hw.le)
      _ = _ := by ring
  have hsecond : |cellSecond δ a x| ≤ 2 * amplitude δ a / (width δ a) ^ 2 := by
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg hα (sq_nonneg _))]
    calc
      _ ≤ (amplitude δ a / (width δ a) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hη.2.2.2 (div_nonneg hα (sq_nonneg _))
      _ = _ := by ring
  have hbase : (amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a) =
      c * epsilon a := by
    rw [hcancel]
    field_simp
  have hvalue : |cellSlope δ a x / k x| ≤ 4 * c * epsilon a * width δ a := by
    calc
      |cellSlope δ a x / k x| = |cellSlope δ a x| * (k x)⁻¹ := by
        rw [abs_div, abs_of_pos hk.1, div_eq_mul_inv]
      _ ≤ (amplitude δ a / (2 * width δ a)) * (8 * a ^ 2 * Real.log a) :=
        mul_le_mul hfirst hk.2.1 (inv_nonneg.mpr hk.1.le) (by positivity)
      _ = 4 * ((amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a)) *
          width δ a := by field_simp; ring
      _ = _ := by rw [hbase]; ring
  refine ⟨hvalue, ?_⟩
  have hd := (hasDerivAt_id x).sub
    ((cell_derivatives hw).2.fun_div (kernel_hasDerivAt hx1) hk.1.ne')
  change HasDerivAt (fun y : ℝ => y - cellSlope δ a y / k y) _ x at hd
  rw [hd.deriv]
  have heq : 1 - (cellSecond δ a x * k x - cellSlope δ a x * kernelSlope x) /
      (k x) ^ 2 - 1 =
      -(cellSecond δ a x / k x) + (cellSlope δ a x / k x) * (kernelSlope x / k x) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |cellSecond δ a x / k x| +
        |cellSlope δ a x / k x| * |kernelSlope x / k x| := by
      simpa only [abs_neg, abs_mul] using abs_add_le
        (-(cellSecond δ a x / k x))
        ((cellSlope δ a x / k x) * (kernelSlope x / k x))
    _ ≤ 16 * c * epsilon a + (4 * c * epsilon a * width δ a) * (7 / a) := by
      apply add_le_add
      · calc
          |cellSecond δ a x / k x| = |cellSecond δ a x| * (k x)⁻¹ := by
            rw [abs_div, abs_of_pos hk.1, div_eq_mul_inv]
          _ ≤ (2 * amplitude δ a / (width δ a) ^ 2) * (8 * a ^ 2 * Real.log a) :=
            mul_le_mul hsecond hk.2.1 (inv_nonneg.mpr hk.1.le) (by positivity)
          _ = 16 * ((amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a)) := by
            ring
          _ = _ := by rw [hbase]; ring
      · apply mul_le_mul hvalue
          (by simpa only [abs_div, abs_of_pos hk.1] using hk.2.2)
          (abs_nonneg _) (by positivity)
    _ ≤ 44 * c * epsilon a := by
      have hwa' : width δ a / a ≤ 1 := (div_le_one ha0).2 hwa
      have heq' : (4 * c * epsilon a * width δ a) * (7 / a) =
          28 * c * epsilon a * (width δ a / a) := by ring
      rw [heq']
      nlinarith [mul_le_mul_of_nonneg_left hwa'
        (by positivity : 0 ≤ 28 * c * epsilon a)]

theorem epsilon_hasDerivAt {a : ℝ} (ha : 1 < a) :
    HasDerivAt epsilon (Real.exp (-(Real.log a) ^ (1 / 4 : ℝ)) / a *
      (1 - (Real.log a) ^ (1 / 4 : ℝ) / 4)) a := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  have hlog := Real.hasDerivAt_log ha0.ne'
  have hu := (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ))
    (Or.inl hL.ne')).comp a hlog
  have hp : Real.log a * (Real.log a) ^ ((1 / 4 : ℝ) - 1) =
      (Real.log a) ^ (1 / 4 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (Real.log a)]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  convert! hlog.mul (hu.neg.exp) using 1 <;> first
  | rfl
  | (dsimp [epsilon]; field_simp; nlinarith [hp])

theorem epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := by
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    Real.tendsto_log_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 1
    (by norm_num)).comp hu
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
  have hL : 0 < Real.log a := Real.log_pos ha
  dsimp [epsilon]
  rw [← Real.rpow_mul hL.le]
  norm_num

theorem width_eventually_bounds {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in atTop, 1 ≤ Real.log a ∧ 1 ≤ width δ a ∧ width δ a ≤ a := by
  have hu : Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ) / L) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [show -(3 / 4 : ℝ) = 1 / 4 - 1 by ring, Real.rpow_sub hL, Real.rpow_one]
  have hlog : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall : Tendsto (fun L : ℝ =>
      L ^ (1 / 4 : ℝ) / L / 2 + (δ - 1 / 2) * (Real.log L / L)) atTop (𝓝 0) := by
    simpa using (hu.div_const 2).add (hlog.const_mul (δ - 1 / 2))
  have hev := (hsmall.comp Real.tendsto_log_atTop).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hev, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with a hsmall hL ha
  have hL0 : 0 < Real.log a := by linarith
  have hlogL : 0 ≤ Real.log (Real.log a) := Real.log_nonneg hL
  have hlogL' : Real.log (Real.log a) ≤ Real.log a - 1 :=
    Real.log_le_sub_one_of_pos hL0
  have hu0 : 0 ≤ (Real.log a) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hL0.le _
  refine ⟨hL, ?_, ?_⟩
  · rw [width_exp ha, Real.one_le_exp_iff]
    nlinarith [mul_nonneg hδ.le hlogL]
  · rw [width_exp ha]
    apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log (by linarith : 0 < a))
    have heq : (Real.log a) ^ (1 / 4 : ℝ) / Real.log a / 2 +
        (δ - 1 / 2) * (Real.log (Real.log a) / Real.log a) =
        ((Real.log a) ^ (1 / 4 : ℝ) / 2 +
          (δ - 1 / 2) * Real.log (Real.log a)) / Real.log a := by ring
    dsimp only [Function.comp_def] at hsmall
    rw [heq] at hsmall
    have h := (div_lt_iff₀ hL0).1 hsmall
    linarith

theorem epsilon_cell_comparison {a x : ℝ} (ha : 1 < a)
    (hLa : 1 ≤ Real.log a) (hx : x ∈ Icc a (2 * a)) : epsilon a ≤ 2 * epsilon x := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hlog := Real.log_le_log ha0 hx.1
  have hL0 : 0 < Real.log a := by linarith
  have hroot : (Real.log x) ^ (1 / 4 : ℝ) - (Real.log a) ^ (1 / 4 : ℝ) ≤
      Real.log x - Real.log a := by
    have hd : ∀ L ∈ Icc (Real.log a) (Real.log x),
        HasDerivWithinAt (fun z : ℝ => z ^ (1 / 4 : ℝ))
          ((1 / 4 : ℝ) * L ^ ((1 / 4 : ℝ) - 1)) (Icc (Real.log a) (Real.log x)) L := by
      intro L hL
      exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hL0.trans_le hL.1)))).hasDerivWithinAt
    have hb : ∀ L ∈ Ico (Real.log a) (Real.log x),
        ‖(1 / 4 : ℝ) * L ^ ((1 / 4 : ℝ) - 1)‖ ≤ 1 := by
      intro L hL
      have hL1 : 1 ≤ L := hLa.trans hL.1
      have hr := Real.rpow_le_one_of_one_le_of_nonpos hL1
        (by norm_num : (1 / 4 : ℝ) - 1 ≤ 0)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (Real.log x)
      (right_mem_Icc.2 hlog)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, one_mul] using hm)
  have hlogdiff : Real.log x - Real.log a ≤ Real.log (2 : ℝ) := by
    have h := Real.log_le_log hx0 hx.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at h
    linarith
  have hfactor : Real.exp ((Real.log x) ^ (1 / 4 : ℝ) -
      (Real.log a) ^ (1 / 4 : ℝ)) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log (2 : ℝ)) := Real.exp_le_exp.mpr (hroot.trans hlogdiff)
      _ = _ := Real.exp_log (by norm_num)
  calc
    epsilon a = Real.log a * Real.exp ((Real.log x) ^ (1 / 4 : ℝ) -
        (Real.log a) ^ (1 / 4 : ℝ)) * Real.exp (-(Real.log x) ^ (1 / 4 : ℝ)) := by
      simp only [epsilon, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.log x * 2 * Real.exp (-(Real.log x) ^ (1 / 4 : ℝ)) := by
      gcongr
      linarith
    _ = 2 * epsilon x := by unfold epsilon; ring

theorem epsilon_width_identity {δ a : ℝ} (ha : 1 < a) :
    epsilon a * width δ a = a ^ (3 / 4 : ℝ) *
      Real.exp (-(Real.log a) ^ (1 / 4 : ℝ) / 2) * (Real.log a) ^ (δ + 1 / 2) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  rw [width_exp ha]
  simp only [epsilon, Real.rpow_def_of_pos ha0, Real.rpow_def_of_pos hL]
  conv_lhs => lhs; lhs; rw [← Real.exp_log hL]
  simp only [← Real.exp_add]
  congr 1
  ring

end D5.S3.Analytic.Interpolation.ArtificialSourceCellEstimates
