/- GID: D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Fourth-order actual cutoff curvature and its uniform integer sign consequence. -/
import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual-root fourth-order analysis and a conditional paid-growth sign restriction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
open Real Filter Finset
open scoped Topology
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature

/-- Ratios and mixed differences always use the actual clamped cutoffs. -/
def theta (X : ℝ) : ℝ := d 3 X / d 2 X
def NU (X : ℝ) : ℝ := 3 * d 4 X - d 8 X - 3 * d 2 X
def NV (X : ℝ) : ℝ := d 2 X - 2 * d 4 X + d 8 X - d 3 X + 2 * d 6 X - d 12 X
def U (X : ℝ) : ℝ := NU X / d 2 X
def V (X : ℝ) : ℝ := NV X / d 2 X
def A (X : ℝ) : ℝ := (theta X - 1) * U X - V X
def kappa : ℝ := 3 * log 2 * log 3 * log (3 / 2 : ℝ)

private def P (s : ℝ) : Polynomial ℝ :=
  Polynomial.C s - Polynomial.C s * Polynomial.X +
    Polynomial.C (s + s ^ 2 / 2) * Polynomial.X ^ 2 -
    Polynomial.C (s + 3 * s ^ 2 / 2 + s ^ 3 / 3) * Polynomial.X ^ 3 +
    Polynomial.C (s + 3 * s ^ 2 + 11 * s ^ 3 / 6 + s ^ 4 / 4) * Polynomial.X ^ 4

private theorem p_coeff (s : ℝ) (n : ℕ) :
    (P s).coeff n = (if n = 0 then s else 0) - (if n = 1 then s else 0) +
      (if n = 2 then s + s ^ 2 / 2 else 0) -
      (if n = 3 then s + 3 * s ^ 2 / 2 + s ^ 3 / 3 else 0) +
      (if n = 4 then s + 3 * s ^ 2 + 11 * s ^ 3 / 6 + s ^ 4 / 4 else 0) := by
  simp only [P, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero, eq_comm]

private theorem coeff_product (p q : Polynomial ℝ) (n : ℕ) :
    (p * q).coeff n = ∑ k ∈ range (n + 1), p.coeff k * q.coeff (n - k) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

private def R (s : ℝ) : Polynomial ℝ :=
  let t := Polynomial.X * P s
  P s + t - Polynomial.C (1 / 2) * t ^ 2 + Polynomial.C (1 / 3) * t ^ 3 -
    Polynomial.C (1 / 4) * t ^ 4 - Polynomial.C s

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
-- Finite coefficient convolutions require normalization of the symbolic log coefficients.
private theorem residual_dvd (s : ℝ) : (Polynomial.X : Polynomial ℝ) ^ 5 ∣ R s := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  interval_cases n <;>
    norm_num [R, coeff_product, p_coeff, Polynomial.coeff_X,
      pow_succ, Finset.sum_range_succ] <;> ring

private theorem p_zero (s : ℝ) : (P s).eval 0 = s := by simp [P]

private theorem p_limit (s : ℝ) :
    Tendsto (fun X : ℝ => (P s).eval (1 / log X)) atTop (𝓝 s) := by
  simpa only [Function.comp_def, p_zero] using (P s).continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.div_atTop tendsto_log_atTop :
      Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0))

private theorem residual_limit (s : ℝ) :
    Tendsto (fun X : ℝ => log X ^ 4 *
      (F (log X) ((P s).eval (1 / log X)) - s)) atTop (𝓝 0) := by
  let z := fun X : ℝ => 1 / log X
  let p := fun X : ℝ => (P s).eval (z X)
  let t := fun X : ℝ => z X * p X
  have hz : Tendsto z atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hp : Tendsto p atTop (𝓝 s) := p_limit s
  have ht : Tendsto t atTop (𝓝 0) := by simpa only [zero_mul] using hz.mul hp
  have habs : ∀ᶠ X : ℝ in atTop, |-(t X)| < 1 / 2 := by
    have hh := ht.abs.eventually (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
    simpa only [abs_neg] using hh
  let E := fun X : ℝ => log (1 + t X) -
    (t X - t X ^ 2 / 2 + t X ^ 3 / 3 - t X ^ 4 / 4)
  have hE : ∀ᶠ X : ℝ in atTop, |log X ^ 4 * E X| ≤
      2 * (z X * |p X| ^ 5) := by
    filter_upwards [habs, eventually_gt_atTop (1 : ℝ)] with X hx hX
    have hL : 0 < log X := log_pos hX
    have hz0 : 0 ≤ z X := by dsimp [z]; positivity
    have hh := abs_log_sub_add_sum_range_le (by linarith : |-(t X)| < 1) 4
    have heq : (∑ i ∈ range 4, (-(t X)) ^ (i + 1) / (i + 1)) +
        log (1 - -(t X)) = E X := by
      norm_num [E, Finset.sum_range_succ]
      <;> ring
    have he : |E X| ≤ |t X| ^ 5 / (1 - |t X|) := by
      simpa only [heq, abs_neg] using hh
    have hden : 0 < 1 - |t X| := by rw [abs_neg] at hx; linarith
    have hh' : |E X| ≤ 2 * |t X| ^ 5 := he.trans (by
      apply (div_le_iff₀ hden).mpr
      rw [abs_neg] at hx
      nlinarith [pow_nonneg (abs_nonneg (t X)) 5])
    rw [abs_mul, abs_of_nonneg (pow_nonneg hL.le 4)]
    have hh'' := mul_le_mul_of_nonneg_left hh' (pow_nonneg hL.le 4)
    have hid : log X ^ 4 * (2 * |t X| ^ 5) = 2 * (z X * |p X| ^ 5) := by
      dsimp [t, z]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / log X), mul_pow]
      field_simp [hL.ne']
      <;> ring
    exact hid ▸ hh''
  have hEzero : Tendsto (fun X : ℝ => log X ^ 4 * E X) atTop (𝓝 0) := by
    apply squeeze_zero_norm' hE
    simpa only [zero_mul, mul_zero] using (hz.mul (hp.abs.pow 5)).const_mul 2
  obtain ⟨q, hq⟩ := residual_dvd s
  have hqzero : Tendsto (fun X : ℝ => log X ^ 4 * (R s).eval (z X)) atTop (𝓝 0) := by
    have hh := hz.mul ((q.continuous.continuousAt.tendsto).comp hz)
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    dsimp [z, Function.comp_def]
    field_simp [(log_pos hX).ne']
    <;> ring
  have hh := hqzero.add hEzero
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [] with X
  dsimp [R, E, F, t, p, z]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp only [div_eq_mul_inv, one_mul, mul_comm]
  ring

/-- The approximation is transferred to each fixed actual root; the gain error
is retained after multiplication by the fourth power of the logarithm. -/
private theorem actual_quartic_error {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => log X ^ 4 *
      (d j X - (P (log j)).eval (1 / log X))) atTop (𝓝 0) := by
  have hs : 0 < log (j : ℝ) := log_pos (by exact_mod_cast (show 1 < j by omega))
  have hp := (p_limit (log j)).eventually (eventually_gt_nhds hs)
  have hbound : ∀ᶠ X : ℝ in atTop,
      |log X ^ 4 * (d j X - (P (log j)).eval (1 / log X))| ≤
      |log X ^ 4 * η j X| +
        |log X ^ 4 * (F (log X) ((P (log j)).eval (1 / log X)) - log j)| := by
    filter_upwards [actual_root_equation hj, hp, eventually_gt_atTop (1 : ℝ)]
      with X hr hpX hX
    obtain ⟨q, hq, _, he⟩ := F_secant (log_pos hX) hpX.le hr.1.le
    have hq0 : 0 ≤ q := by linarith
    have hdiff : |d j X - (P (log j)).eval (1 / log X)| ≤
        |F (log X) (d j X) - F (log X) ((P (log j)).eval (1 / log X))| := by
      rw [he, abs_mul, abs_of_nonneg hq0]
      exact le_mul_of_one_le_right (abs_nonneg _) hq
    have hh := mul_le_mul_of_nonneg_left hdiff (pow_nonneg (log_pos hX).le 4)
    rw [hr.2.2] at hh
    rw [abs_mul, abs_of_nonneg (pow_nonneg (log_pos hX).le 4)]
    apply hh.trans
    have hh' := abs_add_le (log X ^ 4 * η j X)
      (-(log X ^ 4 * (F (log X) ((P (log j)).eval (1 / log X)) - log j)))
    rw [abs_neg] at hh' 
    calc
      _ = |log X ^ 4 * (log j + η j X -
          F (log X) ((P (log j)).eval (1 / log X)))| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (log_pos hX).le 4)]
      _ = _ := by congr 1; ring
      _ ≤ _ := hh'
  apply squeeze_zero_norm' hbound
  simpa using (scaled_root_error hj 4).abs.add (residual_limit (log j)).abs

private def areaPoly (a b : ℝ) : Polynomial ℝ :=
  (P b - P a) * (3 * P (2 * a) - P (3 * a) - 3 * P a) -
    P a * (P a - 2 * P (2 * a) + P (3 * a) - P b +
      2 * P (a + b) - P (2 * a + b))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
-- Finite coefficient convolutions require normalization of the symbolic log coefficients.
private theorem area_dvd (a b : ℝ) :
    (Polynomial.X : Polynomial ℝ) ^ 4 ∣ areaPoly a b := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  interval_cases n <;>
    norm_num [areaPoly, coeff_product, p_coeff, Finset.sum_range_succ] <;> ring

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
-- Finite coefficient convolutions require normalization of the symbolic log coefficients.
private theorem area_coeff (a b : ℝ) :
    (areaPoly a b).coeff 4 = 3 * a ^ 3 * b * (b - a) := by
  norm_num [areaPoly, coeff_product, p_coeff, Finset.sum_range_succ]
  <;> ring

private theorem polynomial_area_limit (a b : ℝ) :
    Tendsto (fun X : ℝ => log X ^ 4 * (areaPoly a b).eval (1 / log X))
      atTop (𝓝 (3 * a ^ 3 * b * (b - a))) := by
  obtain ⟨q, hq⟩ := area_dvd a b
  have hq0 : q.eval 0 = 3 * a ^ 3 * b * (b - a) := by
    have hh := area_coeff a b
    rw [hq, Polynomial.coeff_X_pow_mul] at hh
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hh
  have hz : Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hh := q.continuous.continuousAt.tendsto.comp hz
  rw [hq0] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  dsimp only [Function.comp_def]
  field_simp [(log_pos hX).ne']
  <;> ring

private theorem scaled_product_error {f g p q : ℝ → ℝ} {a b : ℝ}
    (hf : Tendsto (fun X => log X ^ 4 * (f X - p X)) atTop (𝓝 0))
    (hg : Tendsto (fun X => log X ^ 4 * (g X - q X)) atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 a)) (hgb : Tendsto g atTop (𝓝 b)) :
    Tendsto (fun X => log X ^ 4 * (f X * g X - p X * q X)) atTop (𝓝 0) := by
  have hh := (hf.mul hgb).add (hp.mul hg)
  simp only [zero_mul, mul_zero, add_zero] at hh
  convert hh using 1
  funext X
  ring

/-- The fourth-order limit concerns all real X tending to infinity and the
six actual roots, with no assumed analytic curvature. -/
theorem actual_mixed_curvature_tendsto :
    Tendsto (fun X : ℝ => log X ^ 4 * A X) atTop (𝓝 kappa) := by
  let p := fun (j : ℕ) (X : ℝ) => (P (log j)).eval (1 / log X)
  let pu := fun X => 3 * p 4 X - p 8 X - 3 * p 2 X
  let pv := fun X => p 2 X - 2 * p 4 X + p 8 X - p 3 X + 2 * p 6 X - p 12 X
  have herr (j : ℕ) (hj : 2 ≤ j) :
      Tendsto (fun X => log X ^ 4 * (d j X - p j X)) atTop (𝓝 0) :=
    actual_quartic_error hj
  have hNU : Tendsto (fun X => log X ^ 4 * (NU X - pu X)) atTop (𝓝 0) := by
    have hh := ((herr 4 (by norm_num)).const_mul 3).sub (herr 8 (by norm_num))
      |>.sub ((herr 2 (by norm_num)).const_mul 3)
    simp only [mul_zero, sub_zero] at hh
    convert hh using 1
    funext X
    dsimp [NU, pu]
    ring
  have hNV : Tendsto (fun X => log X ^ 4 * (NV X - pv X)) atTop (𝓝 0) := by
    have hh := (herr 2 (by norm_num)).sub ((herr 4 (by norm_num)).const_mul 2)
      |>.add (herr 8 (by norm_num)) |>.sub (herr 3 (by norm_num))
      |>.add ((herr 6 (by norm_num)).const_mul 2) |>.sub (herr 12 (by norm_num))
    simp only [mul_zero, sub_zero, add_zero] at hh
    convert hh using 1
    funext X
    dsimp [NV, pv]
    ring
  have hdp : Tendsto (fun X => log X ^ 4 *
      ((d 3 X - d 2 X) - (p 3 X - p 2 X))) atTop (𝓝 0) := by
    have hh := (herr 3 (by norm_num)).sub (herr 2 (by norm_num))
    simp only [sub_zero] at hh
    convert hh using 1
    funext X
    ring
  have hd (j : ℕ) (hj : 2 ≤ j) : Tendsto (d j) atTop (𝓝 (log j)) :=
    fixed_layer_root_offset_tendsto hj
  have hnut : Tendsto NU atTop (𝓝 (3 * log 4 - log 8 - 3 * log 2)) :=
    ((hd 4 (by norm_num)).const_mul 3).sub (hd 8 (by norm_num))
      |>.sub ((hd 2 (by norm_num)).const_mul 3)
  have hnvt : Tendsto NV atTop
      (𝓝 (log 2 - 2 * log 4 + log 8 - log 3 + 2 * log 6 - log 12)) :=
    (hd 2 (by norm_num)).sub ((hd 4 (by norm_num)).const_mul 2)
      |>.add (hd 8 (by norm_num)) |>.sub (hd 3 (by norm_num))
      |>.add ((hd 6 (by norm_num)).const_mul 2) |>.sub (hd 12 (by norm_num))
  have he1 := scaled_product_error hdp hNU
    ((p_limit (log 3)).sub (p_limit (log 2))) hnut
  have he2 := scaled_product_error (herr 2 (by norm_num)) hNV (p_limit (log 2)) hnvt
  have he := he1.sub he2
  simp only [sub_zero] at he
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat]
      using (Real.log_pow (2 : ℝ) 2)
  have hlog8 : log (8 : ℝ) = 3 * log 2 := by
    simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num, Nat.cast_ofNat]
      using (Real.log_pow (2 : ℝ) 3)
  have hlog6 : log (6 : ℝ) = log 2 + log 3 := by
    simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0))
  have hlog12 : log (12 : ℝ) = 2 * log 2 + log 3 := by
    have hh := Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
    simpa only [show (4 : ℝ) * 3 = 12 by norm_num, hlog4] using hh
  have hnum : Tendsto (fun X => log X ^ 4 *
      ((d 3 X - d 2 X) * NU X - d 2 X * NV X)) atTop
      (𝓝 (3 * log 2 ^ 3 * log 3 * (log 3 - log 2))) := by
    have hh := (polynomial_area_limit (log 2) (log 3)).add he
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    dsimp [areaPoly, p, pu, pv]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, hlog4, hlog8, hlog6, hlog12]
    ring
  have hlog2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hh := hnum.div ((hd 2 (by norm_num)).pow 2) (pow_ne_zero 2 hlog2)
  have hk : (3 * log 2 ^ 3 * log 3 * (log 3 - log 2)) / log 2 ^ 2 = kappa := by
    dsimp [kappa]
    rw [log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
    <;> ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [hk] at hh
  apply hh.congr'
  filter_upwards [actual_root_equation (by norm_num : 2 ≤ 2)] with X hX
  dsimp only [Pi.div_apply]
  dsimp [A, theta, U, V]
  field_simp [hX.1.ne']
  <;> ring

/-- The limiting coefficient has a strictly positive sign. -/
theorem kappa_pos : 0 < kappa := by
  dsimp [kappa]
  positivity

/-- A positive lower bound for the actual mixed curvature. -/
theorem actual_mixed_curvature_lower : ∀ᶠ X : ℝ in atTop,
    0 < log X ∧ kappa / (2 * log X ^ 4) ≤ A X := by
  have hh := actual_mixed_curvature_tendsto.eventually
    (eventually_gt_nhds (show kappa / 2 < kappa by linarith [kappa_pos]))
  filter_upwards [hh, eventually_gt_atTop (1 : ℝ)] with X hX h1
  have hL := log_pos h1
  refine ⟨hL, (div_le_iff₀ (by positivity : 0 < 2 * log X ^ 4)).mpr ?_⟩
  linarith

#print axioms actual_mixed_curvature_tendsto
#print axioms actual_mixed_curvature_lower
private theorem paid_range_rate {barL range : ℝ → ℝ} {rho lambda : ℝ}
    (hrho : 0 < rho) (hlambda : 0 < lambda)
    (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0))
    (hpaid : ∀ᶠ X : ℝ in atTop,
      rho * exp (lambda * barL X) * barL X ^ 2 ≤ range X) :
    (∀ᶠ X : ℝ in atTop, 0 < range X) ∧
      Tendsto (fun X => log X ^ 4 / range X) atTop (𝓝 0) := by
  have hbar : Tendsto barL atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_log_atTop.eventually_ge_atTop (b + 1),
      hclose.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))]
      with X hX hc
    linarith
  have hratio : Tendsto (fun X => log X / barL X) atTop (𝓝 1) := by
    have hh := hclose.div_atTop tendsto_log_atTop
    have hh' : Tendsto (fun X => barL X / log X) atTop (𝓝 1) := by
      have hh'' := (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hh
      simp only [add_zero] at hh''
      apply hh''.congr'
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      field_simp [(log_pos hX).ne']
      <;> ring
    simpa only [inv_one, inv_div] using hh'.inv₀ one_ne_zero
  have hsmall : Tendsto (fun X => barL X ^ 2 / exp (lambda * barL X)) atTop (𝓝 0) :=
    ((isLittleO_pow_exp_pos_mul_atTop 2 hlambda).tendsto_div_nhds_zero).comp hbar
  have hbound : Tendsto (fun X => (log X / barL X) ^ 4 *
      (barL X ^ 2 / exp (lambda * barL X)) / rho) atTop (𝓝 0) := by
    simpa using ((hratio.pow 4).mul hsmall).div_const rho
  have hpos : ∀ᶠ X : ℝ in atTop, 0 < range X := by
    filter_upwards [hpaid, hbar.eventually_gt_atTop 0] with X hX hb
    exact lt_of_lt_of_le (by positivity) hX
  refine ⟨hpos, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · filter_upwards [hpos] with X hX
    exact div_nonneg (by positivity) hX.le
  · filter_upwards [hpaid, hbar.eventually_gt_atTop 0] with X hX hb
    have hp : 0 < rho * exp (lambda * barL X) * barL X ^ 2 := by positivity
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ log X ^ 4) hp hX
    convert hh using 1
    field_simp [hrho.ne', hb.ne', (exp_pos (lambda * barL X)).ne']
    <;> ring

/-- This normalized identity and error bound precede any bound on the integer
labels. In particular it imposes no upper bound on the denominator h. -/
private theorem normalized_determinant_positive {t w z h p u v e3 eU eV : ℝ}
    (hh : 1 ≤ h) (he3 : 0 ≤ e3) (heU : 0 ≤ eU) (heV : 0 ≤ eV)
    (h3 : |h * t - p| ≤ e3) (hU : |h * w - u| ≤ eU)
    (hV : |h * z - v| ≤ eV)
    (harea : |t - 1| * eU + |w| * e3 + e3 * eU + eV < (t - 1) * w - z) :
    0 < (p - h) * u - h * v := by
  have hh0 : 0 < h := by linarith
  let x := (h * t - p) / h
  let y := (h * w - u) / h
  let r := (h * z - v) / h
  have hx : |x| ≤ e3 := by
    dsimp [x]
    rw [abs_div, abs_of_pos hh0]
    exact (div_le_iff₀ hh0).mpr (h3.trans (le_mul_of_one_le_right he3 hh))
  have hy : |y| ≤ eU := by
    dsimp [y]
    rw [abs_div, abs_of_pos hh0]
    exact (div_le_iff₀ hh0).mpr (hU.trans (le_mul_of_one_le_right heU hh))
  have hr : |r| ≤ eV := by
    dsimp [r]
    rw [abs_div, abs_of_pos hh0]
    exact (div_le_iff₀ hh0).mpr (hV.trans (le_mul_of_one_le_right heV hh))
  have hid : ((p - h) * u - h * v) / h ^ 2 =
      ((t - 1) * w - z) - (t - 1) * y - w * x + x * y + r := by
    dsimp [x, y, r]
    field_simp
    <;> ring
  have herror : |((p - h) * u - h * v) / h ^ 2 - ((t - 1) * w - z)| ≤
      |t - 1| * eU + |w| * e3 + e3 * eU + eV := by
    rw [hid]
    have hi : ((t - 1) * w - z - (t - 1) * y - w * x + x * y + r) -
        ((t - 1) * w - z) = -((t - 1) * y) + -(w * x) + x * y + r := by ring
    rw [hi]
    calc
      _ ≤ |(t - 1) * y| + |w * x| + |x * y| + |r| := by
        calc
          _ ≤ |-((t - 1) * y) + -(w * x) + x * y| + |r| := abs_add_le _ _
          _ ≤ (|-((t - 1) * y) + -(w * x)| + |x * y|) + |r| := by
            gcongr; exact abs_add_le _ _
          _ ≤ _ := by
            have hb := abs_add_le (-((t - 1) * y)) (-(w * x))
            simp only [abs_neg] at hb
            linarith
      _ ≤ _ := by
        simp only [abs_mul]
        gcongr
  have hpositive : 0 < ((p - h) * u - h * v) / h ^ 2 := by
    have hb := (abs_le.mp herror).1
    linarith
  exact (div_pos_iff_of_pos_right (pow_pos hh0 2)).mp hpositive

/-- External actual paid-growth suppliers imply one eventual threshold before
all four integer labels. This is a necessary sign restriction only: positive
determinants survive, and no original clock or paid certificate is produced. -/
theorem eventual_integer_determinant_positive
    (beta C0 rho3 rho8 rho12 : ℝ) (barL A3 : ℝ → ℝ) (M N : ℝ → ℕ)
    (hbeta : 37 / 50 ≤ beta) (hbeta' : beta < 3 / 4) (hC0 : 0 ≤ C0)
    (hrho3 : 0 < rho3) (hrho8 : 0 < rho8) (hrho12 : 0 < rho12)
    (hclose : Tendsto (fun X => barL X - log X) atTop (𝓝 0))
    (hpaid3 : ∀ᶠ X : ℝ in atTop,
      rho3 * exp (((1 - beta) / 3 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤ A3 X)
    (hpaid8 : ∀ᶠ X : ℝ in atTop,
      rho8 * exp (((1 - beta) / 8 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (M X : ℝ) + 1)
    (hpaid12 : ∀ᶠ X : ℝ in atTop,
      rho12 * exp (((1 - beta) / 12 - (3 / 2 - 2 * beta)) * barL X) * barL X ^ 2 ≤
        (N X : ℝ) + 1) :
    ∀ᶠ X : ℝ in atTop, ∀ h p u v : ℤ, 1 ≤ h →
      |(h : ℝ) * theta X - p| ≤ C0 / A3 X →
      |(h : ℝ) * U X - u| ≤ C0 / ((M X : ℝ) + 1) →
      |(h : ℝ) * V X - v| ≤ C0 / ((N X : ℝ) + 1) →
      1 ≤ (p - h) * u - h * v := by
  have hl3 : 1 / 15 ≤ (1 - beta) / 3 - (3 / 2 - 2 * beta) := by linarith
  have hl8 : 1 / 80 ≤ (1 - beta) / 8 - (3 / 2 - 2 * beta) := by linarith
  have hl12 : 1 / 600 ≤ (1 - beta) / 12 - (3 / 2 - 2 * beta) := by linarith
  obtain ⟨hpos3, hr3⟩ := paid_range_rate hrho3 (by linarith :
    0 < (1 - beta) / 3 - (3 / 2 - 2 * beta)) hclose hpaid3
  obtain ⟨_, hr8⟩ := paid_range_rate hrho8 (by linarith :
    0 < (1 - beta) / 8 - (3 / 2 - 2 * beta)) hclose hpaid8
  obtain ⟨_, hr12⟩ := paid_range_rate hrho12 (by linarith :
    0 < (1 - beta) / 12 - (3 / 2 - 2 * beta)) hclose hpaid12
  let e3 := fun X => C0 / A3 X
  let eU := fun X => C0 / ((M X : ℝ) + 1)
  let eV := fun X => C0 / ((N X : ℝ) + 1)
  have he3 : Tendsto (fun X => log X ^ 4 * e3 X) atTop (𝓝 0) := by
    simpa [e3, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr3.const_mul C0
  have heU : Tendsto (fun X => log X ^ 4 * eU X) atTop (𝓝 0) := by
    simpa [eU, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr8.const_mul C0
  have heV : Tendsto (fun X => log X ^ 4 * eV X) atTop (𝓝 0) := by
    simpa [eV, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr12.const_mul C0
  have heU0 : Tendsto eU atTop (𝓝 0) := by
    have hh := heU.mul ((tendsto_const_nhds.div_atTop tendsto_log_atTop :
      Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0)).pow 4)
    norm_num only [zero_pow (by norm_num : 4 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    field_simp [(log_pos hX).ne']
  have h2 : Tendsto (d 2) atTop (𝓝 (log 2)) := fixed_layer_root_offset_tendsto (by norm_num)
  have h3 : Tendsto (d 3) atTop (𝓝 (log 3)) := fixed_layer_root_offset_tendsto (by norm_num)
  have h4 : Tendsto (d 4) atTop (𝓝 (log 4)) := fixed_layer_root_offset_tendsto (by norm_num)
  have h8 : Tendsto (d 8) atTop (𝓝 (log 8)) := fixed_layer_root_offset_tendsto (by norm_num)
  have hlog2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ht : Tendsto theta atTop (𝓝 (log 3 / log 2)) := h3.div h2 hlog2
  have hu : Tendsto U atTop (𝓝 ((3 * log 4 - log 8 - 3 * log 2) / log 2)) :=
    (((h4.const_mul 3).sub h8).sub (h2.const_mul 3)).div h2 hlog2
  let E := fun X => |theta X - 1| * eU X + |U X| * e3 X + e3 X * eU X + eV X
  have hE : Tendsto (fun X => log X ^ 4 * E X) atTop (𝓝 0) := by
    have hh := (((ht.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))).abs.mul heU).add
      (hu.abs.mul he3)).add (he3.mul heU0) |>.add heV
    simp only [mul_zero, zero_mul, add_zero] at hh
    convert hh using 1
    funext X
    dsimp [E]
    ring
  have hsmallE := hE.eventually
    (eventually_lt_nhds (show (0 : ℝ) < kappa / 4 by linarith [kappa_pos]))
  filter_upwards [actual_mixed_curvature_lower, hsmallE, hpos3] with X hcurve hsmallX hA3
  intro h p u v hh h3X hUX hVX
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have he3X : 0 ≤ e3 X := div_nonneg hC0 hA3.le
  have heUX : 0 ≤ eU X := div_nonneg hC0 (by positivity)
  have heVX : 0 ≤ eV X := div_nonneg hC0 (by positivity)
  have hg : E X < A X := by
    have hL : 0 < log X ^ 4 := pow_pos hcurve.1 4
    have hb := (div_le_iff₀ (show 0 < 2 * log X ^ 4 by positivity)).mp hcurve.2
    nlinarith [kappa_pos]
  have hp := normalized_determinant_positive hhR he3X heUX heVX h3X hUX hVX hg
  have hZ : (0 : ℤ) < (p - h) * u - h * v := by exact_mod_cast hp
  omega

#print axioms eventual_integer_determinant_positive

end D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
