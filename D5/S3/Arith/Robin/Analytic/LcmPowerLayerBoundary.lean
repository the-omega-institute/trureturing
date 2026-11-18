/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform comparison of the layer boundaries of the LCM power function. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

/-! A common threshold for every natural layer of the LCM power function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
open D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary

private lemma log_difference_lt {κ h : ℝ} (hκ : 1 < κ) (hh : 0 < h) :
    logPowerDifference κ h < κ * h := by
  calc
    logPowerDifference κ h < Real.log ((1 + h) ^ κ) := by
      apply Real.log_lt_log (difference_pos hκ hh.le)
      exact sub_lt_self _ (Real.rpow_pos_of_pos hh _)
    _ = κ * Real.log (1 + h) := Real.log_rpow (by linarith) _
    _ < κ * h := by
      apply mul_lt_mul_of_pos_left _ (by linarith)
      have hi := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + h)
        (by linarith : 1 + h ≠ 1)
      linarith

private lemma increment_lower {κ s h : ℝ} (hκ : 1 < κ) (hh : 0 < h)
    (hsh : h ≤ s) :
    h * deriv (logPowerDifference κ) s ≤
      logPowerDifference κ s - logPowerDifference κ (s - h) := by
  have hs : 0 < s := hh.trans_le hsh
  have hi := (logPowerDifference_concavity hκ).2.1.deriv_le_slope
    (show s - h ∈ Ici 0 by exact sub_nonneg.mpr hsh)
    (show s ∈ Ici 0 by exact hs.le) (by linarith : s - h < s)
    (log_derivative hκ hs).differentiableAt
  rw [slope_def_field, show s - (s - h) = h by ring] at hi
  have := (le_div_iff₀ hh).mp hi
  nlinarith

private lemma layer_increment {κ y : ℝ} (hκ : 1 < κ) (hy : 1 < y)
    {n : ℕ} (hn : 1 ≤ n) :
    let q := y ^ n
    let s := (q - 1) / (q * (y - 1))
    lcmPowerF κ y n =
      (logPowerDifference κ s - logPowerDifference κ (s - 1 / q)) / (κ * Real.log y) := by
  dsimp only
  let q := y ^ n
  let A := q * (y - 1)
  let s := (q - 1) / A
  let h := 1 / q
  have hy0 : 0 < y := by linarith
  have hqy : y ≤ q := le_self_pow₀ hy.le (by omega)
  have hq : 0 < q := pow_pos hy0 _
  have hA : 0 < A := mul_pos hq (sub_pos.mpr hy)
  have hs : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hsh : s - h = (q - y) / A := by
    dsimp [s, h, A]
    field_simp
    <;> ring
  have hsh0 : 0 ≤ s - h := by rw [hsh]; exact div_nonneg (sub_nonneg.mpr hqy) hA.le
  have he₁ : q * y - 1 = A * (1 + s) := by
    dsimp [s]; field_simp; dsimp [A]; ring
  have he₂ : q - 1 = A * s := by dsimp [s]; field_simp
  have he₃ : q * y - y = A * (1 + (s - h)) := by
    rw [hsh]; field_simp; dsimp [A]; ring
  have he₄ : q - y = A * (s - h) := by rw [hsh]; field_simp
  have hnum : (q * y - 1) ^ κ - (q - 1) ^ κ = A ^ κ * powerDifference κ s := by
    rw [he₁, he₂, Real.mul_rpow hA.le (by linarith : 0 ≤ 1 + s),
      Real.mul_rpow hA.le hs]
    unfold powerDifference
    ring
  have hden : (q * y - y) ^ κ - (q - y) ^ κ = A ^ κ * powerDifference κ (s - h) := by
    rw [he₃, he₄, Real.mul_rpow hA.le (by linarith : 0 ≤ 1 + (s - h)),
      Real.mul_rpow hA.le hsh0]
    unfold powerDifference
    ring
  have hpow : y ^ ((n : ℝ) + 1) = q * y := by
    rw [Real.rpow_add hy0, Real.rpow_natCast, Real.rpow_one]
  unfold lcmPowerF
  rw [hpow, Real.rpow_natCast]
  change Real.log (((q * y - 1) ^ κ - (q - 1) ^ κ) /
    ((q * y - y) ^ κ - (q - y) ^ κ)) / (κ * Real.log y) = _
  rw [hnum, hden, mul_div_mul_left _ _ (Real.rpow_pos_of_pos hA κ).ne',
    Real.log_div (difference_pos hκ hs).ne' (difference_pos hκ hsh0).ne']
  rfl

private lemma first_layer_log {κ z : ℝ} (hκ : 1 < κ) (hz : 1 < z) :
    lcmPowerF κ z 1 = logPowerDifference κ (1 / z) / (κ * Real.log z) := by
  have hz0 : 0 < z := by linarith
  rw [F_one (by linarith) hz]
  unfold logPowerDifference powerDifference
  have he : 1 + 1 / z = (z + 1) / z := by field_simp
  rw [he, Real.div_rpow (by linarith : 0 ≤ z + 1) hz0.le,
    Real.div_rpow zero_le_one hz0.le, Real.one_rpow]
  congr 2
  ring

private lemma layer_sum_bound {y : ℝ} (hy : 1 < y) {n : ℕ} (hn : 1 ≤ n) :
    (y ^ n - 1) / (y ^ n * (y - 1)) ≤ (n : ℝ) / Real.log (y ^ n) := by
  have hy0 : 0 < y := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hq : 0 < y ^ n := pow_pos hy0 _
  have hym : 0 < y - 1 := sub_pos.mpr hy
  have hly := Real.log_pos hy
  calc
    (y ^ n - 1) / (y ^ n * (y - 1)) ≤ 1 / (y - 1) := by
      apply (div_le_div_iff₀ (mul_pos hq hym) hym).mpr
      nlinarith
    _ ≤ 1 / Real.log y := one_div_le_one_div_of_le hly
      (by linarith [Real.log_le_sub_one_of_pos hy0])
    _ = (n : ℝ) / Real.log (y ^ n) := by rw [Real.log_pow]; field_simp

private lemma elasticity_lower {κ v : ℝ} (hκ : 1 < κ) (hv : 0 < v) :
    κ * (v / (1 + v) - (v / (1 + v)) ^ κ) ≤
      v * deriv (logPowerDifference κ) v := by
  let r := v / (1 + v)
  have hr : 0 < r := div_pos hv (by linarith)
  have hr1 : r < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hrk : r ^ κ < r := Real.rpow_lt_self_of_lt_one hr hr1 hκ
  have hd : 0 < 1 - r ^ κ := by linarith
  have he : v * deriv (logPowerDifference κ) v =
      κ * (r - r ^ κ) / (1 - r ^ κ) := by
    rw [elasticity_formula hκ hv]
    change κ * (1 - 1 / ((1 - r ^ κ) / (1 - r))) = _
    field_simp
    <;> ring
  change κ * (r - r ^ κ) ≤ _
  rw [he]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_nonneg (show 0 ≤ κ * (r - r ^ κ) by positivity)
    (Real.rpow_pos_of_pos hr κ).le]

private lemma explicit_elasticity_bound {κ u : ℝ} (hκ : 1 < κ) (hu : 6 ≤ u)
    (hthreshold : ((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)) ≤ u) :
    κ < u * ((2 / u) * deriv (logPowerDifference κ) (2 / u)) := by
  have hu0 : 0 < u := by linarith
  have hκ0 : 0 < κ := by linarith
  have hk1 : 0 < κ - 1 := by linarith
  have hp : (2 : ℝ) ^ (κ + 1.01) ≤ u ^ (κ - 1) := by
    apply (Real.rpow_inv_le_iff_of_pos
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le hu0.le hk1).mp
    simpa only [one_div] using hthreshold
  have hstrict : 2 * (2 : ℝ) ^ κ < u ^ (κ - 1) := by
    calc
      2 * (2 : ℝ) ^ κ = (2 : ℝ) ^ (κ + 1) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]; ring
      _ < (2 : ℝ) ^ (κ + 1.01) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ ≤ _ := hp
  have hquot : u * ((2 : ℝ) / u) ^ κ = (2 : ℝ) ^ κ / u ^ (κ - 1) := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hu0.le,
      Real.rpow_sub_one hu0.ne']
    field_simp
  have hloss : u * ((2 : ℝ) / u) ^ κ < 1 / 2 := by
    rw [hquot]
    apply (div_lt_iff₀ (Real.rpow_pos_of_pos hu0 _)).mpr
    linarith
  let r := (2 : ℝ) / (u + 2)
  have hr : 0 < r := div_pos (by norm_num) (by linarith)
  have hrle : r ≤ 2 / u := by
    apply (div_le_div_iff₀ (by linarith : 0 < u + 2) hu0).mpr
    linarith
  have hmain : 3 / 2 ≤ u * r := by
    dsimp [r]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by linarith : 0 < u + 2)).mpr
    linarith
  have hloss' : u * r ^ κ < 1 / 2 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrle hκ0.le) hu0.le).trans_lt hloss
  have he : (2 / u) / (1 + 2 / u) = r := by
    dsimp [r]
    field_simp
    <;> ring
  have hb := mul_le_mul_of_nonneg_left (elasticity_lower hκ
    (div_pos (by norm_num : (0 : ℝ) < 2) hu0)) hu0.le
  rw [he] at hb
  nlinarith [mul_pos hκ0 (show 0 < u * r - u * r ^ κ - 1 by linarith)]

private lemma explicit_derivative_bound {κ u n s : ℝ} (hκ : 1 < κ)
    (hu : 6 ≤ u) (hthreshold : ((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)) ≤ u)
    (hn : 2 ≤ n) (hs : 0 < s) (hsu : s ≤ n / u) :
    κ < n * deriv (logPowerDifference κ) s := by
  have hu0 : 0 < u := by linarith
  have hw : 0 < n / u := div_pos (by linarith) hu0
  have hv : 0 < 2 / u := div_pos (by norm_num) hu0
  have ha := (logPowerDifference_concavity hκ).1.concaveOn.antitoneOn_deriv
    (fun t ht => (log_derivative hκ ht).differentiableAt)
  have hd := ha hs hw hsu
  have hm := (elasticity_strictMono hκ).monotoneOn hv hw
    ((div_le_div_iff_of_pos_right hu0).mpr hn)
  have hb := explicit_elasticity_bound hκ hu hthreshold
  have hm' := mul_le_mul_of_nonneg_left hm hu0.le
  have he : u * (n / u * deriv (logPowerDifference κ) (n / u)) =
      n * deriv (logPowerDifference κ) (n / u) := by field_simp
  rw [he] at hm'
  exact (hb.trans_le hm').trans_le (mul_le_mul_of_nonneg_left hd (by linarith))

/-- The specified all-layer threshold from the explicit layer-boundary estimate. -/
theorem layer_boundary_explicit {κ : ℝ} (hκ : 1 < κ) {x : ℝ}
    (hx : Real.exp (max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)))) ≤ x)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    lcmPowerF κ x 1 < lcmPowerF κ (x ^ ((1 : ℝ) / ℓ)) ℓ := by
  have hu : max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1))) ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hx
  have hu6 : 6 ≤ Real.log x := (le_max_left _ _).trans hu
  have huthreshold : ((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)) ≤ Real.log x :=
    (le_max_right _ _).trans hu
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (show 0 < max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1))) by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) (le_max_left _ _))).trans_le hx
  have hx0 : 0 < x := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  let y := x ^ ((1 : ℝ) / ℓ)
  have hy : 1 < y := Real.one_lt_rpow hx1 (one_div_pos.mpr hℓ0)
  have hy0 : 0 < y := by linarith
  have hqeq : y ^ ℓ = x := by
    dsimp [y]
    simpa only [one_div] using Real.rpow_inv_natCast_pow hx0.le (show ℓ ≠ 0 by omega)
  let q := y ^ ℓ
  let s := (q - 1) / (q * (y - 1))
  let h := 1 / q
  have hq : 0 < q := pow_pos hy0 _
  have hq1 : 1 < q := by simpa only [q, hqeq] using hx1
  have hs : 0 < s := div_pos (sub_pos.mpr hq1) (mul_pos hq (sub_pos.mpr hy))
  have hh : 0 < h := one_div_pos.mpr hq
  have hsh : h ≤ s := by
    have hqy : y ≤ q := le_self_pow₀ hy.le (by omega)
    apply sub_nonneg.mp
    have he : s - h = (q - y) / (q * (y - 1)) := by
      dsimp [s, h]; field_simp; ring
    rw [he]
    exact div_nonneg (sub_nonneg.mpr hqy) (mul_pos hq (sub_pos.mpr hy)).le
  have hsbound : s ≤ (ℓ : ℝ) / Real.log x := by
    simpa only [s, q, hqeq] using layer_sum_bound hy (show 1 ≤ ℓ by omega)
  have hd := explicit_derivative_bound hκ hu6 huthreshold hℓ2 hs hsbound
  have hi := increment_lower hκ hh hsh
  have ht : logPowerDifference κ h <
      (ℓ : ℝ) * (logPowerDifference κ s - logPowerDifference κ (s - h)) := by
    calc
      logPowerDifference κ h < κ * h := log_difference_lt hκ hh
      _ < (ℓ : ℝ) * (h * deriv (logPowerDifference κ) s) := by
        nlinarith [mul_pos hh (sub_pos.mpr hd)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hℓ0.le
  have hf₁ : lcmPowerF κ x 1 = logPowerDifference κ h / (κ * Real.log x) := by
    simpa only [h, q, hqeq] using first_layer_log hκ hx1
  have hfℓ : lcmPowerF κ y ℓ =
      (logPowerDifference κ s - logPowerDifference κ (s - h)) / (κ * Real.log y) :=
    layer_increment hκ hy (by omega)
  change lcmPowerF κ x 1 < lcmPowerF κ y ℓ
  rw [hf₁, hfℓ]
  apply (div_lt_div_iff₀ (mul_pos (by linarith : 0 < κ) (Real.log_pos hx1))
    (mul_pos (by linarith : 0 < κ) (Real.log_pos hy))).mpr
  have hlog : Real.log x = (ℓ : ℝ) * Real.log y := by rw [← hqeq, Real.log_pow]
  rw [hlog]
  nlinarith [mul_lt_mul_of_pos_right ht (mul_pos (by linarith : 0 < κ) (Real.log_pos hy))]

private def layerSum : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, t => layerSum n t + t ^ (n + 1)

private def layerSlope : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, t => layerSlope n t + (n + 1 : ℝ) * t ^ n

private lemma layerSum_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ layerSum n t := by
  induction n with
  | zero => simp [layerSum]
  | succ n ih => exact add_nonneg ih (pow_nonneg ht _)

private lemma layerSum_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < layerSum (n + 1) t :=
  add_pos_of_nonneg_of_pos (layerSum_nonneg n ht.le) (pow_pos ht _)

private lemma layerSlope_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < layerSlope (n + 1) t := by
  induction n with
  | zero => simp [layerSlope]
  | succ n ih =>
    exact add_pos ih (mul_pos (by positivity) (pow_pos ht _))

private lemma layerSum_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (layerSum n) (layerSlope n t) t := by
  induction n with
  | zero => simpa only [layerSum, layerSlope] using hasDerivAt_const t (0 : ℝ)
  | succ n ih =>
    simpa only [layerSum, layerSlope, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel_right, mul_one, id_eq] using
      ih.fun_add ((hasDerivAt_id t).fun_pow (n + 1))

private lemma layerSlope_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t * layerSlope n t ≤ (n : ℝ) * layerSum n t := by
  induction n with
  | zero => simp [layerSum, layerSlope]
  | succ n ih =>
    simp only [layerSum, layerSlope, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    nlinarith [layerSum_nonneg n ht]

private lemma layerSlope_ratio (n : ℕ) {t : ℝ} (ht : 0 < t) :
    layerSlope n t * layerSum (n + 1) t ≤
      layerSlope (n + 1) t * layerSum n t := by
  have hb := mul_le_mul_of_nonneg_right (layerSlope_bound n ht.le) (pow_nonneg ht.le n)
  have hp := mul_nonneg (layerSum_nonneg n ht.le) (pow_nonneg ht.le n)
  simp only [layerSum, layerSlope, pow_succ]
  nlinarith

private lemma layer_increment_derivative_pos {κ : ℝ} (hκ : 1 < κ)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ d : ℝ, HasDerivAt (fun t =>
      logPowerDifference κ (layerSum (n + 1) t) -
        logPowerDifference κ (layerSum n t)) d t ∧ 0 < d := by
  cases n with
  | zero =>
    refine ⟨deriv (logPowerDifference κ) t, ?_, log_deriv_pos hκ ht⟩
    have hd := ((log_derivative hκ ht).sub_const (logPowerDifference κ 0))
    simpa only [layerSum, zero_add, pow_one, ← (log_derivative hκ ht).deriv] using hd
  | succ n =>
    let a := layerSum (n + 1) t
    let b := layerSum (n + 1 + 1) t
    let d := layerSlope (n + 1) t
    let e := layerSlope (n + 1 + 1) t
    have ha : 0 < a := layerSum_pos n ht
    have hb : 0 < b := layerSum_pos (n + 1) ht
    have hd : 0 < d := layerSlope_pos n ht
    have hab : a < b := by
      change layerSum (n + 1) t < layerSum (n + 1) t + t ^ (n + 1 + 1)
      exact lt_add_of_pos_right _ (pow_pos ht _)
    have he : d / a ≤ e / b :=
      (div_le_div_iff₀ ha hb).mpr (layerSlope_ratio (n + 1) ht)
    have hφ := elasticity_strictMono hκ ha hb hab
    have hφb : 0 < b * deriv (logPowerDifference κ) b :=
      mul_pos hb (log_deriv_pos hκ hb)
    have hprod : deriv (logPowerDifference κ) a * d <
        deriv (logPowerDifference κ) b * e := by
      calc
        deriv (logPowerDifference κ) a * d =
            (a * deriv (logPowerDifference κ) a) * (d / a) := by
          field_simp [ha.ne']
        _ < (b * deriv (logPowerDifference κ) b) * (d / a) :=
          mul_lt_mul_of_pos_right hφ (div_pos hd ha)
        _ ≤ (b * deriv (logPowerDifference κ) b) * (e / b) :=
          mul_le_mul_of_nonneg_left he hφb.le
        _ = deriv (logPowerDifference κ) b * e := by field_simp [hb.ne']
    refine ⟨deriv (logPowerDifference κ) b * e -
      deriv (logPowerDifference κ) a * d, ?_, sub_pos.mpr hprod⟩
    have hda := ((log_derivative hκ ha).comp t (layerSum_derivative (n + 1) t))
    have hdb := ((log_derivative hκ hb).comp t (layerSum_derivative (n + 1 + 1) t))
    simpa only [Function.comp_def, d, e,
      ← (log_derivative hκ ha).deriv, ← (log_derivative hκ hb).deriv]
      using hdb.fun_sub hda

private lemma layer_increment_strictMono {κ : ℝ} (hκ : 1 < κ) (n : ℕ) :
    StrictMonoOn (fun t => logPowerDifference κ (layerSum (n + 1) t) -
      logPowerDifference κ (layerSum n t)) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht =>
      ((layer_increment_derivative_pos hκ n ht).choose_spec.1).continuousAt.continuousWithinAt)
  intro t ht
  have ht : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
  obtain ⟨d, hd, hd0⟩ := layer_increment_derivative_pos hκ n ht
  rwa [hd.deriv]

private lemma layer_increment_pos {κ : ℝ} (hκ : 1 < κ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    0 < logPowerDifference κ (layerSum (n + 1) t) -
      logPowerDifference κ (layerSum n t) := by
  cases n with
  | zero =>
    have hi := increment_lower hκ ht (le_refl t)
    have hz := (logPowerDifference_concavity hκ).2.2
    simp only [sub_self, hz, sub_zero] at hi
    simpa only [layerSum, zero_add, pow_one, hz, sub_zero] using
      (mul_pos ht (log_deriv_pos hκ ht)).trans_le hi
  | succ n =>
    apply sub_pos.mpr
    apply log_strictMono hκ (layerSum_pos n ht) (layerSum_pos (n + 1) ht)
    change layerSum (n + 1) t < layerSum (n + 1) t + t ^ (n + 1 + 1)
    exact lt_add_of_pos_right _ (pow_pos ht _)

private lemma layerSum_inverse {y : ℝ} (hy : 1 < y) (n : ℕ) :
    layerSum n (1 / y) = (y ^ n - 1) / (y ^ n * (y - 1)) := by
  have hy0 : y ≠ 0 := (lt_trans zero_lt_one hy).ne'
  have hym : y - 1 ≠ 0 := (sub_pos.mpr hy).ne'
  induction n with
  | zero => simp [layerSum]
  | succ n ih =>
    rw [layerSum, ih, one_div_pow, pow_succ]
    field_simp [hy0, hym]
    ring

private lemma F_layerSum {κ y : ℝ} (hκ : 1 < κ) (hy : 1 < y) (n : ℕ) :
    lcmPowerF κ y (n + 1 : ℕ) =
      (logPowerDifference κ (layerSum (n + 1) (1 / y)) -
        logPowerDifference κ (layerSum n (1 / y))) / (κ * Real.log y) := by
  rw [layer_increment hκ hy (show 1 ≤ n + 1 by omega)]
  rw [← layerSum_inverse hy (n + 1)]
  have he : layerSum (n + 1) (1 / y) - 1 / y ^ (n + 1) = layerSum n (1 / y) := by
    rw [layerSum, one_div_pow]
    ring
  rw [he]

/-- Every positive natural layer of F strictly decreases with its base above one. -/
theorem F_strictAntiOn {κ : ℝ} (hκ : 1 < κ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    StrictAntiOn (fun y : ℝ => lcmPowerF κ y ℓ) (Ioi 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show ℓ ≠ 0 by omega)
  intro x hx y hy hxy
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hκ0 : 0 < κ := by linarith
  have hi := layer_increment_strictMono hκ n (one_div_pos.mpr hy0)
    (one_div_pos.mpr hx0) (one_div_lt_one_div_of_lt hx0 hxy)
  change lcmPowerF κ y (n + 1 : ℕ) < lcmPowerF κ x (n + 1 : ℕ)
  rw [F_layerSum hκ hy n, F_layerSum hκ hx n]
  calc
    (logPowerDifference κ (layerSum (n + 1) (1 / y)) -
        logPowerDifference κ (layerSum n (1 / y))) / (κ * Real.log y) <
        (logPowerDifference κ (layerSum (n + 1) (1 / x)) -
          logPowerDifference κ (layerSum n (1 / x))) / (κ * Real.log y) :=
      div_lt_div_of_pos_right hi (mul_pos hκ0 (Real.log_pos hy))
    _ ≤ _ := div_le_div_of_nonneg_left (layer_increment_pos hκ n (one_div_pos.mpr hx0)).le
      (mul_pos hκ0 (Real.log_pos hx))
      (mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxy.le) hκ0.le)

/-- Equal layer values place the source layer variable beyond the root boundary. -/
theorem layer_boundary_xl {κ : ℝ} (hκ : 1 < κ) {x x' : ℝ}
    (hx : Real.exp (max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)))) ≤ x)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hx' : 1 < x')
    (h : lcmPowerF κ x' ℓ = lcmPowerF κ x 1) :
    x ^ ((1 : ℝ) / ℓ) < x' := by
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr
    (show 0 < max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1))) from
      lt_of_lt_of_le (by norm_num) (le_max_left _ _))).trans_le hx
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hy : 1 < x ^ ((1 : ℝ) / ℓ) :=
    Real.one_lt_rpow hx1 (one_div_pos.mpr hℓ0)
  have hb := layer_boundary_explicit hκ hx hℓ
  by_contra hn
  have ha := (F_strictAntiOn hκ (show 1 ≤ ℓ by omega)).antitoneOn hx' hy
    (le_of_not_gt hn)
  rw [h] at ha
  exact (not_lt_of_ge ha) hb

/-- Fan–Kobayashi–Molnar Remark 5.5: one threshold works for all layer bases. -/
theorem layer_boundary_uniform {κ : ℝ} (hκ : 1 < κ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ x' : ℝ, 1 < x' →
      lcmPowerF κ x' ℓ = lcmPowerF κ x 1 → x ^ ((1 : ℝ) / ℓ) < x' := by
  refine ⟨Real.exp (max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)))), ?_⟩
  intro x hx ℓ hℓ x' hx' h
  exact layer_boundary_xl hκ hx hℓ hx' h

end D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
