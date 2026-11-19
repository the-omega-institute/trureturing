/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real power inequalities and comparison of the LCM power function. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity
import D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The all-parameter power inequality and its logarithmic comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open D5.S3.Arith.Robin.Analytic.LcmPowerLogConcavity

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

private lemma decreasing_increment {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Ioi 0) f)
    {h s : ℝ} (hh : 0 < h) (hs : h < s) :
    f (s + h) - f s < f (2 * h) - f h := by
  have hs0 : 0 < s := hh.trans hs
  rcases le_total (2 * h) s with he | he
  · have hi := D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum.strictConcave_symmetric_sum
      hf (r := (s + 2 * h) / 2) (s := (s - 2 * h) / 2) (t := s / 2)
      (by linarith) (by linarith) (by linarith)
    have hi' : f h + f (s + h) < f (2 * h) + f s := by
      convert hi using 1 <;> congr 1 <;> ring
    linarith
  · have hi := D5.S3.Analytic.Convexity.StrictConcaveSymmetricSum.strictConcave_symmetric_sum
      hf (r := (s + 2 * h) / 2) (s := (2 * h - s) / 2) (t := s / 2)
      (by linarith) (by linarith) (by linarith)
    have hi' : f h + f (s + h) < f s + f (2 * h) := by
      convert hi using 1 <;> congr 1 <;> ring
    linarith

/-- The core all-parameter inequality. -/
theorem lemma415_core {κ y : ℝ} (hκ : 1 < κ) (hy : 1 < y) :
    (((y ^ (2 : ℝ) + 2) ^ κ - 2 ^ κ) * ((y + 1) ^ κ - 1) ^ (2 : ℝ) : ℝ) >
      ((y ^ (2 : ℝ) + y + 1) ^ κ - (y + 1) ^ κ) ^ (2 : ℝ) := by
  simp only [Real.rpow_two]
  have hy0 : 0 < y := by linarith
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy0
  let s : ℝ := 1 / y
  let h : ℝ := 1 / y ^ 2
  have hh : 0 < h := one_div_pos.mpr hy2
  have hs : h < s := by
    dsimp [h, s]
    apply one_div_lt_one_div_of_lt hy0
    nlinarith
  obtain ⟨hc, hc0, hz⟩ := logPowerDifference_concavity hκ
  have hi := decreasing_increment hc hh hs
  have hm := hc0.2 (show (0 : ℝ) ∈ Ici 0 by simp)
    (show 2 * h ∈ Ici 0 by change 0 ≤ 2 * h; linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, hz] at hm
  have hmarg : (1 / 2 : ℝ) * (2 * h) = h := by ring
  rw [hmarg] at hm
  have hlogs : 2 * logPowerDifference κ (s + h) <
      logPowerDifference κ (2 * h) + 2 * logPowerDifference κ s := by linarith
  have cp (t : ℝ) (ht : 0 ≤ t) : 0 < powerDifference κ t :=
    sub_pos.mpr (Real.rpow_lt_rpow ht (by linarith) (by linarith))
  have cs := cp s (by linarith)
  have ch := cp (2 * h) (by linarith)
  have csh := cp (s + h) (by linarith)
  have hnorm : (powerDifference κ (s + h)) ^ 2 <
      powerDifference κ (2 * h) * (powerDifference κ s) ^ 2 := by
    apply (Real.log_lt_log_iff (sq_pos_of_pos csh) (mul_pos ch (sq_pos_of_pos cs))).mp
    rw [Real.log_mul ch.ne' (sq_pos_of_pos cs).ne', Real.log_pow, Real.log_pow]
    exact hlogs
  have scale (p t : ℝ) (hp : 0 < p) (ht : 0 ≤ t) :
      p ^ κ * powerDifference κ t = (p * (1 + t)) ^ κ - (p * t) ^ κ := by
    rw [Real.mul_rpow hp.le (by linarith : 0 ≤ 1 + t), Real.mul_rpow hp.le ht]
    unfold powerDifference
    ring
  have hA : (y ^ 2 + 2) ^ κ - 2 ^ κ =
      (y ^ 2) ^ κ * powerDifference κ (2 * h) := by
    rw [scale _ _ hy2 (by linarith)]
    have he₁ : y ^ 2 * (1 + 2 * h) = y ^ 2 + 2 := by
      dsimp [h]; field_simp
    have he₂ : y ^ 2 * (2 * h) = 2 := by dsimp [h]; field_simp
    rw [he₁, he₂]
  have hC : (y + 1) ^ κ - 1 = y ^ κ * powerDifference κ s := by
    rw [scale _ _ hy0 (by linarith)]
    have he₁ : y * (1 + s) = y + 1 := by dsimp [s]; field_simp
    have he₂ : y * s = 1 := by dsimp [s]; field_simp
    rw [he₁, he₂, Real.one_rpow]
  have hB : (y ^ 2 + y + 1) ^ κ - (y + 1) ^ κ =
      (y ^ 2) ^ κ * powerDifference κ (s + h) := by
    rw [scale _ _ hy2 (by linarith)]
    have he₁ : y ^ 2 * (1 + (s + h)) = y ^ 2 + y + 1 := by
      dsimp [s, h]; field_simp; ring
    have he₂ : y ^ 2 * (s + h) = y + 1 := by dsimp [s, h]; field_simp
    rw [he₁, he₂]
  have hpow : (y ^ κ) ^ 2 = (y ^ 2) ^ κ := by
    simpa only [pow_two] using (Real.mul_rpow hy0.le hy0.le (z := κ)).symm
  rw [hA, hB, hC, mul_pow, hpow]
  convert mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos (Real.rpow_pos_of_pos hy2 κ)) using 1 <;> ring


noncomputable def lcmPowerF (κ x a : ℝ) : ℝ :=
  Real.log (((x ^ (a + 1) - 1) ^ κ - (x ^ a - 1) ^ κ) /
      ((x ^ (a + 1) - x) ^ κ - (x ^ a - x) ^ κ)) / (κ * Real.log x)

private lemma strict_rpow_add {κ a b : ℝ} (hκ : 1 < κ) (ha : 0 < a) (hb : 0 < b) :
    a ^ κ + b ^ κ < (a + b) ^ κ := by
  have hab : 0 < a + b := add_pos ha hb
  have hp : 0 < (a + b) ^ κ := Real.rpow_pos_of_pos hab _
  have h₁ := Real.rpow_lt_self_of_lt_one (div_pos ha hab)
    ((div_lt_one hab).mpr (by linarith)) hκ
  have h₂ := Real.rpow_lt_self_of_lt_one (div_pos hb hab)
    ((div_lt_one hab).mpr (by linarith)) hκ
  rw [Real.div_rpow ha.le hab.le] at h₁
  rw [Real.div_rpow hb.le hab.le] at h₂
  have hsum : (a ^ κ + b ^ κ) / (a + b) ^ κ < 1 := by
    rw [add_div]
    calc
      a ^ κ / (a + b) ^ κ + b ^ κ / (a + b) ^ κ < a / (a + b) + b / (a + b) := add_lt_add h₁ h₂
      _ = 1 := by field_simp
  exact (div_lt_one hp).mp hsum

private lemma F_two {κ y : ℝ} (hκ : 0 < κ) (hy : 1 < y) :
    lcmPowerF κ y 2 =
      Real.log (((y ^ 2 + y + 1) ^ κ - (y + 1) ^ κ) /
        (((y + 1) ^ κ - 1) * y ^ κ)) / (κ * Real.log y) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hym : 0 < y - 1 := sub_pos.mpr hy
  have hyp : 0 < y + 1 := by linarith
  have hq : 0 < y ^ 2 + y + 1 := by positivity
  have hc : 0 < (y + 1) ^ κ - 1 := by
    exact sub_pos.mpr (by simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) (by linarith : 1 < y + 1) hκ)
  have hm : 0 < (y - 1) ^ κ := Real.rpow_pos_of_pos hym _
  have hyκ : 0 < y ^ κ := Real.rpow_pos_of_pos hy0 _
  unfold lcmPowerF
  norm_num only [show (2:ℝ) + 1 = 3 by norm_num, Real.rpow_ofNat]
  congr 2
  rw [show y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) by ring,
    show y ^ 2 - 1 = (y - 1) * (y + 1) by ring,
    show y ^ 3 - y = (y - 1) * (y * (y + 1)) by ring,
    show y ^ 2 - y = (y - 1) * y by ring]
  rw [Real.mul_rpow hym.le hq.le, Real.mul_rpow hym.le hyp.le,
    Real.mul_rpow hym.le (mul_pos hy0 hyp).le, Real.mul_rpow hym.le hy0.le,
    Real.mul_rpow hy0.le hyp.le]
  field_simp [hm.ne', hyκ.ne', hc.ne']
  <;> ring

lemma F_one {κ x : ℝ} (hκ : 0 < κ) (hx : 1 < x) :
    lcmPowerF κ x 1 = Real.log (((x + 1) ^ κ - 1) / x ^ κ) / (κ * Real.log x) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxm : 0 < x - 1 := sub_pos.mpr hx
  have hxp : 0 < x + 1 := by linarith
  have hm : 0 < (x - 1) ^ κ := Real.rpow_pos_of_pos hxm _
  have hxκ : 0 < x ^ κ := Real.rpow_pos_of_pos hx0 _
  unfold lcmPowerF
  norm_num only [show (1:ℝ) + 1 = 2 by norm_num, Real.rpow_ofNat, Real.rpow_one,
    pow_one, sub_self, Real.zero_rpow hκ.ne', sub_zero]
  congr 2
  rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring,
    show x ^ 2 - x = (x - 1) * x by ring,
    Real.mul_rpow hxm.le hxp.le, Real.mul_rpow hxm.le hx0.le]
  field_simp [hm.ne', hxκ.ne']
  <;> ring

private lemma F_one_scaled {κ y : ℝ} (hκ : 0 < κ) (hy : 1 < y) (hy2 : 2 < y ^ 2) :
    lcmPowerF κ (y ^ 2 / 2) 1 =
      Real.log (((y ^ 2 + 2) ^ κ - (2:ℝ) ^ κ) / (y ^ 2) ^ κ) /
        (κ * Real.log (y ^ 2 / 2)) := by
  have hy0 : 0 < y := by linarith
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy0
  have hx : 1 < y ^ 2 / 2 := by nlinarith
  rw [F_one hκ hx]
  congr 2
  rw [show y ^ 2 / 2 + 1 = (y ^ 2 + 2) / 2 by ring,
    Real.div_rpow (by positivity : 0 ≤ y ^ 2 + 2) (by norm_num) κ,
    Real.div_rpow hy2.le (by norm_num) κ]
  have h2 : 0 < (2:ℝ) ^ κ := Real.rpow_pos_of_pos (by norm_num) _
  have hyκ : 0 < (y ^ 2) ^ κ := Real.rpow_pos_of_pos hy2 _
  field_simp [h2.ne', hyκ.ne']
  <;> ring

private theorem F_of_core {κ y : ℝ} (hκ : 1 < κ) (hy : 1 < y) (hy2 : 2 < y ^ 2)
    (hcore : (((y ^ 2 + 2) ^ κ - (2:ℝ) ^ κ) * ((y + 1) ^ κ - 1) ^ 2 : ℝ) >
      ((y ^ 2 + y + 1) ^ κ - (y + 1) ^ κ) ^ 2) :
    lcmPowerF κ y 2 < lcmPowerF κ (y ^ 2 / 2) 1 := by
  have hk0 : 0 < κ := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  let A : ℝ := (y ^ 2 + 2) ^ κ - (2:ℝ) ^ κ
  let B : ℝ := (y ^ 2 + y + 1) ^ κ - (y + 1) ^ κ
  let C : ℝ := (y + 1) ^ κ - 1
  let Y : ℝ := y ^ κ
  have hY : 0 < Y := Real.rpow_pos_of_pos hy0 _
  have hC : 0 < C := sub_pos.mpr (by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) (by linarith : 1 < y + 1) hk0)
  have hB : 0 < B := sub_pos.mpr
    (Real.rpow_lt_rpow (by linarith : 0 ≤ y + 1) (by nlinarith : y + 1 < y ^ 2 + y + 1) hk0)
  have hYs : (y ^ 2) ^ κ = Y ^ 2 := by
    change (y ^ 2) ^ κ = (y ^ κ) ^ 2
    rw [← Real.rpow_two y, ← Real.rpow_mul hy0.le, mul_comm (2:ℝ) κ,
      Real.rpow_mul hy0.le, Real.rpow_two]
  have hA : Y ^ 2 < A := by
    have hh := strict_rpow_add hκ (sq_pos_of_pos hy0) (by norm_num : (0:ℝ) < 2)
    rw [hYs] at hh
    dsimp [A]
    linarith
  have hCY : 0 < C * Y := mul_pos hC hY
  have hratio : (B / (C * Y)) ^ 2 < A / Y ^ 2 := by
    rw [div_pow]
    apply (div_lt_div_iff₀ (sq_pos_of_pos hCY) (sq_pos_of_pos hY)).mpr
    change B ^ 2 < A * C ^ 2 at hcore
    have hm := mul_lt_mul_of_pos_right hcore (sq_pos_of_pos hY)
    nlinarith
  have hlog : 2 * Real.log (B / (C * Y)) < Real.log (A / Y ^ 2) := by
    have hh := Real.log_lt_log (sq_pos_of_pos (div_pos hB hCY)) hratio
    rwa [Real.log_pow] at hh
  have hlogA : 0 < Real.log (A / Y ^ 2) :=
    Real.log_pos ((one_lt_div (sq_pos_of_pos hY)).mpr hA)
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlx : 0 < Real.log (y ^ 2 / 2) := Real.log_pos (by nlinarith)
  have hlxy : Real.log (y ^ 2 / 2) < 2 * Real.log y := by
    rw [Real.log_div (sq_pos_of_pos hy0).ne' (by norm_num), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  rw [F_two hk0 hy1, F_one_scaled hk0 hy hy2, hYs]
  change Real.log (B / (C * Y)) / (κ * Real.log y) <
    Real.log (A / Y ^ 2) / (κ * Real.log (y ^ 2 / 2))
  calc
    Real.log (B / (C * Y)) / (κ * Real.log y) <
        Real.log (A / Y ^ 2) / (2 * (κ * Real.log y)) := by
      apply (div_lt_div_iff₀ (mul_pos hk0 hly) (by positivity)).mpr
      nlinarith [mul_pos hk0 hly]
    _ < Real.log (A / Y ^ 2) / (κ * Real.log (y ^ 2 / 2)) := by
      exact div_lt_div_of_pos_left hlogA (mul_pos hk0 hlx) (by nlinarith)


lemma log_deriv_pos {κ t : ℝ} (hκ : 1 < κ) (ht : 0 < t) :
    0 < deriv (logPowerDifference κ) t := by
  rw [(log_derivative hκ ht).deriv]
  change 0 < κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) / powerDifference κ t
  exact div_pos (mul_pos (by linarith)
    (sub_pos.mpr (Real.rpow_lt_rpow ht.le (by linarith) (by linarith))))
    (difference_pos hκ ht.le)

lemma log_strictMono {κ : ℝ} (hκ : 1 < κ) :
    StrictMonoOn (logPowerDifference κ) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht => (log_derivative hκ ht).continuousAt.continuousWithinAt)
  simpa only [interior_Ioi, mem_Ioi] using (fun t ht => log_deriv_pos hκ ht)

lemma elasticity_formula {κ t : ℝ} (hκ : 1 < κ) (ht : 0 < t) :
    t * deriv (logPowerDifference κ) t =
      κ * (1 - 1 / ((1 - (t / (1 + t)) ^ κ) / (1 - t / (1 + t)))) := by
  have hq : 0 < 1 + t := by linarith
  have hp := difference_pos hκ ht.le
  rw [(log_derivative hκ ht).deriv]
  change t * (κ * ((1 + t) ^ (κ - 1) - t ^ (κ - 1)) /
    ((1 + t) ^ κ - t ^ κ)) = _
  rw [Real.rpow_sub_one hq.ne', Real.rpow_sub_one ht.ne', Real.div_rpow ht.le hq.le]
  have hqk := (Real.rpow_pos_of_pos hq κ).ne'
  change 0 < (1 + t) ^ κ - t ^ κ at hp
  field_simp [hq.ne', ht.ne', hqk, hp.ne']
  <;> ring

lemma elasticity_strictMono {κ : ℝ} (hκ : 1 < κ) :
    StrictMonoOn (fun t => t * deriv (logPowerDifference κ) t) (Ioi 0) := by
  intro t ht u hu htu
  change 0 < t at ht
  change 0 < u at hu
  dsimp only
  have hqt : 0 < 1 + t := by linarith [ht]
  have hqu : 0 < 1 + u := by linarith [hu]
  have hrt : 0 < t / (1 + t) := div_pos ht hqt
  have hru : 0 < u / (1 + u) := div_pos hu hqu
  have hrt1 : t / (1 + t) < 1 := (div_lt_one hqt).mpr (by linarith)
  have hru1 : u / (1 + u) < 1 := (div_lt_one hqu).mpr (by linarith)
  have hrr : t / (1 + t) < u / (1 + u) := by
    apply (div_lt_div_iff₀ hqt hqu).mpr
    nlinarith
  have hs := (strictConvexOn_rpow hκ).secant_strict_mono
    (a := 1) (by norm_num) hrt.le hru.le hrt1.ne hru1.ne hrr
  simp only [Real.one_rpow] at hs
  have hn (v : ℝ) : (v ^ κ - 1) / (v - 1) = (1 - v ^ κ) / (1 - v) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [hn, hn] at hs
  have hpos : 0 < (1 - (t / (1 + t)) ^ κ) / (1 - t / (1 + t)) := by
    apply div_pos _ (sub_pos.mpr hrt1)
    exact sub_pos.mpr (Real.rpow_lt_one hrt.le hrt1 (by linarith))
  rw [elasticity_formula hκ ht, elasticity_formula hκ hu]
  exact mul_lt_mul_of_pos_left (by linarith [one_div_lt_one_div_of_lt hpos hs])
    (by linarith)

private lemma increment_derivative {κ s : ℝ} (hκ : 1 < κ) (hs : 0 < s) :
    HasDerivAt (fun s => logPowerDifference κ (s + s ^ 2) - logPowerDifference κ s)
      ((1 + 2 * s) * deriv (logPowerDifference κ) (s + s ^ 2) -
        deriv (logPowerDifference κ) s) s := by
  have hsp : 0 < s + s ^ 2 := by positivity
  have hd := (log_derivative hκ hsp).comp s ((hasDerivAt_id s).add
    ((hasDerivAt_id s).pow 2))
  convert hd.sub (log_derivative hκ hs) using 1
  · rfl
  · simp only [← (log_derivative hκ hsp).deriv, ← (log_derivative hκ hs).deriv,
      id_eq, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 by rfl, pow_one, mul_one]
    ring

private lemma increment_strictMono {κ : ℝ} (hκ : 1 < κ) :
    StrictMonoOn (fun s => logPowerDifference κ (s + s ^ 2) - logPowerDifference κ s)
      (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun s hs => (increment_derivative hκ hs).continuousAt.continuousWithinAt)
  intro s hs
  have hs : 0 < s := by simpa using hs
  have hsp : 0 < s + s ^ 2 := by positivity
  have hi := elasticity_strictMono hκ hs hsp (by nlinarith [sq_pos_of_pos hs])
  have hp := log_deriv_pos hκ hsp
  rw [(increment_derivative hκ hs).deriv]
  have hm : 0 < s * ((1 + 2 * s) * deriv (logPowerDifference κ) (s + s ^ 2) -
      deriv (logPowerDifference κ) s) := by nlinarith [mul_pos (sq_pos_of_pos hs) hp]
  exact (mul_pos_iff_of_pos_left hs).mp hm

private lemma F_two_increment {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    lcmPowerF κ x 2 =
      (logPowerDifference κ (1 / x + (1 / x) ^ 2) - logPowerDifference κ (1 / x)) /
        (κ * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hs : 0 < 1 / x := one_div_pos.mpr hx0
  have hsp : 0 < 1 / x + (1 / x) ^ 2 := by positivity
  have scale (p t : ℝ) (hp : 0 < p) (ht : 0 ≤ t) :
      p ^ κ * powerDifference κ t = (p * (1 + t)) ^ κ - (p * t) ^ κ := by
    rw [Real.mul_rpow hp.le (by linarith : 0 ≤ 1 + t), Real.mul_rpow hp.le ht]
    unfold powerDifference
    ring
  have hn : (x ^ 2 + x + 1) ^ κ - (x + 1) ^ κ =
      (x ^ 2) ^ κ * powerDifference κ (1 / x + (1 / x) ^ 2) := by
    rw [scale _ _ hx2 hsp.le]
    congr 2 <;> field_simp <;> ring
  have hd : ((x + 1) ^ κ - 1) * x ^ κ =
      (x ^ 2) ^ κ * powerDifference κ (1 / x) := by
    have hh := scale x (1 / x) hx0 hs.le
    have he₁ : x * (1 + 1 / x) = x + 1 := by field_simp
    have he₂ : x * (1 / x) = 1 := by field_simp
    rw [he₁, he₂, Real.one_rpow] at hh
    have hp : (x ^ 2) ^ κ = x ^ κ * x ^ κ := by
      rw [pow_two, Real.mul_rpow hx0.le hx0.le]
    rw [← hh, hp]
    ring
  rw [F_two (by linarith) hx, hn, hd, mul_div_mul_left _ _
    (Real.rpow_pos_of_pos hx2 κ).ne', Real.log_div
      (difference_pos hκ hsp.le).ne' (difference_pos hκ hs.le).ne']
  rfl

private lemma F_two_strictAnti {κ : ℝ} (hκ : 1 < κ) :
    StrictAntiOn (fun x => lcmPowerF κ x 2) (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  dsimp only
  have hx0 : 0 < x := by linarith [hx]
  have hy0 : 0 < y := by linarith [hy]
  have hsx : 0 < 1 / x := one_div_pos.mpr hx0
  have hsy : 0 < 1 / y := one_div_pos.mpr hy0
  have hn := increment_strictMono hκ hsy hsx (one_div_lt_one_div_of_lt hx0 hxy)
  have hp : 0 < logPowerDifference κ (1 / y + (1 / y) ^ 2) -
      logPowerDifference κ (1 / y) := sub_pos.mpr
    (log_strictMono hκ hsy (show 0 < 1 / y + (1 / y) ^ 2 by positivity)
      (by nlinarith [sq_pos_of_pos hsy]))
  rw [F_two_increment hκ hx, F_two_increment hκ hy]
  exact div_lt_div₀ hn
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxy.le) (by linarith))
    (hp.le.trans hn.le) (mul_pos (by linarith) (Real.log_pos hx))

/-- The comparison of the two LCM power function values. -/
theorem lemma415_F {κ y : ℝ} (hκ : 1 < κ) (hy : Real.sqrt 2 < y) :
    lcmPowerF κ y 2 < lcmPowerF κ (y ^ (2 : ℝ) / 2) 1 := by
  have hy0 : 0 < y := (Real.sqrt_pos.2 (by norm_num)).trans hy
  have hy2 : 2 < y ^ 2 := (Real.sqrt_lt (by norm_num) hy0.le).mp hy
  have hy1 : 1 < y := by nlinarith
  simpa only [Real.rpow_two] using F_of_core hκ hy1 hy2
    (by simpa only [Real.rpow_two] using lemma415_core hκ hy1)

/-- Lemma 4.15 for every real kappa greater than one. -/
theorem lemma415 {κ x x' : ℝ} (hκ : 1 < κ) (hx : 1 < x) (hx' : 1 < x')
    (h : lcmPowerF κ x' 2 = lcmPowerF κ x 1) : x' < Real.sqrt (2 * x) := by
  have hy : Real.sqrt 2 < Real.sqrt (2 * x) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hy1 : 1 < Real.sqrt (2 * x) := by
    have : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith
  have hi := lemma415_F hκ hy
  rw [Real.rpow_two, Real.sq_sqrt (by linarith : 0 ≤ 2 * x),
    show 2 * x / 2 = x by ring, ← h] at hi
  by_contra hn
  rcases eq_or_lt_of_le (le_of_not_gt hn) with he | he
  · exact (ne_of_lt hi) (congrArg (fun z => lcmPowerF κ z 2) he)
  · exact (not_lt_of_gt (F_two_strictAnti hκ hy1 hx' he)) hi

end D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
