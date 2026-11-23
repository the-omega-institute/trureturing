/- GID: D5/S3/Weil/Mertens/RobinWeightedRamp
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/RobinWeightedRamp
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Exact weighted Mangoldt ramps and finite sampling of the Robin negative mass. -/

import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Weil.Mertens.WeightedTailWindowMass

/-! Exact finite Mangoldt ramps, their upper chord, and fourth-power sampling for
the canonical Robin weighted negative mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.RobinWeightedRamp

open Real Set MeasureTheory Finset
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg)
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel complete_mertens_ledger)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)

noncomputable section

/-- The coordinate in which each weighted Mangoldt ramp is convex. -/
def u (x : ℝ) : ℝ := x * log x

/-- The finite weighted Mertens error after subtracting the Chebyshev endpoint term. -/
def R (x : ℝ) : ℝ := u x * Mertens.E₂Λ x - (Chebyshev.psi x - x)

private lemma u_pos {x : ℝ} (hx : 1 < x) : 0 < u x :=
  mul_pos (zero_lt_one.trans hx) (log_pos hx)

private lemma u_strictMonoOn : StrictMonoOn u (Ioi 1) := by
  intro x hx y hy hxy
  have hx' : 1 < x := hx
  have hlog := log_le_log (zero_lt_one.trans hx') hxy.le
  exact (mul_lt_mul_of_pos_right hxy (log_pos hx')).trans_le
    (mul_le_mul_of_nonneg_left hlog (by linarith))

theorem ramp_eq_neg_weightedTail {x : ℝ} (hx : 2 ≤ x) :
    R x = -u x * weightedTail psiErrorKernel x := by
  have hu := (u_pos (by linarith : 1 < x)).ne'
  unfold R
  rw [(complete_mertens_ledger hx).2.2]
  change u x * ((Chebyshev.psi x - x) / u x - weightedTail psiErrorKernel x) -
    (Chebyshev.psi x - x) = _
  field_simp [hu]
  ring

private def rampSum (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Icc 2 N, vonMangoldt n * max (s / u (n : ℝ) - 1) 0

/-- Each prime power through the common cutoff contributes a nonnegative ramp.
The term at an integer endpoint is included and its ramp vanishes there. -/
theorem ramp_eq_sum {x : ℝ} {N : ℕ} (hx : 2 ≤ x) (hN : ⌊x⌋₊ ≤ N) :
    R x = (∑ n ∈ Icc 2 N, vonMangoldt n * max (u x / u (n : ℝ) - 1) 0) -
      u x * (log (log x) + eulerMascheroniConstant) + x := by
  let f (n : ℕ) : ℝ := vonMangoldt n * (u x / u (n : ℝ) - 1)
  have hsmall : ∑ n ∈ Icc 2 ⌊x⌋₊, f n = ∑ n ∈ Ioc 0 ⌊x⌋₊, f n := by
    apply sum_subset
    · intro n hn
      rw [Finset.mem_Icc] at hn
      exact Finset.mem_Ioc.mpr ⟨by omega, hn.2⟩
    · intro n hn hnot
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc, not_and_or] at hnot
      have : n = 1 := by omega
      simp [f, this]
  have hsum : (∑ n ∈ Icc 2 N, vonMangoldt n * max (u x / u (n : ℝ) - 1) 0) =
      ∑ n ∈ Icc 2 ⌊x⌋₊, f n := by
    symm
    refine Eq.trans (sum_congr rfl ?_) (sum_subset ?_ ?_)
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hnx := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hn.2
      have hnu := u_strictMonoOn.monotoneOn (show 1 < (n : ℝ) by linarith)
        (show 1 < x by linarith) hnx
      exact congrArg (vonMangoldt n * ·) (max_eq_left (sub_nonneg.mpr
        ((le_div_iff₀ (u_pos (by linarith))).2 (by simpa using hnu)))).symm
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans hN⟩
    · intro n hn hnot
      rw [Finset.mem_Icc] at hn hnot
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt (by omega)
      have hnu := u_strictMonoOn (show 1 < x by linarith)
        (show 1 < (n : ℝ) by linarith) hxn
      rw [max_eq_right (sub_nonpos.mpr ((div_le_one (u_pos (by linarith))).2 hnu.le)),
        mul_zero]
  rw [hsum, hsmall]
  unfold R
  rw [Mertens.E₂Λ, Chebyshev.psi, Mertens.γ.eq_eulerMascheroni]
  have hterm (n : ℕ) : f n = u x * (vonMangoldt n / u (n : ℝ)) - vonMangoldt n := by
    dsimp [f]
    ring
  simp_rw [hterm, sum_sub_distrib, ← mul_sum]
  unfold u
  ring

private lemma rampSum_chord (N : ℕ) {s t y p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p + q = 1) (hy : p * s + q * t = y) :
    rampSum N y ≤ p * rampSum N s + q * rampSum N t := by
  unfold rampSum
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro n _
  let r (v : ℝ) := v / u (n : ℝ) - 1
  have heq : r y = p * r s + q * r t := by
    dsimp [r]
    rw [← hy]
    linear_combination hs
  have hmax : max (r y) 0 ≤ p * max (r s) 0 + q * max (r t) 0 :=
    max_le (heq.le.trans (add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hp)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hq))) (by positivity)
  calc
    _ ≤ vonMangoldt n * (p * max (r s) 0 + q * max (r t) 0) :=
      mul_le_mul_of_nonneg_left hmax vonMangoldt_nonneg
    _ = _ := by dsimp [r]; ring

private def smooth (z : ℝ) : ℝ :=
  u z * (log (log z) + eulerMascheroniConstant) - z

/-- The two elementary bounds for a logarithmic difference. -/
private lemma log_diff_bounds {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    z - a ≤ z * (log z - log a) ∧ log z - log a ≤ (z - a) / a := by
  have hlo := one_sub_inv_le_log_of_pos (div_pos hz ha)
  have hhi := log_le_sub_one_of_pos (div_pos hz ha)
  rw [log_div hz.ne' ha.ne', inv_div] at hlo
  rw [log_div hz.ne' ha.ne'] at hhi
  constructor
  · calc
      z - a = z * (1 - a / z) := by field_simp [hz.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hz.le
  · calc
      _ ≤ z / a - 1 := hhi
      _ = _ := by field_simp [ha.ne']

private lemma smooth_tangent_bounds {a z : ℝ} (ha : exp 1 ≤ a) (haz : a ≤ z)
    (hz : z ≤ 2 * a) :
    let T := smooth z - smooth a -
      (log (log a) + eulerMascheroniConstant) * (u z - u a)
    0 ≤ T ∧ T ≤ 3 * (z - a) ^ 2 / a := by
  dsimp
  have ha0 := (exp_pos 1).trans_le ha
  have hz0 := ha0.trans_le haz
  have hLa : 1 ≤ log a := (le_log_iff_exp_le ha0).2 ha
  have hLz := log_le_log ha0 haz
  have hLa0 : 0 < log a := by linarith
  have hLz0 := hLa0.trans_le hLz
  let d := log z - log a
  have hd0 : 0 ≤ d := sub_nonneg.mpr hLz
  have ⟨hzlo, hdhi⟩ := log_diff_bounds ha0 hz0
  have ⟨hlo, hhi⟩ := log_diff_bounds hLa0 hLz0
  have htangent : smooth z - smooth a -
      (log (log a) + eulerMascheroniConstant) * (u z - u a) =
      u z * (log (log z) - log (log a)) - (z - a) := by unfold smooth; ring
  rw [htangent]
  constructor
  · have hprod := mul_le_mul_of_nonneg_left hlo hz0.le
    unfold u
    linarith only [hzlo, hprod]
  · have hcoef : z / log a ≤ 2 * a :=
      (div_le_self hz0.le hLa).trans hz
    have hmain : z * d - (z - a) ≤ (z - a)^2 / a := calc
      _ ≤ z * ((z - a) / a) - (z - a) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hdhi hz0.le) _
      _ = _ := by field_simp [ha0.ne']
    have hquad : (z / log a) * d ^ 2 ≤ 2 * ((z - a)^2 / a) := calc
      _ ≤ (2 * a) * (((z - a) / a) ^ 2) :=
        mul_le_mul hcoef (pow_le_pow_left₀ hd0 hdhi 2) (sq_nonneg _) (by positivity)
      _ = _ := by field_simp [ha0.ne']
    calc
      _ ≤ u z * (d / log a) - (z - a) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hhi (mul_nonneg hz0.le hLz0.le)) _
      _ = (z * d - (z - a)) + (z / log a) * d ^ 2 := by
        unfold u
        dsimp [d]
        field_simp [hLa0.ne']
        ring
      _ ≤ (z - a) ^ 2 / a + 2 * ((z - a) ^ 2 / a) := add_le_add hmain hquad
      _ = _ := by ring

/-- The exact Robin ramp satisfies a second-order upper chord in the coordinate x log x. -/
theorem ramp_chord {a b x p q : ℝ} (ha : exp 1 ≤ a) (hab : a < b) (hb : b ≤ 2 * a)
    (hx : x ∈ Icc a b) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p + q = 1)
    (hc : p * u a + q * u b = u x) :
    R x ≤ p * R a + q * R b + 3 * (b - a) ^ 2 / a := by
  have ha2 : 2 ≤ a := Real.exp_one_gt_two.le.trans ha
  have hre (z : ℝ) (hz : z ∈ Icc a b) :
      R z = rampSum ⌊b⌋₊ (u z) - smooth z := by
    rw [ramp_eq_sum (ha2.trans hz.1) (Nat.floor_mono hz.2)]
    unfold rampSum smooth
    ring
  rw [hre x hx, hre a ⟨le_rfl, hab.le⟩, hre b ⟨hab.le, le_rfl⟩]
  have hr := rampSum_chord ⌊b⌋₊ hp hq hs hc
  let m := log (log a) + eulerMascheroniConstant
  have hlo : 0 ≤ smooth x - smooth a - m * (u x - u a) :=
    (smooth_tangent_bounds ha hx.1 (hx.2.trans hb)).1
  have hhi := mul_le_mul_of_nonneg_left (smooth_tangent_bounds ha hab.le hb).2 hq
  change q * (smooth b - smooth a - m * (u b - u a)) ≤
    q * (3 * (b - a) ^ 2 / a) at hhi
  have hq1 : q ≤ 1 := by linarith
  have herror : 0 ≤ 3 * (b - a) ^ 2 / a := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hq1 herror
  have hlinear : p * smooth a + q * smooth b - smooth x =
      q * (smooth b - smooth a - m * (u b - u a)) -
        (smooth x - smooth a - m * (u x - u a)) := by
    linear_combination (smooth a - m * u a) * hs + m * hc
  nlinarith only [hr, hlinear, hlo, hhi, hscaled]

private def rampDensity (x : ℝ) : ℝ :=
  (log x / (1 + log x)) * (max (R x) 0 / (x * sqrt x))

private lemma density_eq {x : ℝ} (hx : 2 ≤ x) :
    (WeightedTailInverse.a x / sqrt x) * max (-weightedTail psiErrorKernel x) 0 =
      rampDensity x := by
  have hx0 : 0 < x := by linarith
  have hl := log_pos (by linarith : 1 < x)
  have hs := sqrt_pos.2 hx0
  have hd : 0 < 1 + log x := by positivity
  have hu := u_pos (by linarith : 1 < x)
  have heq : max (R x) 0 = u x * max (-weightedTail psiErrorKernel x) 0 := by
    rw [mul_max_of_nonneg _ _ hu.le, mul_zero, ramp_eq_neg_weightedTail hx, mul_neg, neg_mul]
  unfold rampDensity WeightedTailInverse.a
  rw [heq]
  unfold u
  field_simp [hx0.ne', hs.ne', hd.ne']

private lemma density_continuousOn {c d : ℝ} (hc : 2 ≤ c) :
    ContinuousOn rampDensity (Icc c d) := by
  have hlog : ContinuousOn log (Icc c d) := fun x hx =>
    (continuousAt_log (by linarith [hx.1] : x ≠ 0)).continuousWithinAt
  have htail : ContinuousOn (weightedTail psiErrorKernel) (Icc c d) :=
    (complete_mertens_ledger hc).2.1.continuousOn_Ici_primitive_Ioi.mono (fun _ hx => hx.1)
  have hR : ContinuousOn R (Icc c d) := by
    apply ((continuousOn_id.mul hlog).neg.mul htail).congr
    intro x hx
    exact ramp_eq_neg_weightedTail (hc.trans hx.1)
  have hratio : ContinuousOn (fun x => log x / (1 + log x)) (Icc c d) :=
    hlog.div (hlog.const_add 1) (fun x hx =>
      ne_of_gt (by linarith [log_pos (by linarith [hx.1] : 1 < x)]))
  exact hratio.mul ((hR.sup continuousOn_const).div
    (continuousOn_id.mul continuous_sqrt.continuousOn) (fun x hx =>
      have hx0 : 0 < x := by linarith [hx.1]
      mul_ne_zero hx0.ne' (sqrt_pos.2 hx0).ne'))

/-- Endpoint samples on a full chord cell control the weighted negative mass on
every subinterval. -/
theorem mass_le_of_cell {a b c d : ℝ} (ha : exp 1 ≤ a) (hab : a < b) (hb : b ≤ 2 * a)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    weightedNegativeMass psiErrorKernel c d ≤
      (d - c) / (a * sqrt a) * (max (R a) 0 + max (R b) 0 + 3 * (b - a) ^ 2 / a) := by
  have ha2 : 2 ≤ a := Real.exp_one_gt_two.le.trans ha
  have ha0 : 0 < a := by linarith
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := ha1.trans hab
  have hdena : 0 < a * sqrt a := mul_pos ha0 (sqrt_pos.2 ha0)
  let M := max (R a) 0 + max (R b) 0 + 3 * (b - a) ^ 2 / a
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have heq : weightedNegativeMass psiErrorKernel c d = ∫ x in c..d, rampDensity x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hcd]
    intro x hx
    exact density_eq (ha2.trans (hac.trans hx.1))
  rw [heq, div_mul_eq_mul_div, mul_div_assoc, ← smul_eq_mul (d - c),
    ← intervalIntegral.integral_const]
  apply intervalIntegral.integral_mono_on hcd
    ((density_continuousOn (ha2.trans hac)).intervalIntegrable_of_Icc hcd)
    intervalIntegrable_const
  intro x hx
  have hx' : x ∈ Icc a b := ⟨hac.trans hx.1, hx.2.trans hdb⟩
  have hx1 : 1 < x := ha1.trans_le hx'.1
  have hx0 : 0 < x := ha0.trans_le hx'.1
  have habu := u_strictMonoOn ha1 hb1 hab
  have hgap := sub_pos.mpr habu
  let q := (u x - u a) / (u b - u a)
  let p := 1 - q
  have hq : 0 ≤ q :=
    div_nonneg (sub_nonneg.mpr (u_strictMonoOn.monotoneOn ha1 hx1 hx'.1)) hgap.le
  have hq1 : q ≤ 1 := (div_le_one hgap).2
    (sub_le_sub_right (u_strictMonoOn.monotoneOn hx1 hb1 hx'.2) _)
  have hp : 0 ≤ p := sub_nonneg.mpr hq1
  have hp1 : p ≤ 1 := sub_le_self _ hq
  have hsum : p + q = 1 := sub_add_cancel _ _
  have hcoord : p * u a + q * u b = u x := by
    have hmul : q * (u b - u a) = u x - u a := div_mul_cancel₀ _ hgap.ne'
    dsimp only [p]
    linarith only [hmul]
  have hr := ramp_chord ha hab hb hx' hp hq hsum hcoord
  have hap : p * R a ≤ max (R a) 0 := calc
    _ ≤ p * max (R a) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hp
    _ ≤ _ := mul_le_of_le_one_left (le_max_right _ _) hp1
  have hbp : q * R b ≤ max (R b) 0 := calc
    _ ≤ q * max (R b) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hq
    _ ≤ _ := mul_le_of_le_one_left (le_max_right _ _) hq1
  have hR : max (R x) 0 ≤ M := max_le (by dsimp [M]; linarith only [hr, hap, hbp]) hM
  have hden : a * sqrt a ≤ x * sqrt x :=
    mul_le_mul hx'.1 (sqrt_le_sqrt hx'.1) (sqrt_nonneg _) hx0.le
  have hl := log_pos hx1
  have hratio : log x / (1 + log x) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  change rampDensity x ≤ M / (a * sqrt a)
  calc
    _ ≤ max (R x) 0 / (x * sqrt x) :=
      mul_le_of_le_one_left (div_nonneg (le_max_right _ _) (by positivity)) hratio
    _ ≤ M / (a * sqrt a) :=
      (div_le_div_of_nonneg_right hR (by positivity)).trans
        (div_le_div_of_nonneg_left hM hdena hden)

private lemma quartic_cell_bounds {n : ℝ} (hn : 6 ≤ n) :
    exp 1 ≤ n ^ 4 ∧ n ^ 4 < (n + 1) ^ 4 ∧ (n + 1) ^ 4 ≤ 2 * n ^ 4 ∧
      (n + 1) ^ 4 - n ^ 4 ≤ 15 * n ^ 3 := by
  have hn1 : 1 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  refine ⟨Real.exp_one_lt_three.le.trans ?_, ?_, ?_, ?_⟩
  · exact (by norm_num : (3 : ℝ) ≤ 6 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) hn 4)
  · exact pow_lt_pow_left₀ (by linarith) hn0.le (by decide)
  · calc
      (n + 1) ^ 4 ≤ ((7 / 6 : ℝ) * n) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ = (7 / 6 : ℝ) ^ 4 * n ^ 4 := mul_pow _ _ _
      _ ≤ 2 * n ^ 4 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg n),
      mul_nonneg (sub_nonneg.mpr hn1) hn0.le]

/-- On a partial fourth-power cell, the weighted negative mass is bounded by
its relative length times the sum of the normalized endpoint data and the curvature allowance. -/
theorem quartic_mass_le {n : ℕ} (hn : 6 ≤ n) {c d : ℝ}
    (hc : (n : ℝ) ^ 4 ≤ c) (hcd : c ≤ d) (hd : d ≤ ((n : ℝ) + 1) ^ 4) :
    weightedNegativeMass psiErrorKernel c d ≤
      (d - c) / (n : ℝ) ^ 4 *
        ((max (R ((n : ℝ) ^ 4)) 0 + max (R (((n : ℝ) + 1) ^ 4)) 0) / (n : ℝ) ^ 2 + 675) := by
  have hn' : 6 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  obtain ⟨ha, hab, hb, hw⟩ := quartic_cell_bounds hn'
  have herror : 3 * (((n : ℝ) + 1) ^ 4 - (n : ℝ) ^ 4) ^ 2 / (n : ℝ) ^ 4 ≤
      675 * (n : ℝ) ^ 2 := by
    apply (div_le_iff₀ (pow_pos hn0 4)).2
    calc
      _ ≤ 3 * (15 * (n : ℝ) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hab.le) hw 2) (by norm_num)
      _ = _ := by ring
  have hsqrt : sqrt ((n : ℝ) ^ 4) = (n : ℝ) ^ 2 := by
    rw [show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring, sqrt_sq (sq_nonneg _)]
  have hm := mass_le_of_cell ha hab hb hc hcd hd
  rw [hsqrt] at hm
  refine hm.trans (le_trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) herror)
    (by positivity)) ?_)
  apply le_of_eq
  field_simp [hn0.ne']

end
end D5.S3.Weil.Mertens.RobinWeightedRamp
