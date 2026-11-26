/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenter
   generality: G
   mirror-B: none(waiver:internal-analytic-identity)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact log-coordinate normalization of the positive-center BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeDerivatives
import D5.S3.Quantum.Analysis.RefinedBMVExtremeWalk
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination

/-! # Log coordinates for the positive-center refined BMV kernel -/

noncomputable section

namespace RefinedBMV.PositiveCenter

open DimThree (defect defect_corner defect_corner_eq_iff gaps gaps_length_eq_choose
  mem_gaps_iff_total word_counts_all)
open UniformThreeSpectrum (defect_cycle_all defect_diag_all defect_nonneg_all)

/-- The degree-scaled log ratio of a root to the center. -/
def logCoordinate (p : ℕ) (a x : ℝ) : ℝ :=
  (p : ℝ) * Real.log (x / a)

private def centeredExponent (p n : ℕ) : ℝ :=
  3 * (n : ℝ) / (p : ℝ) - 1

/-- The centered exponential moment of the uniform weak three-part compositions. -/
def compositionMoment (p : ℕ) (u v : ℝ) : ℝ :=
  ((gaps p).map fun g =>
    Real.exp (centeredExponent p g.2.1 * u + centeredExponent p g.2.2 * v)).sum /
      ((gaps p).length : ℝ) - 1

/-- The normalized ordered kernel in the independent coordinates `u` and `v`. -/
def logKernel (p : ℕ) (u v : ℝ) : ℝ :=
  (compositionMoment p u v -
    Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v - u))) /
    Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v))

private theorem logCoordinate_self (p : ℕ) {a : ℝ} (ha : 0 < a) :
    logCoordinate p a a = 0 := by
  simp [logCoordinate, ha.ne']

private theorem logCoordinate_sub (p : ℕ) {a x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    logCoordinate p a y - logCoordinate p a x = logCoordinate p x y := by
  simp only [logCoordinate, Real.log_div hy.ne' ha.ne', Real.log_div hx.ne' ha.ne',
    Real.log_div hy.ne' hx.ne']
  ring

private theorem logCoordinate_reverse (p : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    logCoordinate p x a = -logCoordinate p a x := by
  rw [← logCoordinate_sub p ha hx ha, logCoordinate_self p ha, zero_sub]

private theorem exp_nat_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log x) = x ^ n := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

private theorem monomial_eq_exp {p : ℕ} (hp : 0 < p) {a x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) {g : ℕ × ℕ × ℕ} (hg : g ∈ gaps p) :
    (a ^ 3) ^ g.1 * (x ^ 3) ^ g.2.1 * (y ^ 3) ^ g.2.2 =
      (a * x * y) ^ p *
        Real.exp (centeredExponent p g.2.1 * logCoordinate p a x +
          centeredExponent p g.2.2 * logCoordinate p a y) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htotal : (g.1 : ℝ) + g.2.1 + g.2.2 = (p : ℝ) := by
    exact_mod_cast (mem_gaps_iff_total p g).mp hg
  have hcenter (n : ℕ) (s : ℝ) :
      centeredExponent p n * ((p : ℝ) * s) = (3 * (n : ℝ) - (p : ℝ)) * s := by
    rw [← mul_assoc, centeredExponent, sub_mul, div_mul_cancel₀ _ hpR, one_mul]
  calc
    _ = Real.exp ((g.1 : ℝ) * (((3 : ℕ) : ℝ) * Real.log a) +
          (g.2.1 : ℝ) * (((3 : ℕ) : ℝ) * Real.log x) +
          (g.2.2 : ℝ) * (((3 : ℕ) : ℝ) * Real.log y)) := by
      rw [Real.exp_add, Real.exp_add,
        Real.exp_nat_mul (((3 : ℕ) : ℝ) * Real.log a) g.1,
        Real.exp_nat_mul (((3 : ℕ) : ℝ) * Real.log x) g.2.1,
        Real.exp_nat_mul (((3 : ℕ) : ℝ) * Real.log y) g.2.2,
        exp_nat_log ha 3, exp_nat_log hx 3, exp_nat_log hy 3]
    _ = Real.exp ((p : ℝ) * Real.log (a * x * y) +
          (centeredExponent p g.2.1 * logCoordinate p a x +
            centeredExponent p g.2.2 * logCoordinate p a y)) := by
      apply congrArg Real.exp
      rw [Real.log_mul (mul_ne_zero ha.ne' hx.ne') hy.ne', Real.log_mul ha.ne' hx.ne']
      simp only [logCoordinate, Real.log_div hx.ne' ha.ne', Real.log_div hy.ne' ha.ne',
        hcenter, Nat.cast_ofNat]
      linear_combination (3 * Real.log a) * htotal
    _ = _ := by
      rw [Real.exp_add, exp_nat_log (mul_pos (mul_pos ha hx) hy)]

private theorem compositionCount_pos (p : ℕ) : (0 : ℝ) < (gaps p).length := by
  exact_mod_cast (word_counts_all p).2.1

/-- The defect factors into its geometric mean scale and the centered moment. -/
theorem defect_eq_compositionMoment {p : ℕ} (hp : 0 < p) {a x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    defect p a x y = ((gaps p).length : ℝ) * (a * x * y) ^ p *
      compositionMoment p (logCoordinate p a x) (logCoordinate p a y) := by
  let f (g : ℕ × ℕ × ℕ) :=
    Real.exp (centeredExponent p g.2.1 * logCoordinate p a x +
      centeredExponent p g.2.2 * logCoordinate p a y)
  have hsum : ((gaps p).map (fun g =>
      (a ^ 3) ^ g.1 * (x ^ 3) ^ g.2.1 * (y ^ 3) ^ g.2.2)).sum =
      (a * x * y) ^ p * ((gaps p).map f).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    exact List.map_congr_left fun g hg => monomial_eq_exp hp ha hx hy hg
  unfold defect
  rw [hsum]
  let N : ℝ := (gaps p).length
  let b : ℝ := (a * x * y) ^ p
  let s : ℝ := ((gaps p).map f).sum
  change b * s - N * b = N * b * (s / N - 1)
  rw [mul_comm N b, mul_assoc b N, mul_sub, mul_one,
    mul_div_cancel₀ s (compositionCount_pos p).ne', mul_sub]

/-- The exact normalization used by `Extreme.normalized` at positive roots.
The identity allows repeated roots, and applies to the ordered upper kernel for `x ≤ y`. -/
theorem normalized_eq_logKernel {p : ℕ} (hp : 0 < p) {a x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    Extreme.normalized (fun z => defect p a z z) (fun z => defect p a z z)
      (defect p a) (fun s t => defect p a a t * defect p s s t) x y =
      logKernel p (logCoordinate p a x) (logCoordinate p a y) := by
  let u := logCoordinate p a x
  let v := logCoordinate p a y
  let F (r s t : ℝ) := ((gaps p).length : ℝ) * (r * s * t) ^ p
  have hF : 0 < F a x y :=
    mul_pos (compositionCount_pos p) (pow_pos (mul_pos (mul_pos ha hx) hy) p)
  have hnum : defect p a x y = F a x y * compositionMoment p u v :=
    defect_eq_compositionMoment hp ha hx hy
  have haa : defect p a a y = F a a y * compositionMoment p 0 v := by
    simpa only [logCoordinate_self p ha] using defect_eq_compositionMoment hp ha ha hy
  have hxx : defect p x x y = F x x y * compositionMoment p 0 (v - u) := by
    change defect p x x y = F x x y *
      compositionMoment p 0 (logCoordinate p a y - logCoordinate p a x)
    rw [logCoordinate_sub p ha hx hy]
    simpa only [logCoordinate_self p hx] using defect_eq_compositionMoment hp hx hx hy
  have hweight {z : ℝ} (hz : 0 < z) :
      defect p a z z = F a z z * compositionMoment p 0 (-logCoordinate p a z) := by
    rw [← defect_cycle_all p a z z]
    have hscale : F z z a = F a z z := by
      dsimp only [F]
      rw [show z * z * a = a * z * z by ring]
    calc
      defect p z z a = F z z a * compositionMoment p (logCoordinate p z z)
          (logCoordinate p z a) := defect_eq_compositionMoment hp hz hz ha
      _ = _ := by rw [hscale, logCoordinate_self p hz, logCoordinate_reverse p ha hz]
  have hnumScale : F a a y * F x x y = (F a x y) ^ 2 := by
    simp only [F, mul_pow]
    ring
  have hdenScale : F a x x * F a y y = (F a x y) ^ 2 := by
    simp only [F, mul_pow]
    ring
  have hsqrt (m n r s : ℝ) (h : m * n = (F a x y) ^ 2) :
      Real.sqrt ((m * r) * (n * s)) = F a x y * Real.sqrt (r * s) := by
    rw [show (m * r) * (n * s) = (m * n) * (r * s) by ring, h,
      Real.sqrt_mul (sq_nonneg (F a x y)), Real.sqrt_sq hF.le]
  have hq : Real.sqrt (defect p a a y * defect p x x y) =
      F a x y * Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v - u)) := by
    rw [haa, hxx]
    exact hsqrt _ _ _ _ hnumScale
  have hw : Real.sqrt (defect p a x x * defect p a y y) =
      F a x y * Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) := by
    rw [hweight hx, hweight hy]
    exact hsqrt _ _ _ _ hdenScale
  change Extreme.normalized _ _ _ _ x y = logKernel p u v
  unfold Extreme.normalized logKernel
  rw [div_div, ← Real.sqrt_mul (defect_nonneg_all p a x x ha.le hx.le hx.le),
    hnum, hq, hw, ← mul_sub]
  exact mul_div_mul_left _ _ hF.ne'

/-- The normalized symmetric upper kernel at a positive center, including coincident points. -/
theorem upperKernel_div_weights_eq_logKernel {p : ℕ} (hp : 0 < p) {a x y : ℝ}
    (ha : 0 < a) (hx : a < x) (hy : a < y) :
    ExtremeWalk.upperKernel p a x y / Real.sqrt (defect p a x x * defect p a y y) =
      logKernel p (logCoordinate p a (min x y)) (logCoordinate p a (max x y)) := by
  have ordered {s t : ℝ} (hs : a < s) (hst : s ≤ t) :
      ExtremeWalk.upperKernel p a s t / Real.sqrt (defect p a s s * defect p a t t) =
        logKernel p (logCoordinate p a s) (logCoordinate p a t) := by
    have hs' := ha.trans hs
    have ht' := hs'.trans_le hst
    simpa only [Extreme.normalized, div_div,
      ← Real.sqrt_mul (defect_nonneg_all p a s s ha.le hs'.le hs'.le),
      ExtremeWalk.upperKernel, min_eq_left hst, max_eq_right hst] using
        normalized_eq_logKernel hp ha hs' ht'
  rcases le_total x y with hxy | hyx
  · simpa only [min_eq_left hxy, max_eq_right hxy] using ordered hx hxy
  · rw [min_eq_right hyx, max_eq_left hyx]
    simpa only [ExtremeWalk.upperKernel, min_comm y x, max_comm y x,
      mul_comm (defect p a y y) (defect p a x x)] using ordered hy hyx

/-- The diagonal normalization uses a strictly positive defect above the center. -/
theorem weight_pos {p : ℕ} (hp : 0 < p) {a x : ℝ} (ha : 0 ≤ a) (hax : a < x) :
    0 < defect p a x x := by
  have hx := ha.trans hax.le
  have hne : Real.sqrt (defect p a a x * defect p x x x) ≠ defect p a x x := by
    intro heq
    exact ((defect_corner_eq_iff p ha hx hx).mp heq).elim hp.ne' hax.ne
  exact (Real.sqrt_nonneg _).trans_lt (lt_of_le_of_ne (defect_corner p ha hx hx) hne)

/-- The logarithmic formula has value one at a tie above the positive center. -/
theorem logKernel_diagonal {p : ℕ} (hp : 0 < p) {a x : ℝ} (ha : 0 < a) (hx : a < x) :
    logKernel p (logCoordinate p a x) (logCoordinate p a x) = 1 := by
  have hw := weight_pos hp ha.le hx
  have h := upperKernel_div_weights_eq_logKernel hp ha hx hx
  simpa only [ExtremeWalk.upperKernel, min_self, max_self, defect_diag_all, mul_zero,
    Real.sqrt_zero, sub_zero, Real.sqrt_mul_self hw.le, div_self hw.ne'] using h.symm

/-- The uncentered moment times its geometric factor is the homogeneous sum at the
three cube nodes. This supplies the existing distinct- and repeated-node divided differences. -/
theorem compositionMoment_add_one_mul {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    ((gaps p).length : ℝ) * Real.exp (u + v) * (compositionMoment p u v + 1) =
      DividedDifference.homogeneousThree p 1
        (Real.exp (3 * (u / (p : ℝ)))) (Real.exp (3 * (v / (p : ℝ)))) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let x := Real.exp (u / (p : ℝ))
  let y := Real.exp (v / (p : ℝ))
  have hcoord (t : ℝ) : logCoordinate p 1 (Real.exp (t / (p : ℝ))) = t := by
    rw [logCoordinate, div_one, Real.log_exp, mul_comm, div_mul_cancel₀ _ hpR]
  have hcube (t : ℝ) :
      Real.exp (t / (p : ℝ)) ^ 3 = Real.exp (3 * (t / (p : ℝ))) :=
    (Real.exp_nat_mul (t / (p : ℝ)) 3).symm
  have hgeom : (1 * x * y) ^ p = Real.exp (u + v) := by
    change (1 * Real.exp (u / (p : ℝ)) * Real.exp (v / (p : ℝ))) ^ p = _
    rw [one_mul, ← Real.exp_add, ← Real.exp_nat_mul]
    apply congrArg Real.exp
    rw [mul_add, mul_comm (p : ℝ) (u / (p : ℝ)), div_mul_cancel₀ _ hpR,
      mul_comm (p : ℝ) (v / (p : ℝ)), div_mul_cancel₀ _ hpR]
  have h := defect_eq_compositionMoment hp (a := 1) (x := x) (y := y) zero_lt_one
    (Real.exp_pos _) (Real.exp_pos _)
  have hx : logCoordinate p 1 x = u := hcoord u
  have hy : logCoordinate p 1 y = v := hcoord v
  rw [hx, hy, DividedDifference.defect_eq_homogeneous, ← gaps_length_eq_choose, hgeom] at h
  calc
    _ = ((gaps p).length : ℝ) * Real.exp (u + v) * compositionMoment p u v +
        ((gaps p).length : ℝ) * Real.exp (u + v) := by rw [mul_add, mul_one]
    _ = DividedDifference.homogeneousThree p ((1 : ℝ) ^ 3) (x ^ 3) (y ^ 3) := by
      rw [← h, sub_add_cancel]
    _ = _ := by
      change DividedDifference.homogeneousThree p ((1 : ℝ) ^ 3)
        (Real.exp (u / (p : ℝ)) ^ 3) (Real.exp (v / (p : ℝ)) ^ 3) = _
      rw [one_pow, hcube u, hcube v]

/-- The cleared marginal formula holds at either sign of the log gap, including zero. -/
theorem compositionMoment_marginal_clear {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let z := Real.exp (3 * (t / (p : ℝ)))
    (z - 1) ^ 2 * (((gaps p).length : ℝ) * Real.exp t * (compositionMoment p 0 t + 1)) =
      z ^ (p + 2) - (p + 2 : ℝ) * z + (p + 1 : ℝ) := by
  dsimp only
  have h := compositionMoment_add_one_mul hp 0 t
  simp only [zero_add, zero_div, mul_zero, Real.exp_zero] at h
  rw [h]
  simpa only [one_pow, mul_one] using
    DividedDifference.clear_repeat_first p (1 : ℝ) (Real.exp (3 * (t / (p : ℝ))))

/-- Positive root coordinates are inverted by the exponential parametrization. -/
theorem logCoordinate_mul_exp {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    logCoordinate p a (a * Real.exp (t / (p : ℝ))) = t := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold logCoordinate
  rw [mul_comm a, mul_div_cancel_right₀ _ ha.ne', Real.log_exp, mul_div_cancel₀ _ hp']

/-- Exchanging the first two roots gives the moment symmetry used at the lower collision. -/
theorem compositionMoment_swap_center {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    compositionMoment p u v = compositionMoment p (-u) (v - u) := by
  let x := Real.exp (u / (p : ℝ))
  let y := Real.exp (v / (p : ℝ))
  have hx : 0 < x := Real.exp_pos _
  have hy : 0 < y := Real.exp_pos _
  have hu : logCoordinate p 1 x = u := by
    simpa only [x, one_mul] using logCoordinate_mul_exp hp zero_lt_one u
  have hv : logCoordinate p 1 y = v := by
    simpa only [y, one_mul] using logCoordinate_mul_exp hp zero_lt_one v
  have hreverse : logCoordinate p x 1 = -u := by
    rw [logCoordinate_reverse p zero_lt_one hx, hu]
  have hgap : logCoordinate p x y = v - u := by
    rw [← logCoordinate_sub p zero_lt_one hx hy, hu, hv]
  have ha := defect_eq_compositionMoment hp zero_lt_one hx hy
  have hb := defect_eq_compositionMoment hp hx zero_lt_one hy
  rw [hu, hv, one_mul] at ha
  rw [hreverse, hgap, mul_one, DividedDifference.defect_swap_general p 1 x y] at hb
  exact mul_left_cancel₀
    (mul_pos (compositionCount_pos p) (pow_pos (mul_pos hx hy) p)).ne'
    (ha.symm.trans hb)

#print axioms normalized_eq_logKernel
#print axioms compositionMoment_marginal_clear

end RefinedBMV.PositiveCenter
