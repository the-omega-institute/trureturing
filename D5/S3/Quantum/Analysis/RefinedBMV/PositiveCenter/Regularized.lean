/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/Regularized
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact regularization of the positive-center logarithmic kernel near collisions. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.LinearCombination

/-! # Exact small-corner regularization of the positive-center log kernel -/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter.SmallCorner

/-- The normalized marginal at a nonzero gap. -/
def G (p : ℕ) (c t : ℝ) : ℝ := compositionMoment p 0 t / (c * t ^ 2)

/-- The positive square root of the normalized marginal at a nonzero gap. -/
def R (p : ℕ) (c t : ℝ) : ℝ := Real.sqrt (G p c t)

/-- The quotient-rule expression for the derivative of `G` at a nonzero gap. -/
def GPrime (p : ℕ) (c t : ℝ) : ℝ :=
  (deriv (compositionMoment p 0) t / c - 2 * t * G p c t) / t ^ 2

/-- The normalized quadratic Taylor remainder in the first coordinate, for `u ≠ 0`. -/
def A (p : ℕ) (c u v : ℝ) : ℝ :=
  (compositionMoment p u v / c - compositionMoment p 0 v / c -
    u * (deriv (fun s ↦ compositionMoment p s v) 0 / c)) / u ^ 2

/-- The divided difference `G[v, v - u]`, for `u ≠ 0`. -/
def D (p : ℕ) (c u v : ℝ) : ℝ := (G p c v - G p c (v - u)) / u

/-- The repeated-node divided difference `G[v, v, v - u]`, for `u ≠ 0`. -/
def Q (p : ℕ) (c u v : ℝ) : ℝ := (GPrime p c v - D p c u v) / u

/-- The expression multiplying `u / v` on the open ordered corner. -/
def F (p : ℕ) (c u v : ℝ) : ℝ :=
  (A p c u v - v * GPrime p c v / 2 +
    (v * (v - u) / 2) * ((D p c u v / (R p c v + R p c (v - u))) ^ 2 - Q p c u v)) /
    (R p c (-u) * R p c (-v))

private theorem contDiff_marginal (p order : ℕ) :
    ContDiff ℝ (order : ℕ) (compositionMoment p 0) := by
  have h (a : (ℕ × ℕ × ℕ) → ℝ) (l : List (ℕ × ℕ × ℕ)) :
      ContDiff ℝ (order : ℕ) (fun t : ℝ ↦ (l.map fun g ↦ Real.exp (a g * t)).sum) := by
    induction l with
    | nil =>
      simpa only [List.map_nil, List.sum_nil] using
        (contDiff_const : ContDiff ℝ (order : ℕ) (fun _ : ℝ ↦ (0 : ℝ)))
    | cons g l ih =>
      have hg : ContDiff ℝ (order : ℕ) (fun t : ℝ ↦ Real.exp (a g * t)) := by fun_prop
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using hg.add ih
  change ContDiff ℝ (order : ℕ) (fun t : ℝ ↦ compositionMoment p 0 t)
  simp only [compositionMoment, mul_zero, zero_add]
  exact ((h _ _).div_const _).sub contDiff_const

private theorem differentiable_marginal (p : ℕ) : Differentiable ℝ (compositionMoment p 0) :=
  (contDiff_marginal p 1).differentiable (by norm_num)

/-- The algebraic expression `GPrime` is the derivative at every nonzero gap. -/
theorem hasDerivAt_G (p : ℕ) {c t : ℝ} (hc : c ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (G p c) (GPrime p c t) t := by
  have hm := (differentiable_marginal p t).hasDerivAt
  have hden : HasDerivAt (fun s : ℝ ↦ c * s ^ 2) (c * (2 * t)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hasDerivAt_pow 2 t).const_mul c
  apply (hm.div hden (mul_ne_zero hc (pow_ne_zero 2 ht))).congr_deriv
  unfold GPrime G
  field_simp [hc, ht]

/-- At `u = 0` the first-coordinate derivative is minus half the marginal derivative. -/
theorem hasDerivAt_compositionMoment_left {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun u ↦ compositionMoment p u v) (-deriv (compositionMoment p 0) v / 2) 0 := by
  let m := compositionMoment p 0
  have hm : HasDerivAt m (deriv m v) (v - 0) := by
    simpa only [sub_zero] using (differentiable_marginal p v).hasDerivAt
  have hshift : HasDerivAt (fun u : ℝ ↦ v - u) (-1) 0 := (hasDerivAt_id' 0).const_sub v
  have hpos : 0 < m v := compositionMoment_marginal_pos hp hv.ne'
  have harg := (hm.comp 0 hshift).const_mul (m v)
  have hne : m v * m (v - 0) ≠ 0 := by
    rw [sub_zero]
    exact mul_ne_zero hpos.ne' hpos.ne'
  have hsqrt : HasDerivAt (fun u ↦ Real.sqrt (m v * m (v - u))) (-deriv m v / 2) 0 := by
    apply (harg.sqrt hne).congr_deriv
    simp only [Function.comp_apply, sub_zero, Real.sqrt_mul_self hpos.le, mul_neg, mul_one]
    field_simp [hpos.ne']
  have hsum := (hasDerivAt_logKernel_numerator_zero hp hv).add hsqrt
  simp only [zero_add] at hsum
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ by
    change compositionMoment p u v = compositionMoment p u v -
      Real.sqrt (m v * m (v - u)) + Real.sqrt (m v * m (v - u))
    rw [sub_add_cancel])

theorem G_pos {p : ℕ} (hp : 0 < p) {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    0 < G p c t :=
  div_pos (compositionMoment_marginal_pos hp ht) (mul_pos hc (sq_pos_of_ne_zero ht))

theorem R_pos {p : ℕ} (hp : 0 < p) {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    0 < R p c t := Real.sqrt_pos.2 (G_pos hp hc ht)

private theorem R_sq {p : ℕ} (hp : 0 < p) {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    R p c t ^ 2 = G p c t := Real.sq_sqrt (G_pos hp hc ht).le

private theorem marginal_eq {p : ℕ} {c t : ℝ} (hc : c ≠ 0) (ht : t ≠ 0) :
    compositionMoment p 0 t = c * t ^ 2 * G p c t := by
  unfold G
  exact (mul_div_cancel₀ _ (mul_ne_zero hc (pow_ne_zero 2 ht))).symm

theorem compositionMoment_div_eq {p : ℕ} (hp : 0 < p) {c u v : ℝ}
    (hu : u ≠ 0) (hv : 0 < v) :
    compositionMoment p u v / c = v ^ 2 * G p c v -
      u * (v * G p c v + v ^ 2 * GPrime p c v / 2) + u ^ 2 * A p c u v := by
  have hG : v ^ 2 * G p c v = compositionMoment p 0 v / c := by
    unfold G
    rw [← div_div]
    exact mul_div_cancel₀ _ (pow_ne_zero 2 hv.ne')
  have hGPrime : v ^ 2 * GPrime p c v = deriv (compositionMoment p 0) v / c - 2 * v * G p c v :=
    mul_div_cancel₀ _ (pow_ne_zero 2 hv.ne')
  have hA : u ^ 2 * A p c u v = compositionMoment p u v / c - compositionMoment p 0 v / c +
      u * (deriv (compositionMoment p 0) v / c) / 2 := by
    unfold A
    rw [(hasDerivAt_compositionMoment_left hp hv).deriv, mul_div_cancel₀ _ (pow_ne_zero 2 hu)]
    ring
  linear_combination -hA - hG + (u / 2) * hGPrime

private theorem sqrt_marginal_mul {p : ℕ} (hp : 0 < p) {c s t : ℝ} (hc : 0 < c)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.sqrt (compositionMoment p 0 s * compositionMoment p 0 t) =
      c * |s| * |t| * (R p c s * R p c t) := by
  have harg : compositionMoment p 0 s * compositionMoment p 0 t =
      (c ^ 2 * s ^ 2 * t ^ 2) * (G p c s * G p c t) := by
    rw [marginal_eq hc.ne' hs, marginal_eq hc.ne' ht]
    ring
  rw [harg, Real.sqrt_mul (by positivity : 0 ≤ c ^ 2 * s ^ 2 * t ^ 2),
    Real.sqrt_mul (by positivity : 0 ≤ c ^ 2 * s ^ 2), Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc.le, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (G_pos hp hc hs).le]
  rfl

private theorem normalized_numerator {p : ℕ} (hp : 0 < p) {c u v : ℝ} (hc : 0 < c)
    (hu : 0 < u) (huv : u < v) :
    compositionMoment p u v / c - v * (v - u) * (R p c v * R p c (v - u)) =
      u ^ 2 * (A p c u v - v * GPrime p c v / 2 +
        (v * (v - u) / 2) * ((D p c u v / (R p c v + R p c (v - u))) ^ 2 - Q p c u v)) := by
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  have hD : u * D p c u v = G p c v - G p c (v - u) := mul_div_cancel₀ _ hu.ne'
  have hQ : u * Q p c u v = GPrime p c v - D p c u v := mul_div_cancel₀ _ hu.ne'
  have hsum : 0 < R p c v + R p c (v - u) := add_pos (R_pos hp hc hv.ne') (R_pos hp hc hd.ne')
  have hdiff : R p c v - R p c (v - u) = u * (D p c u v / (R p c v + R p c (v - u))) := by
    rw [← mul_div_assoc, eq_div_iff hsum.ne', hD]
    calc
      _ = R p c v ^ 2 - R p c (v - u) ^ 2 := by ring
      _ = _ := by rw [R_sq hp hc hv.ne', R_sq hp hc hd.ne']
  have hprod : R p c v * R p c (v - u) = (G p c v + G p c (v - u)) / 2 -
      (u * (D p c u v / (R p c v + R p c (v - u)))) ^ 2 / 2 := by
    calc
      _ = (R p c v ^ 2 + R p c (v - u) ^ 2) / 2 - (R p c v - R p c (v - u)) ^ 2 / 2 := by ring
      _ = _ := by rw [R_sq hp hc hv.ne', R_sq hp hc hd.ne', hdiff]
  rw [compositionMoment_div_eq hp hu.ne' hv, hprod]
  linear_combination (u * v * (v - u) / 2) * hQ - (v * (v - u) / 2) * hD

/-- Section 1 of the small-corner certificate, on `0 < u < v`. -/
theorem logKernel_eq_mul_F {p : ℕ} (hp : 0 < p) {c u v : ℝ} (hc : 0 < c)
    (hu : 0 < u) (huv : u < v) : logKernel p u v = (u / v) * F p c u v := by
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  have hRu := R_pos hp hc (neg_ne_zero.mpr hu.ne')
  have hRv := R_pos hp hc (neg_ne_zero.mpr hv.ne')
  have hupper : Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v - u)) =
      c * v * (v - u) * (R p c v * R p c (v - u)) := by
    simpa only [abs_of_pos hv, abs_of_pos hd] using sqrt_marginal_mul hp hc hv.ne' hd.ne'
  have hlower : Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) =
      c * u * v * (R p c (-u) * R p c (-v)) := by
    simpa only [abs_neg, abs_of_pos hu, abs_of_pos hv] using
      sqrt_marginal_mul hp hc (neg_ne_zero.mpr hu.ne') (neg_ne_zero.mpr hv.ne')
  calc
    logKernel p u v =
        (compositionMoment p u v / c - v * (v - u) * (R p c v * R p c (v - u))) /
          (u * v * (R p c (-u) * R p c (-v))) := by
      unfold logKernel
      rw [hupper, hlower]
      field_simp [hc.ne', hu.ne', hv.ne', hRu.ne', hRv.ne']
    _ = _ := by
      rw [normalized_numerator hp hc hu huv]
      unfold F
      field_simp [hu.ne', hv.ne', hRu.ne', hRv.ne']

/-- The certificate uses half the marginal variance for its normalization. -/
theorem logKernel_eq_mul_F_variance {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    logKernel p u v = (u / v) * F p (compositionMarginalVariance p / 2) u v :=
  logKernel_eq_mul_F hp (div_pos (compositionMarginalVariance_pos p) zero_lt_two) hu huv

private theorem mixedDerivative_mul_div (f : ℝ → ℝ → ℝ) {u v fv fuv : ℝ}
    (hv : v ≠ 0)
    (hleft : ∀ᶠ t in 𝓝 v, DifferentiableAt ℝ (fun s ↦ f s t) u)
    (hright : HasDerivAt (f u) fv v)
    (hmixed : HasDerivAt (fun t ↦ deriv (fun s ↦ f s t) u) fuv v) :
    v ^ 2 * deriv (fun t ↦ deriv (fun s ↦ (s / t) * f s t) u) v =
      -f u v - u * deriv (fun s ↦ f s v) u + v * fv + u * v * fuv := by
  have hfirst : (fun t ↦ deriv (fun s ↦ (s / t) * f s t) u) =ᶠ[𝓝 v]
      (fun t ↦ f u t / t + (u / t) * deriv (fun s ↦ f s t) u) := by
    filter_upwards [hleft] with t ht
    have hd := ((hasDerivAt_id' u).div_const t).mul ht.hasDerivAt
    change HasDerivAt (fun s ↦ (s / t) * f s t) _ u at hd
    rw [hd.deriv]
    ring
  have hsecond := (hright.div (hasDerivAt_id' v) hv).add
    (((hasDerivAt_const v u).div (hasDerivAt_id' v) hv).mul hmixed)
  change HasDerivAt (fun t ↦ f u t / t + (u / t) * deriv (fun s ↦ f s t) u) _ v at hsecond
  rw [hfirst.deriv_eq, hsecond.deriv]
  simp only [Pi.div_apply]
  field_simp [hv]
  <;> ring

/-- The scaled mixed derivative used by the small-corner interval bound. -/
theorem logKernel_mixed_scaled {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let f := F p (compositionMarginalVariance p / 2)
    ∀ {fv fuv : ℝ},
      (∀ᶠ t in 𝓝 v, DifferentiableAt ℝ (fun s ↦ f s t) u) →
      HasDerivAt (f u) fv v →
      HasDerivAt (fun t ↦ deriv (fun s ↦ f s t) u) fuv v →
      v ^ 2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v =
        -f u v - u * deriv (fun s ↦ f s v) u + v * fv + u * v * fuv := by
  let f := F p (compositionMarginalVariance p / 2)
  dsimp only
  intro fv fuv hleft hright hmixed
  have heq : (fun t ↦ deriv (fun s ↦ logKernel p s t) u) =ᶠ[𝓝 v]
      (fun t ↦ deriv (fun s ↦ (s / t) * f s t) u) := by
    filter_upwards [Ioi_mem_nhds huv] with t ht
    have hnear : (fun s ↦ logKernel p s t) =ᶠ[𝓝 u] (fun s ↦ (s / t) * f s t) := by
      filter_upwards [Ioo_mem_nhds hu ht] with s hs
      exact logKernel_eq_mul_F_variance hp hs.1 hs.2
    exact hnear.deriv_eq
  rw [heq.deriv_eq]
  exact mixedDerivative_mul_div f (hu.trans huv).ne' hleft hright hmixed

/-- In the double-small corner the exponential argument lies in [-2, 2]. The weight 16
accounts for up to four derivatives of the normalized marginal, or one derivative
in each of the two joint coordinates. -/
theorem weighted_exp_remainder_le {z : ℝ} (hz : |z| ≤ 2) {n : ℕ} (hn : 19 ≤ n) :
    16 * |Real.exp z - ∑ i ∈ Finset.range n, z ^ i / (i.factorial : ℝ)| ≤ 1 / (2 : ℝ) ^ 30 := by
  have hratio : ‖(z : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
    have hnR : (19 : ℝ) ≤ n := by exact_mod_cast hn
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  have htaylor : |Real.exp z - ∑ i ∈ Finset.range n, z ^ i / (i.factorial : ℝ)| ≤
      |z| ^ n / (n.factorial : ℝ) * 2 := by
    exact_mod_cast Complex.exp_bound' hratio
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hfac : (19 : ℕ).factorial * 2 ^ k ≤ (19 + k).factorial := by
    calc
      _ ≤ (19 : ℕ).factorial * 20 ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
      _ ≤ _ := Nat.factorial_mul_pow_le_factorial
  have hfacR : ((19 : ℕ).factorial : ℝ) * 2 ^ k ≤ ((19 + k).factorial : ℝ) := by
    exact_mod_cast hfac
  have hdec : (2 : ℝ) ^ (19 + k) / ((19 + k).factorial : ℝ) ≤
      2 ^ 19 / ((19 : ℕ).factorial : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    rw [pow_add]
    calc
      _ = 2 ^ 19 * (((19 : ℕ).factorial : ℝ) * 2 ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfacR (by positivity)
  calc
    _ ≤ 16 * (|z| ^ (19 + k) / ((19 + k).factorial : ℝ) * 2) := by gcongr
    _ ≤ 16 * (2 ^ (19 + k) / ((19 + k).factorial : ℝ) * 2) := by
      gcongr
    _ ≤ 16 * (2 ^ 19 / ((19 : ℕ).factorial : ℝ) * 2) := by gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

/-- The simplex constraint bounds the joint Taylor argument throughout the double-small
corner, including the interior points used by the integral remainder. -/
theorem composition_exp_remainder_le {p : ℕ} (hp : 0 < p) {g : ℕ × ℕ × ℕ}
    (hg : g ∈ DimThree.gaps p) {s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) (hv : v ≤ 1)
    {n : ℕ} (hn : 19 ≤ n) :
    let z := (3 * (g.2.1 : ℝ) / (p : ℝ) - 1) * s + (3 * (g.2.2 : ℝ) / (p : ℝ) - 1) * v
    16 * |Real.exp z - ∑ i ∈ Finset.range n, z ^ i / (i.factorial : ℝ)| ≤ 1 / (2 : ℝ) ^ 30 := by
  dsimp only
  refine weighted_exp_remainder_le (abs_le.mpr ?_) hn
  let x : ℝ := 3 * (g.2.1 : ℝ) / (p : ℝ)
  let y : ℝ := 3 * (g.2.2 : ℝ) / (p : ℝ)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hsum : x + y ≤ 3 := by
    have hnat : g.2.1 + g.2.2 ≤ p := by
      have h := (DimThree.mem_gaps_iff_total p g).mp hg
      omega
    have hreal : (g.2.1 : ℝ) + (g.2.2 : ℝ) ≤ p := by exact_mod_cast hnat
    dsimp only [x, y]
    rw [← add_div, ← mul_add]
    exact (div_le_iff₀ hpR).mpr (mul_le_mul_of_nonneg_left hreal (by norm_num))
  change -2 ≤ (x - 1) * s + (y - 1) * v ∧ (x - 1) * s + (y - 1) * v ≤ 2
  have hv0 := hs.trans hsv
  have hxy := mul_le_mul_of_nonneg_right hsum hv0
  rw [add_mul] at hxy
  constructor
  · nlinarith only [mul_nonneg hx hs, mul_nonneg hy hv0, hsv, hv]
  · nlinarith only [hxy, mul_le_mul_of_nonneg_left hsv hx, hs, hv]

/-- Integral form of the quadratic exponential remainder. After division by
the square of the gap this identity gives a regular integrand at coalescence. -/
theorem exp_quadratic_remainder_eq_integral (z : ℝ) :
    Real.exp z - 1 - z = z ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (z * t) := by
  have huniq : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc zero_ne_one
  have hderiv (n : ℕ) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      iteratedDerivWithin n (fun x : ℝ ↦ Real.exp (z * x)) (uIcc (0 : ℝ) 1) t =
        z ^ n * Real.exp (z * t) := by
    have hcont : ContDiffAt ℝ (n : ℕ) (fun x : ℝ ↦ Real.exp (z * x)) t := by fun_prop
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hcont ht, iteratedDeriv_exp_const_mul]
  have hcont : ContDiffOn ℝ (1 + 1 : ℕ) (fun x : ℝ ↦ Real.exp (z * x))
      (uIcc (0 : ℝ) 1) := by fun_prop
  have ht := taylor_integral_remainder (n := 1) (x₀ := (0 : ℝ)) (x := 1) hcont
  have hpoly : taylorWithinEval (fun x : ℝ ↦ Real.exp (z * x)) 1 (uIcc (0 : ℝ) 1) 0 1 =
      1 + z := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [hderiv (0 + 1) 0 left_mem_uIcc]
    norm_num [Nat.factorial]
  rw [hpoly, mul_one] at ht
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ = Real.exp z - (1 + z) := by ring
    _ = _ := ht
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [hderiv (1 + 1) t ht]
      norm_num [Nat.factorial]
      ring

/-- The joint quadratic remainder is a finite average of exponential integrals.
This form remains bounded as the first gap tends to zero. -/
theorem A_eq_integral_average (p : ℕ) {c u v : ℝ} (hc : c ≠ 0) (hu : u ≠ 0) :
    A p c u v =
      ((DimThree.gaps p).map fun g ↦
        let x := 3 * (g.2.1 : ℝ) / (p : ℝ) - 1
        let y := 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
        x ^ 2 * Real.exp (y * v) * ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp ((x * u) * t)).sum /
          (((DimThree.gaps p).length : ℝ) * c) := by
  let l := DimThree.gaps p
  let x : (ℕ × ℕ × ℕ) → ℝ := fun g ↦ 3 * (g.2.1 : ℝ) / (p : ℝ) - 1
  let y : (ℕ × ℕ × ℕ) → ℝ := fun g ↦ 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
  let N : ℝ := l.length
  let f := fun g ↦ Real.exp (x g * u + y g * v)
  let m := fun g ↦ Real.exp (y g * v)
  let s := fun g ↦ x g * m g
  let r := fun g ↦ x g ^ 2 * m g *
    ∫ t in (0 : ℝ)..1, (1 - t) * Real.exp ((x g * u) * t)
  have hN : N ≠ 0 := by
    change ((DimThree.gaps p).length : ℝ) ≠ 0
    exact_mod_cast (DimThree.word_counts_all p).2.1.ne'
  have hterm (g : ℕ × ℕ × ℕ) : f g - m g - u * s g = u ^ 2 * r g := by
    have h := exp_quadratic_remainder_eq_integral (x g * u)
    change Real.exp (x g * u + y g * v) - m g - u * (x g * m g) = _
    rw [Real.exp_add]
    linear_combination m g * h
  have hsum (xs : List (ℕ × ℕ × ℕ)) :
      (xs.map f).sum - (xs.map m).sum - u * (xs.map s).sum = u ^ 2 * (xs.map r).sum := by
    induction xs with
    | nil => simp
    | cons g xs ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination hterm g + ih
  have hm0 : compositionMoment p 0 v = (l.map m).sum / N - 1 := by
    unfold compositionMoment
    have heq : (fun g ↦ Real.exp (x g * 0 + y g * v)) = m := by
      funext g
      simp [m]
    change (l.map (fun g ↦ Real.exp (x g * 0 + y g * v))).sum / N - 1 = _
    rw [heq]
  unfold A
  rw [hm0, deriv_compositionMoment_fst_zero]
  change (((l.map f).sum / N - 1) / c - ((l.map m).sum / N - 1) / c -
    u * ((l.map s).sum / N / c)) / u ^ 2 = (l.map r).sum / (N * c)
  calc
    _ = ((l.map f).sum - (l.map m).sum - u * (l.map s).sum) / (N * c * u ^ 2) := by
      field_simp [hN, hc, hu]
      ring
    _ = _ := by
      rw [hsum l]
      field_simp [hN, hc, hu]

/-- The marginal square quotient has an integral expression through zero. -/
theorem G_eq_integral_average {p : ℕ} (hp : 0 < p) {c t : ℝ} (hc : c ≠ 0) (ht : t ≠ 0) :
    G p c t =
      ((DimThree.gaps p).map fun g ↦
        let y := 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
        y ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp ((y * t) * s)).sum /
          (((DimThree.gaps p).length : ℝ) * c) := by
  let l := DimThree.gaps p
  let y : (ℕ × ℕ × ℕ) → ℝ := fun g ↦ 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
  let N : ℝ := l.length
  let f := fun g ↦ Real.exp (y g * t)
  let r := fun g ↦ y g ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp ((y g * t) * s)
  have hN : N ≠ 0 := by
    change ((DimThree.gaps p).length : ℝ) ≠ 0
    exact_mod_cast (DimThree.word_counts_all p).2.1.ne'
  have hterm (g : ℕ × ℕ × ℕ) : f g - 1 - y g * t = t ^ 2 * r g := by
    have h := exp_quadratic_remainder_eq_integral (y g * t)
    change _ = t ^ 2 * (y g ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp ((y g * t) * s))
    linear_combination h
  have hsum (xs : List (ℕ × ℕ × ℕ)) :
      (xs.map f).sum - (xs.length : ℝ) - (xs.map y).sum * t = t ^ 2 * (xs.map r).sum := by
    induction xs with
    | nil => simp
    | cons g xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linear_combination hterm g + ih
  have hz : (l.map y).sum = 0 := composition_last_exponent_sum_zero hp
  have hmain := hsum l
  rw [hz, zero_mul, sub_zero] at hmain
  have hm : compositionMoment p 0 t = (l.map f).sum / N - 1 := by
    unfold compositionMoment
    change (l.map (fun g ↦ Real.exp ((3 * (g.2.1 : ℝ) / (p : ℝ) - 1) * 0 + y g * t))).sum /
        N - 1 = _
    simp [f]
  unfold G
  rw [hm]
  change ((l.map f).sum / N - 1) / (c * t ^ 2) = (l.map r).sum / (N * c)
  calc
    _ = ((l.map f).sum - N) / (N * c * t ^ 2) := by
      field_simp [hN, hc, ht]
    _ = _ := by
      rw [hmain]
      field_simp [hN, hc, ht]

/-- The root term factors as a positive ratio in the upper gap, a convex marginal
root in the gap difference, and a decreasing reciprocal in the lower gap. -/
theorem mixed_deriv_root_term_nonpos {a q c : ℝ → ℝ} {u v a' a'' q' c' : ℝ}
    (ha : HasDerivAt a a' (v - u)) (haa : HasDerivAt (deriv a) a'' (v - u))
    (hdiff : ∀ᶠ t in 𝓝 v, DifferentiableAt ℝ a (t - u))
    (hq : HasDerivAt q q' v) (hc : HasDerivAt c c' u)
    (ha₀ : 0 ≤ a (v - u)) (ha₁ : 0 ≤ a') (ha₂ : 0 ≤ a'')
    (hq₀ : 0 ≤ q v) (hq₁ : 0 ≤ q') (hc₀ : 0 ≤ c u) (hc₁ : c' ≤ 0) :
    deriv (fun t ↦ deriv (fun s ↦ q t * a (t - s) * c s) u) v ≤ 0 := by
  have hfirst : (fun t ↦ deriv (fun s ↦ q t * a (t - s) * c s) u) =ᶠ[𝓝 v]
      (fun t ↦ q t * (a (t - u) * c' - deriv a (t - u) * c u)) := by
    filter_upwards [hdiff] with t ht
    have harg := ht.hasDerivAt.comp u ((hasDerivAt_id' u).const_sub t)
    have h := (harg.const_mul (q t)).mul hc
    change HasDerivAt (fun s ↦ q t * a (t - s) * c s) _ u at h
    rw [h.deriv]
    simp only [Function.comp_apply, mul_neg]
    ring
  have hshift : HasDerivAt (fun t : ℝ ↦ t - u) 1 v := (hasDerivAt_id' v).sub_const u
  have hsecond := hq.mul (((ha.comp v hshift).mul_const c').sub
    ((haa.comp v hshift).mul_const (c u)))
  change HasDerivAt (fun t ↦ q t * (a (t - u) * c' - deriv a (t - u) * c u)) _ v at hsecond
  rw [hfirst.deriv_eq, hsecond.deriv]
  have hval : a (v - u) * c' - a' * c u ≤ 0 :=
    sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos ha₀ hc₁).trans (mul_nonneg ha₁ hc₀))
  have hslope : a' * c' - a'' * c u ≤ 0 :=
    sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos ha₁ hc₁).trans (mul_nonneg ha₂ hc₀))
  have hsign := add_nonpos (mul_nonpos_of_nonneg_of_nonpos hq₁ hval)
    (mul_nonpos_of_nonneg_of_nonpos hq₀ hslope)
  simpa only [Function.comp_apply, Pi.sub_apply, mul_one, ha.deriv, mul_comm, add_comm] using hsign

private theorem triangular_weight_sums (n : ℕ) (a : ℝ) :
    (∑ i ∈ Finset.range (n + 1), (a - (i : ℝ))) =
        ((n : ℝ) + 1) * (2 * a - (n : ℝ)) / 2 ∧
    (∑ i ∈ Finset.range (n + 1), (a - (i : ℝ)) * (i : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) * (3 * a - 2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [Finset.sum_range_succ, ih.1, Nat.cast_succ]
      ring
    · rw [Finset.sum_range_succ, ih.2, Nat.cast_succ]
      ring

/-- The first centered residual sum on the upper side of a triangular lattice law. -/
theorem triangular_upper_residual_sum {p k : ℕ} (hk : k ≤ p) (z : ℝ) :
    let n := p - k
    (∑ i ∈ Finset.range (n + 1),
      ((n : ℝ) + 1 - (i : ℝ)) * (3 * ((k : ℝ) + (i : ℝ)) - (p : ℝ) - z)) =
    (∑ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 - (i : ℝ))) * (2 * (k : ℝ) - z) := by
  let n := p - k
  dsimp only
  change (∑ i ∈ Finset.range (n + 1),
      ((n : ℝ) + 1 - (i : ℝ)) * (3 * ((k : ℝ) + (i : ℝ)) - (p : ℝ) - z)) =
    (∑ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 - (i : ℝ))) * (2 * (k : ℝ) - z)
  have hr (i : ℕ) : ((n : ℝ) + 1 - (i : ℝ)) *
      (3 * ((k : ℝ) + (i : ℝ)) - (p : ℝ) - z) =
      ((n : ℝ) + 1 - (i : ℝ)) * (3 * (k : ℝ) - (p : ℝ) - z) +
        3 * (((n : ℝ) + 1 - (i : ℝ)) * (i : ℝ)) := by ring
  simp_rw [hr, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [(triangular_weight_sums n ((n : ℝ) + 1)).1,
    (triangular_weight_sums n ((n : ℝ) + 1)).2]
  have hnk : (n : ℝ) + (k : ℝ) = (p : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  rw [← hnk]
  ring

/-- The first centered residual sum on the lower side of a triangular lattice law. -/
theorem triangular_lower_residual_sum {p j : ℕ} (hj : j ≤ p) (z : ℝ) :
    (∑ i ∈ Finset.range (j + 1),
      ((p : ℝ) + 1 - (i : ℝ)) * ((p : ℝ) - z - 3 * (i : ℝ))) =
    (∑ i ∈ Finset.range (j + 1), ((p : ℝ) + 1 - (i : ℝ))) *
      ((p : ℝ) - z - (j : ℝ) * (3 * (p : ℝ) + 2 - 2 * (j : ℝ)) /
        (2 * (p : ℝ) + 2 - (j : ℝ))) := by
  have hr (i : ℕ) : ((p : ℝ) + 1 - (i : ℝ)) * ((p : ℝ) - z - 3 * (i : ℝ)) =
      ((p : ℝ) + 1 - (i : ℝ)) * ((p : ℝ) - z) -
        3 * (((p : ℝ) + 1 - (i : ℝ)) * (i : ℝ)) := by ring
  simp_rw [hr]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [(triangular_weight_sums j ((p : ℝ) + 1)).1,
    (triangular_weight_sums j ((p : ℝ) + 1)).2]
  have hjR : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast hj
  have hden : 0 < 2 * (p : ℝ) + 2 - (j : ℝ) := by
    have hpR : 0 ≤ (p : ℝ) := by positivity
    linarith
  have hratio : ((j : ℝ) + 1) * (2 * ((p : ℝ) + 1) - (j : ℝ)) / 2 *
        ((j : ℝ) * (3 * (p : ℝ) + 2 - 2 * (j : ℝ)) / (2 * (p : ℝ) + 2 - j)) =
      3 * ((j : ℝ) * ((j : ℝ) + 1) * (3 * ((p : ℝ) + 1) - 2 * (j : ℝ) - 1) / 6) := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hden.ne').mpr
    ring
  nlinarith only [hratio]

/-- The triangular count weights give a larger positive residual distance.
The lower and upper cutoffs are controlled by the two adjacent lattice indices. -/
theorem triangular_tail_mean_gap {p k j : ℕ} (hp : 11 ≤ p)
    (hk : 2 * p / 3 ≤ k + j) (hj : j ≤ p / 3) (z : ℝ) :
    (p : ℝ) - z - (j : ℝ) * (3 * (p : ℝ) + 2 - 2 * (j : ℝ)) /
        (2 * (p : ℝ) + 2 - (j : ℝ)) < 2 * (k : ℝ) - z := by
  let n := p / 3
  let q := 2 * p / 3
  have hnj : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hqk : (q : ℝ) ≤ (k : ℝ) + (j : ℝ) := by exact_mod_cast hk
  have hjp : (j : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show j ≤ p by omega)
  let den : ℝ := 2 * (p : ℝ) + 2 - (j : ℝ)
  have hden : 0 < den := by
    have hp₀ : 0 ≤ (p : ℝ) := by positivity
    linarith [show den = 2 * (p : ℝ) + 2 - (j : ℝ) by rfl]
  have hmul := mul_le_mul_of_nonneg_left hnj (show 0 ≤ (q : ℝ) + 1 by positivity)
  have hlower : 0 < (q : ℝ) * (2 * (p : ℝ) + 2) - (p : ℝ) ^ 2 - (p : ℝ) -
      ((q : ℝ) + 1) * (n : ℝ) := by
    rcases (show p = 3 * n ∨ p = 3 * n + 1 ∨ p = 3 * n + 2 by dsimp only [n]; omega)
      with hp₀ | hp₁ | hp₂
    · have hq : q = 2 * n := by dsimp only [q]; omega
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
      have hpR : (p : ℝ) = 3 * (n : ℝ) := by exact_mod_cast hp₀
      have hqR : (q : ℝ) = 2 * (n : ℝ) := by exact_mod_cast hq
      rw [hpR, hqR]
      nlinarith [sq_nonneg ((n : ℝ) - 4)]
    · have hq : q = 2 * n := by dsimp only [q]; omega
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
      have hpR : (p : ℝ) = 3 * (n : ℝ) + 1 := by exact_mod_cast hp₁
      have hqR : (q : ℝ) = 2 * (n : ℝ) := by exact_mod_cast hq
      rw [hpR, hqR]
      nlinarith [sq_nonneg ((n : ℝ) - 4)]
    · have hq : q = 2 * n + 1 := by dsimp only [q]; omega
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hpR : (p : ℝ) = 3 * (n : ℝ) + 2 := by exact_mod_cast hp₂
      have hqR : (q : ℝ) = 2 * (n : ℝ) + 1 := by exact_mod_cast hq
      rw [hpR, hqR]
      nlinarith [sq_nonneg ((n : ℝ) - 3)]
  have hprod := mul_le_mul_of_nonneg_right (show (q : ℝ) - j ≤ k by linarith) hden.le
  have hgap : 0 < (k : ℝ) * den - ((p : ℝ) - j) * ((p : ℝ) - j + 1) := by
    dsimp only [den] at hprod ⊢
    nlinarith only [hlower, hmul, hprod]
  apply sub_pos.mp
  change 0 < 2 * (k : ℝ) - z -
    ((p : ℝ) - z - (j : ℝ) * (3 * (p : ℝ) + 2 - 2 * (j : ℝ)) / den)
  calc
    0 < 2 * ((k : ℝ) * den - ((p : ℝ) - j) * ((p : ℝ) - j + 1)) / den :=
      div_pos (mul_pos zero_lt_two hgap) hden
    _ = _ := by
      field_simp [hden.ne']
      dsimp only [den]
      ring

/-- Integral representations of the first and repeated-node divided differences.
These are the expressions evaluated near the lower collision. -/
theorem divided_differences_eq_integral {g g₁ g₂ : ℝ → ℝ} {u v : ℝ} (hu : u ≠ 0)
    (hg₁ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g₁ (v - t * u)) (v - t * u))
    (hg₂ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g₁ (g₂ (v - t * u)) (v - t * u))
    (h₁ : IntervalIntegrable (fun t ↦ g₁ (v - t * u)) volume 0 1)
    (h₂ : IntervalIntegrable (fun t ↦ (1 - t) * g₂ (v - t * u)) volume 0 1) :
    let d := (g v - g (v - u)) / u
    d = (∫ t in (0 : ℝ)..1, g₁ (v - t * u)) ∧
      (g₁ v - d) / u = (∫ t in (0 : ℝ)..1, (1 - t) * g₂ (v - t * u)) := by
  have hpath (t : ℝ) : HasDerivAt (fun r : ℝ ↦ v - r * u) (-u) t := by
    simpa only [one_mul] using ((hasDerivAt_id' t).mul_const u).const_sub v
  have hpath₁ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun r ↦ g (v - r * u)) (-u * g₁ (v - t * u)) t := by
    have h := (hg₁ t ht).comp t (hpath t)
    change HasDerivAt (fun r ↦ g (v - r * u)) (g₁ (v - t * u) * -u) t at h
    simpa only [mul_comm (g₁ (v - t * u)) (-u)] using h
  have hftc₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath₁ (h₁.const_mul (-u))
  rw [intervalIntegral.integral_const_mul] at hftc₁
  simp only [zero_mul, one_mul, sub_zero] at hftc₁
  have hd : (g v - g (v - u)) / u = ∫ t in (0 : ℝ)..1, g₁ (v - t * u) := by
    apply (div_eq_iff hu).mpr
    linarith only [hftc₁]
  have hpath₂ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun r ↦ (1 - r) * g₁ (v - r * u))
        (-g₁ (v - t * u) - u * ((1 - t) * g₂ (v - t * u))) t := by
    have hlinear := (hasDerivAt_id' t).const_sub 1
    have hcompose := (hg₂ t ht).comp t (hpath t)
    apply (hlinear.mul hcompose).congr_deriv
    simp only [Function.comp_apply]
    ring
  have hneg : IntervalIntegrable (fun t ↦ -g₁ (v - t * u)) volume 0 1 := h₁.neg
  have hftc₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath₂
    (hneg.sub (h₂.const_mul u))
  rw [intervalIntegral.integral_sub hneg (h₂.const_mul u), intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul] at hftc₂
  simp only [zero_mul, sub_zero, sub_self, zero_mul, one_mul, zero_sub] at hftc₂
  dsimp only
  refine ⟨hd, ?_⟩
  rw [hd]
  apply (div_eq_iff hu).mpr
  linarith only [hftc₂]

/-- Both divided differences use the ordinary derivatives of the normalized
marginal on the nonzero segment between the gaps. -/
theorem D_Q_eq_integrals (p : ℕ) {c u v : ℝ} (hc : c ≠ 0) (hu : 0 < u) (huv : u < v) :
    D p c u v = (∫ t in (0 : ℝ)..1, deriv (G p c) (v - t * u)) ∧
      Q p c u v = (∫ t in (0 : ℝ)..1, (1 - t) * deriv (deriv (G p c)) (v - t * u)) := by
  have hG : ContDiffOn ℝ 2 (G p c) (Ioi (0 : ℝ)) := by
    unfold G
    apply (contDiff_marginal p 2).contDiffOn.div (by fun_prop)
    intro t ht
    exact mul_ne_zero hc (pow_ne_zero _ (show 0 < t from ht).ne')
  have hG' : ContDiffOn ℝ 1 (deriv (G p c)) (Ioi (0 : ℝ)) :=
    hG.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hG'' : ContinuousOn (deriv (deriv (G p c))) (Ioi (0 : ℝ)) :=
    hG'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hmem : MapsTo (fun t : ℝ ↦ v - t * u) (uIcc (0 : ℝ) 1) (Ioi (0 : ℝ)) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have htu := mul_le_mul_of_nonneg_right ht.2 hu.le
    exact sub_pos.mpr (lt_of_le_of_lt (by simpa only [one_mul] using htu) huv)
  have hcont : ContinuousOn (fun t : ℝ ↦ v - t * u) (uIcc (0 : ℝ) 1) := by fun_prop
  have hd₁ : IntervalIntegrable (fun t ↦ deriv (G p c) (v - t * u)) volume 0 1 :=
    (hG'.continuousOn.comp hcont hmem).intervalIntegrable
  have hd₂ : IntervalIntegrable (fun t ↦ (1 - t) * deriv (deriv (G p c)) (v - t * u)) volume 0 1 :=
    ((show ContinuousOn (fun t : ℝ ↦ 1 - t) (uIcc (0 : ℝ) 1) by fun_prop).mul
    (hG''.comp hcont hmem)).intervalIntegrable
  have h₁ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (G p c) (deriv (G p c) (v - t * u)) (v - t * u) :=
    ((hG.contDiffAt (Ioi_mem_nhds (hmem ht))).differentiableAt (by norm_num)).hasDerivAt
  have h₂ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (deriv (G p c)) (deriv (deriv (G p c)) (v - t * u)) (v - t * u) :=
    ((hG'.contDiffAt (Ioi_mem_nhds (hmem ht))).differentiableAt (by norm_num)).hasDerivAt
  simpa only [D, Q, (hasDerivAt_G p hc (hu.trans huv).ne').deriv] using
    divided_differences_eq_integral hu.ne' h₁ h₂ hd₁ hd₂

 /-- A continuous weight on the compact integration interval can be
differentiated against an exponential in the parameter. -/
private theorem hasDerivAt_weighted_exp_integral (w a : ℝ → ℝ)
    (hw : Continuous w) (ha : Continuous a) (t : ℝ) :
    HasDerivAt (fun x ↦ ∫ s in (0 : ℝ)..1, w s * Real.exp (x * a s))
      (∫ s in (0 : ℝ)..1, w s * a s * Real.exp (t * a s)) t := by
  let f (x s : ℝ) := w s * Real.exp (x * a s)
  let f' (x s : ℝ) := w s * a s * Real.exp (x * a s)
  let parameters := Icc (t - 1) (t + 1)
  have hcompact : IsCompact (parameters ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hcontinuous : Continuous (fun z : ℝ × ℝ ↦ f' z.1 z.2) := by
    dsimp only [f']
    fun_prop
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcontinuous.continuousOn
  have hnbhd : parameters ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hf (x : ℝ) : Continuous (f x) := by
    dsimp only [f]
    fun_prop
  have hfp (x : ℝ) : Continuous (f' x) := by
    dsimp only [f']
    fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := f) (F' := f') (bound := fun _ ↦ C)
    hnbhd (.of_forall fun x ↦ (hf x).aestronglyMeasurable)
    ((hf t).intervalIntegrable 0 1) (hfp t).aestronglyMeasurable ?_
    (continuous_const.intervalIntegrable 0 1) ?_).2
  · filter_upwards with s hs x hx
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩
    exact hC (x, s) ⟨hx, hs'⟩
  · filter_upwards with s _ x _
    have h := (((hasDerivAt_id' x).mul_const (a s)).exp.const_mul (w s))
    change HasDerivAt (fun y ↦ f y s) _ x at h
    apply h.congr_deriv
    simp only [f', mul_one, one_mul]
    ring

/-- Differentiating the regularized scalar exponential moment adds a
power of the same exponent in the integrand. -/
theorem hasDerivAt_exponential_moment_integral (b : ℝ) (order : ℕ) (t : ℝ) :
    HasDerivAt (fun x ↦ ∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ order * Real.exp (x * (b * s)))
      (∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ (order + 1) * Real.exp (t * (b * s))) t := by
  simpa only [pow_succ, mul_assoc] using
    hasDerivAt_weighted_exp_integral (fun s ↦ (1 - s) * (b * s) ^ order)
      (fun s ↦ b * s) (by fun_prop) (by fun_prop) t

 /-- The integral formula for the normalized marginal and its derivatives,
continued through the origin. -/
def integralMarginalDerivative (p : ℕ) (c : ℝ) (order : ℕ) (t : ℝ) : ℝ :=
  ((DimThree.gaps p).map fun g ↦
    let y := 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
    y ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * (y * s) ^ order * Real.exp (t * (y * s))).sum /
      (((DimThree.gaps p).length : ℝ) * c)

private theorem hasDerivAt_integralMarginalDerivative (p : ℕ) (c : ℝ)
    (order : ℕ) (t : ℝ) :
    HasDerivAt (integralMarginalDerivative p c order)
      (integralMarginalDerivative p c (order + 1) t) t := by
  let y : (ℕ × ℕ × ℕ) → ℝ := fun g ↦ 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
  let f (k : ℕ) (g : ℕ × ℕ × ℕ) (x : ℝ) :=
    (y g) ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * (y g * s) ^ k * Real.exp (x * (y g * s))
  have h (l : List (ℕ × ℕ × ℕ)) :
      HasDerivAt (fun x ↦ (l.map fun g ↦ f order g x).sum)
        ((l.map fun g ↦ f (order + 1) g t).sum) t := by
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const t (0 : ℝ)
    | cons g l ih =>
      have hg : HasDerivAt (f order g) (f (order + 1) g t) t :=
        (hasDerivAt_exponential_moment_integral (y g) order t).const_mul ((y g) ^ 2)
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using hg.add ih
  exact (h (DimThree.gaps p)).div_const _

/-- Each derivative needed by the interval witness is the corresponding
exponential moment integral. The normalized marginal agrees with this
formula wherever its original quotient is defined. -/
theorem iteratedDeriv_G_eq_integral {p : ℕ} (hp : 0 < p) {c t : ℝ} (hc : c ≠ 0)
    (ht : t ≠ 0) (order : ℕ) :
    iteratedDeriv order (G p c) t = integralMarginalDerivative p c order t := by
  have hgAt : G p c =ᶠ[𝓝 t] integralMarginalDerivative p c 0 := by
    filter_upwards [eventually_ne_nhds ht] with x hx
    rw [G_eq_integral_average hp hc hx]
    unfold integralMarginalDerivative
    simp only [pow_zero, mul_one, mul_assoc, mul_left_comm x]
  have hderiv (k : ℕ) : iteratedDeriv k (integralMarginalDerivative p c 0) =
      integralMarginalDerivative p c k := by
    induction k with
    | zero => rw [iteratedDeriv_zero]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_integralMarginalDerivative p c k x).deriv
  exact (Filter.EventuallyEq.iteratedDeriv_eq order hgAt).trans (congrFun (hderiv order) t)

theorem unit_weight_moment (k : ℕ) :
    (∫ s in (0 : ℝ)..1, (1 - s) * s ^ k) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have h (s : ℝ) : (1 - s) * s ^ k = s ^ k - s ^ (k + 1) := by
    rw [pow_succ]
    ring
  simp_rw [h]
  have hint (n : ℕ) : IntervalIntegrable (fun s : ℝ ↦ s ^ n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub (hint k) (hint (k + 1)), integral_pow, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one]
  have hk : 0 ≤ (k : ℝ) := by positivity
  field_simp
  ring

/-- Outward Taylor error for the weighted exponential integrals in the
small-corner certificate. The weight integrates to one half. -/
theorem weighted_exponential_moment_integral_error {b t : ℝ} (hb : |b| ≤ 2) (ht : |t| ≤ 1)
    {order n : ℕ} (hk : order ≤ 4) (hn : 19 ≤ n) :
    |(∫ s in (0 : ℝ)..1, (1 - s) * (b * s) ^ order * Real.exp (t * (b * s))) -
        (∑ i ∈ Finset.range n,
          b ^ (order + i) * t ^ i /
            ((i.factorial : ℝ) * (((order + i : ℕ) : ℝ) + 1) * (((order + i : ℕ) : ℝ) + 2)))|
      ≤ 1 / (2 : ℝ) ^ 31 := by
  let value (s : ℝ) := (1 - s) * (b * s) ^ order * Real.exp (t * (b * s))
  let pol (s : ℝ) := (1 - s) * (b * s) ^ order *
    ∑ i ∈ Finset.range n, (t * (b * s)) ^ i / (i.factorial : ℝ)
  have hpol :
      (∫ s in (0 : ℝ)..1, pol s) =
        ∑ i ∈ Finset.range n, b ^ (order + i) * t ^ i /
          ((i.factorial : ℝ) * (((order + i : ℕ) : ℝ) + 1) * (((order + i : ℕ) : ℝ) + 2)) := by
    simp only [pol, Finset.mul_sum]
    refine (intervalIntegral.integral_finsetSum (fun i _ ↦ ?_)).trans ?_
    · apply Continuous.intervalIntegrable
      fun_prop
    apply Finset.sum_congr rfl
    intro i _
    have heq (s : ℝ) :
        (1 - s) * (b * s) ^ order * ((t * (b * s)) ^ i / (i.factorial : ℝ)) =
          (b ^ (order + i) * t ^ i / (i.factorial : ℝ)) * ((1 - s) * s ^ (order + i)) := by
      simp only [mul_pow, pow_add]
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, unit_weight_moment]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_assoc]
    ac_rfl
  have hv : IntervalIntegrable value volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [value]
    fun_prop
  have hp : IntervalIntegrable pol volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [pol]
    fun_prop
  let ε : ℝ := 1 / (2 : ℝ) ^ 30
  have hbnd : ∀ s ∈ Ioc (0 : ℝ) 1, ‖value s - pol s‖ ≤ ε * (1 - s) := by
    intro s hs
    have hbs : |b * s| ≤ 2 := by
      rw [abs_mul, abs_of_pos hs.1]
      nlinarith [mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hs.2)]
    have hz : |t * (b * s)| ≤ 2 := by
      rw [abs_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (abs_nonneg (b * s))]
    have hpow : |b * s| ^ order ≤ 16 :=
      (pow_le_pow_left₀ (abs_nonneg _) hbs _).trans
        (by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
          exact pow_le_pow_right₀ (by norm_num) hk)
    have herr := weighted_exp_remainder_le hz hn
    dsimp only [value, pol]
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_pow]
    calc
      _ = (1 - s) * (|b * s| ^ order * |Real.exp (t * (b * s)) -
          ∑ i ∈ Finset.range n, (t * (b * s)) ^ i / (i.factorial : ℝ)|) := by ring
      _ ≤ (1 - s) * ε := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans herr) (sub_nonneg.mpr hs.2)
      _ = _ := mul_comm _ _
  have hint : IntervalIntegrable (fun s : ℝ ↦ ε * (1 - s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall hbnd) hint
  rw [← hpol, ← intervalIntegral.integral_sub hv hp]
  rw [intervalIntegral.integral_const_mul] at h
  have hhalf : (∫ s in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    simpa using unit_weight_moment 0
  rw [hhalf, Real.norm_eq_abs] at h
  convert h using 1 <;> norm_num [ε]

#print axioms weighted_exponential_moment_integral_error
#print axioms iteratedDeriv_G_eq_integral
#print axioms hasDerivAt_exponential_moment_integral
#print axioms D_Q_eq_integrals
#print axioms divided_differences_eq_integral
#print axioms triangular_upper_residual_sum
#print axioms triangular_lower_residual_sum
#print axioms triangular_tail_mean_gap
#print axioms mixed_deriv_root_term_nonpos
#print axioms G_eq_integral_average
#print axioms A_eq_integral_average
#print axioms exp_quadratic_remainder_eq_integral
#print axioms composition_exp_remainder_le
#print axioms weighted_exp_remainder_le
#print axioms logKernel_mixed_scaled
#print axioms hasDerivAt_G
#print axioms hasDerivAt_compositionMoment_left
#print axioms compositionMoment_div_eq
#print axioms logKernel_eq_mul_F
#print axioms logKernel_eq_mul_F_variance

end RefinedBMV.PositiveCenter.SmallCorner
