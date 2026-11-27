/- GID: D5/S3/Analytic/Resolvent/EntireLogDerivPowers
   generality: G
   mirror-B: D5/B/S3/Analytic/Resolvent/EntireLogDerivPowers
   mirror-E: none(waiver:complex-analytic-zero-sum)
   anchors: []
   utility: none
   digest: Higher logarithmic derivatives are absolutely convergent zero power sums. -/

import D5.S3.Analytic.Resolvent.EntireLogDerivDifference
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Termwise differentiation of the zero resolvent near any nonzero center. -/

noncomputable section
namespace D5.S3.Analytic.Resolvent.EntireLogDerivPowers
open Complex Filter Set Topology
open D5.S3.Analytic.Resolvent.EntireLogDerivDifference

private theorem local_inverse_bounds {a y ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : 2 * δ ≤ ‖a - ρ‖) (hy : y ∈ Metric.ball a δ) :
    ‖(y - ρ)⁻¹‖ ≤ 2 * ‖(a - ρ)⁻¹‖ ∧ ‖(y - ρ)⁻¹‖ ≤ δ⁻¹ := by
  have hya : ‖y - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  have htri : ‖a - ρ‖ ≤ ‖y - a‖ + ‖y - ρ‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev a y] using
      norm_add_le (a - y) (y - ρ)
  have hd : δ ≤ ‖y - ρ‖ := by linarith
  have ha : 0 < ‖a - ρ‖ := by linarith
  have hp : 0 < ‖y - ρ‖ := hδ.trans_le hd
  simp only [norm_inv]
  constructor
  · calc
      (‖y - ρ‖)⁻¹ = 1 / ‖y - ρ‖ := by simp
      _ ≤ 2 / ‖a - ρ‖ := (div_le_div_iff₀ hp ha).mpr (by nlinarith)
      _ = 2 * (‖a - ρ‖)⁻¹ := by ring
  · exact inv_anti₀ hδ hd

private theorem local_power_bound {a y ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : 2 * δ ≤ ‖a - ρ‖) (hy : y ∈ Metric.ball a δ) (n : ℕ) :
    ‖(y - ρ)⁻¹ ^ (n + 2)‖ ≤
      4 * (δ⁻¹) ^ n * ‖(a - ρ)⁻¹‖ ^ 2 := by
  obtain ⟨hcomp, hbound⟩ := local_inverse_bounds hδ hsep hy
  rw [norm_pow, pow_add]
  calc
    _ ≤ (δ⁻¹) ^ n * (2 * ‖(a - ρ)⁻¹‖) ^ 2 := by gcongr
    _ = _ := by ring

private theorem power_summable {ι : Type*} (ρ : ι → ℂ) (m : ι → ℕ)
    {a : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ i, 2 * δ ≤ ‖a - ρ i‖)
    (hs : Summable (fun i => (m i : ℝ) * ‖(a - ρ i)⁻¹‖ ^ 2))
    (n : ℕ) : Summable (fun i => (m i : ℂ) * (a - ρ i)⁻¹ ^ (n + 2)) := by
  apply (hs.mul_left (4 * δ⁻¹ ^ n)).of_norm_bounded
  intro i
  rw [norm_mul, Complex.norm_natCast]
  have hb := local_power_bound hδ (hsep i) (Metric.mem_ball_self hδ) n
  nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (m i))]

private theorem power_hasDerivAt {ι : Type*} (ρ : ι → ℂ) (m : ι → ℕ)
    {a : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ i, 2 * δ ≤ ‖a - ρ i‖)
    (hs : Summable (fun i => (m i : ℝ) * ‖(a - ρ i)⁻¹‖ ^ 2)) (n : ℕ) :
    HasDerivAt (fun y => ∑' i, (m i : ℂ) * (y - ρ i)⁻¹ ^ (n + 2))
      (-(n + 2 : ℂ) * ∑' i, (m i : ℂ) * (a - ρ i)⁻¹ ^ (n + 3)) a := by
  let g' := fun i y => -(n + 2 : ℂ) * (m i : ℂ) * (y - ρ i)⁻¹ ^ (n + 3)
  have hd (i : ι) (y : ℂ) (hy : y ∈ Metric.ball a δ) :
      HasDerivAt (fun y => (m i : ℂ) * (y - ρ i)⁻¹ ^ (n + 2)) (g' i y) y := by
    have hn : y - ρ i ≠ 0 := by
      have ht : ‖a - ρ i‖ ≤ ‖y - a‖ + ‖y - ρ i‖ := by
        simpa only [sub_add_sub_cancel, norm_sub_rev a y] using
          norm_add_le (a - y) (y - ρ i)
      have hya : ‖y - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      intro he
      simp only [he, norm_zero, add_zero] at ht
      linarith [hsep i]
    have he := ((((hasDerivAt_id y).sub_const (ρ i)).inv hn).pow (n + 2)).const_mul
      (m i : ℂ)
    apply he.congr_deriv
    change (m i : ℂ) * (((n + 2 : ℕ) : ℂ) * (y - ρ i)⁻¹ ^ (n + 2 - 1) *
      (-1 / (y - ρ i) ^ 2)) = -(n + 2 : ℂ) * (m i : ℂ) * (y - ρ i)⁻¹ ^ (n + 3)
    have hdiv : (-1 : ℂ) / (y - ρ i) ^ 2 = -((y - ρ i)⁻¹ ^ 2) := by
      rw [inv_pow]
      ring
    rw [show n + 2 - 1 = n + 1 by omega, hdiv]
    push_cast
    ring
  have hb (i : ι) (y : ℂ) (hy : y ∈ Metric.ball a δ) :
      ‖g' i y‖ ≤ ((n + 2 : ℝ) * (4 * δ⁻¹ ^ (n + 1))) *
        ((m i : ℝ) * ‖(a - ρ i)⁻¹‖ ^ 2) := by
    have hh := local_power_bound hδ (hsep i) hy (n + 1)
    dsimp [g']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast]
    have hnc : ‖(n + 2 : ℂ)‖ = (n + 2 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using Complex.norm_natCast (n + 2)
    rw [hnc]
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at *
    have hpos : 0 ≤ (n + 2 : ℝ) * (m i : ℝ) := by positivity
    convert mul_le_mul_of_nonneg_left hh hpos using 1 <;> ring
  have hh := hasDerivAt_tsum_of_isPreconnected
    (hs.mul_left ((n + 2 : ℝ) * (4 * δ⁻¹ ^ (n + 1))))
    Metric.isOpen_ball (convex_ball a δ).isPreconnected hd hb
    (Metric.mem_ball_self hδ) (power_summable ρ m hδ hsep hs n)
    (Metric.mem_ball_self hδ)
  convert hh using 1
  dsimp [g']
  rw [← tsum_mul_left]
  congr 1
  ext i
  ring

private theorem difference_hasDerivAt {ι : Type*} (ρ : ι → ℂ) (m : ι → ℕ)
    {a : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ i, 2 * δ ≤ ‖a - ρ i‖)
    (hs : Summable (fun i => (m i : ℝ) * ‖(a - ρ i)⁻¹‖ ^ 2)) :
    HasDerivAt (fun y => ∑' i, (m i : ℂ) * ((y - ρ i)⁻¹ - (a - ρ i)⁻¹))
      (-(∑' i, (m i : ℂ) * (a - ρ i)⁻¹ ^ 2)) a := by
  let g' := fun i y => -(m i : ℂ) * (y - ρ i)⁻¹ ^ 2
  have hd (i : ι) (y : ℂ) (hy : y ∈ Metric.ball a δ) :
      HasDerivAt (fun y => (m i : ℂ) * ((y - ρ i)⁻¹ - (a - ρ i)⁻¹))
        (g' i y) y := by
    have hn : y - ρ i ≠ 0 := by
      have ht : ‖a - ρ i‖ ≤ ‖y - a‖ + ‖y - ρ i‖ := by
        simpa only [sub_add_sub_cancel, norm_sub_rev a y] using
          norm_add_le (a - y) (y - ρ i)
      have hya : ‖y - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      intro he
      simp only [he, norm_zero, add_zero] at ht
      linarith [hsep i]
    have he := (((((hasDerivAt_id y).sub_const (ρ i)).inv hn).sub_const
      ((a - ρ i)⁻¹)).const_mul (m i : ℂ))
    apply he.congr_deriv
    dsimp only [g', id_eq]
    field_simp
  have hb (i : ι) (y : ℂ) (hy : y ∈ Metric.ball a δ) :
      ‖g' i y‖ ≤ 4 * ((m i : ℝ) * ‖(a - ρ i)⁻¹‖ ^ 2) := by
    have hh := local_power_bound hδ (hsep i) hy 0
    dsimp [g']
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    norm_num only [pow_zero, mul_one, zero_add] at hh
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (m i))]
  have hh := hasDerivAt_tsum_of_isPreconnected (hs.mul_left 4)
    Metric.isOpen_ball (convex_ball a δ).isPreconnected hd hb (Metric.mem_ball_self hδ)
    (by simp : Summable (fun i => (m i : ℂ) * ((a - ρ i)⁻¹ - (a - ρ i)⁻¹)))
    (Metric.mem_ball_self hδ)
  convert hh using 1
  dsimp [g']
  rw [← tsum_neg]
  congr 1
  ext i
  ring

private theorem local_separation {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a : ℂ} (ha : F a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {z : ℂ // F z = 0}, 2 * δ ≤ ‖a - ρ.1‖ := by
  have hopen : IsOpen {z : ℂ | F z ≠ 0} := isOpen_ne_fun hF.continuous continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen a ha
  refine ⟨r / 2, by positivity, fun ρ => ?_⟩
  by_contra h
  have hh : ρ.1 ∈ Metric.ball a r := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  exact hball hh ρ.2

private theorem square_summable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    {a : ℂ} (ha : F a ≠ 0) :
    Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) * ‖(a - ρ.1)⁻¹‖ ^ 2) := by
  obtain ⟨δ, hδ, hseparation⟩ := local_separation hF ha
  have hsep (ρ : {z : ℂ // F z = 0}) : δ ≤ ‖a - ρ.1‖ := by
    linarith [hseparation ρ]
  apply ((entire_zero_summable (a := a) hF hα hg).1.mul_left
    (1 + (δ ^ 2)⁻¹)).of_nonneg_of_le (fun _ => by positivity)
  intro ρ
  have hd : 0 < ‖a - ρ.1‖ := hδ.trans_le (hsep ρ)
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hsq : δ ^ 2 ≤ ‖a - ρ.1‖ ^ 2 := by gcongr; exact hsep ρ
  have hr : 1 ≤ ‖a - ρ.1‖ ^ 2 / δ ^ 2 := by
    exact (le_div_iff₀ hδ2).mpr (by simpa using hsq)
  have hb : ‖(a - ρ.1)⁻¹‖ ^ 2 ≤
      (1 + (δ ^ 2)⁻¹) / (1 + ‖ρ.1 - a‖ ^ 2) := by
    rw [norm_inv, inv_pow]
    apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos hd)).mpr
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 1 + ‖ρ.1 - a‖ ^ 2)]
    rw [norm_sub_rev ρ.1 a]
    change 1 ≤ ‖a - ρ.1‖ ^ 2 * (δ ^ 2)⁻¹ at hr
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb
    (Nat.cast_nonneg (analyticOrderNatAt F ρ.1))
  convert hm using 1 <;> ring

private theorem first_derivative {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    {a : ℂ} (ha : F a ≠ 0) :
    deriv (logDeriv F) a = -(∑' ρ : {z : ℂ // F z = 0},
      (analyticOrderNatAt F ρ.1 : ℂ) * (a - ρ.1)⁻¹ ^ 2) := by
  obtain ⟨δ, hδ, hsep⟩ := local_separation hF ha
  have hd := difference_hasDerivAt (fun ρ : {z : ℂ // F z = 0} => ρ.1)
    (fun ρ => analyticOrderNatAt F ρ.1) hδ hsep (square_summable hF hα hg ha)
  have he : (fun y => ∑' ρ : {z : ℂ // F z = 0},
      (analyticOrderNatAt F ρ.1 : ℂ) * ((y - ρ.1)⁻¹ - (a - ρ.1)⁻¹)) =ᶠ[𝓝 a]
      (fun y => logDeriv F y - logDeriv F a) := by
    filter_upwards [(isOpen_ne_fun hF.continuous continuous_const).mem_nhds ha] with y hy
    exact (entire_logDeriv_difference_hasSum hF hα hg ha hy).tsum_eq
  have hh := (hd.congr_of_eventuallyEq he.symm).deriv
  simpa only [deriv_sub_const] using hh

private theorem derivative_formula {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    (k : ℕ) (hk : 1 ≤ k) {a : ℂ} (ha : F a ≠ 0) :
    iteratedDeriv k (logDeriv F) a = (-1 : ℂ) ^ k * k.factorial *
      ∑' ρ : {z : ℂ // F z = 0}, (analyticOrderNatAt F ρ.1 : ℂ) *
        (a - ρ.1)⁻¹ ^ (k + 1) := by
  induction k, hk using Nat.le_induction generalizing a with
  | base => simpa using first_derivative hF hα hg ha
  | succ k hk ih =>
    have he : iteratedDeriv k (logDeriv F) =ᶠ[𝓝 a]
        (fun y => (-1 : ℂ) ^ k * k.factorial *
          ∑' ρ : {z : ℂ // F z = 0}, (analyticOrderNatAt F ρ.1 : ℂ) *
            (y - ρ.1)⁻¹ ^ (k + 1)) := by
      filter_upwards [(isOpen_ne_fun hF.continuous continuous_const).mem_nhds ha] with y hy
      exact ih hy
    obtain ⟨δ, hδ, hsep⟩ := local_separation hF ha
    have hd := (power_hasDerivAt (fun ρ : {z : ℂ // F z = 0} => ρ.1)
      (fun ρ => analyticOrderNatAt F ρ.1) hδ hsep
      (square_summable hF hα hg ha) (k - 1)).const_mul
      ((-1 : ℂ) ^ k * k.factorial)
    have hn : k - 1 + 2 = k + 1 := by omega
    have hn' : k - 1 + 3 = k + 2 := by omega
    rw [iteratedDeriv_succ, he.deriv_eq]
    rw [hn, hn'] at hd
    have hc : ((k - 1 : ℕ) : ℂ) + 2 = (k : ℂ) + 1 := by
      exact_mod_cast hn
    rw [hc] at hd
    rw [hd.deriv]
    push_cast
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    ring

/-- All positive-order logarithmic derivatives equal absolutely convergent,
multiplicity-weighted inverse powers of the entire function's zero divisor. -/
theorem entire_logDeriv_power_hasSum {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    (k : ℕ) (hk : 1 ≤ k) {a : ℂ} (ha : F a ≠ 0) :
    HasSum (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℂ) * (a - ρ.1)⁻¹ ^ (k + 1))
      (((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k (logDeriv F) a) := by
  obtain ⟨δ, hδ, hsep⟩ := local_separation hF ha
  have hs := power_summable (fun ρ : {z : ℂ // F z = 0} => ρ.1)
    (fun ρ => analyticOrderNatAt F ρ.1) hδ hsep
    (square_summable hF hα hg ha) (k - 1)
  have hn : k - 1 + 2 = k + 1 := by omega
  rw [hn] at hs
  convert hs.hasSum using 1
  rw [derivative_formula hF hα hg k hk ha]
  have hf : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hp : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  generalize (∑' ρ : {z : ℂ // F z = 0},
    (analyticOrderNatAt F ρ.1 : ℂ) * (a - ρ.1)⁻¹ ^ (k + 1)) = S
  calc
    (-1 : ℂ) ^ k / k.factorial * ((-1 : ℂ) ^ k * k.factorial * S) =
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * S := by field_simp
    _ = S := by rw [hp]; ring

end D5.S3.Analytic.Resolvent.EntireLogDerivPowers
