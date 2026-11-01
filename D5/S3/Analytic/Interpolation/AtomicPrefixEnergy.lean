/- GID: D5/S3/Analytic/Interpolation/AtomicPrefixEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/AtomicPrefixEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Set, mathlib/module/Mathlib.MeasureTheory.Group.Integral]
   utility: none
   digest: Exact shifted hinge, exponential energy and coercivity for zero-mass complex atoms. -/

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
Finite complex atomic coefficients of total mass zero have a compactly supported
prefix. Its translated correlation is exactly the negative shifted hinge form.
No ordering, distinctness or nonemptiness of the nodes is required.

The finite interval expansion below uses the zero mass to remove a common tail.
The final estimate uses translation invariance and the elementary inequality
`2 * A * B ≤ A ^ 2 + B ^ 2`, rather than an assumption of square integrability.
The finite-window exponential identity below consumes this hinge bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

variable {I : Type*} [Fintype I]

/-- The cumulative complex mass, including atoms at the endpoint. -/
def «prefix» (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, if x i ≤ t then a i else 0

private def intervalStep (l b v : ℝ) : ℂ :=
  (Icc l b).indicator (fun _ => 1) v

private lemma intervalStep_star (l b v : ℝ) :
    star (intervalStep l b v) = intervalStep l b v := by
  by_cases h : v ∈ Icc l b <;> simp [intervalStep, h]

private lemma intervalStep_overlap (l r b : ℝ) (hl : l ≤ b) (hr : r ≤ b) :
    Integrable (fun v : ℝ => intervalStep l b v * intervalStep r b v) ∧
      (∫ v : ℝ, intervalStep l b v * intervalStep r b v) =
        ((b - max l r : ℝ) : ℂ) := by
  have he : (fun v : ℝ => intervalStep l b v * intervalStep r b v) =
      (Icc (max l r) (min b b)).indicator (fun _ => (1 : ℂ)) := by
    ext v
    rw [← Icc_inter_Icc]
    by_cases h₁ : v ∈ Icc l b <;> by_cases h₂ : v ∈ Icc r b <;>
      simp [intervalStep, h₁, h₂]
  simp only [min_self] at he
  rw [he]
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (by simp [Real.volume_Icc])), ?_⟩
  rw [integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le (max_le hl hr), Complex.real_smul, mul_one]

/-- The common upper endpoint disappears because the full mass is zero. -/
private lemma prefix_interval_expansion (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (b s : ℝ) (hb : ∀ i, x i - s ≤ b) (v : ℝ) :
    «prefix» x a (v + s) = ∑ i, intervalStep (x i - s) b v * a i := by
  classical
  by_cases hv : v ≤ b
  · unfold «prefix»
    apply Finset.sum_congr rfl
    intro i _
    have hm : v ∈ Icc (x i - s) b ↔ x i ≤ v + s := by
      simp only [mem_Icc]
      constructor
      · intro h; linarith [h.1]
      · intro h; exact ⟨by linarith, hv⟩
    by_cases hi : x i ≤ v + s <;> simp [intervalStep, Set.indicator, hm, hi]
  · have hi : ∀ i, x i ≤ v + s := by
      intro i
      have hbi := hb i
      linarith
    simp [«prefix», intervalStep, Set.indicator, mem_Icc, hv, hi, ha]

/-- Simultaneous bounds exist without choosing an element of the index type. -/
private lemma common_upper_bound (x : I → ℝ) (s : ℝ) :
    ∃ b : ℝ, (∀ i, x i - s ≤ b) ∧ (∀ i, x i ≤ b) := by
  classical
  refine ⟨∑ i, (|x i| + |s|), ?_, ?_⟩
  · intro i
    have hi : |x i| + |s| ≤ ∑ j, (|x j| + |s|) :=
      Finset.single_le_sum (f := fun j => |x j| + |s|)
        (fun j _ => add_nonneg (abs_nonneg (x j)) (abs_nonneg s))
        (Finset.mem_univ i)
    linarith [le_abs_self (x i), neg_le_abs s]
  · intro i
    have hi : |x i| + |s| ≤ ∑ j, (|x j| + |s|) :=
      Finset.single_le_sum (f := fun j => |x j| + |s|)
        (fun j _ => add_nonneg (abs_nonneg (x j)) (abs_nonneg s))
        (Finset.mem_univ i)
    linarith [le_abs_self (x i), abs_nonneg s]

private lemma correlation_integral (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (s : ℝ) :
    Integrable (fun v : ℝ => star («prefix» x a (v + s)) * «prefix» x a v) ∧
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) =
        -(∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := common_upper_bound x s
  have he (v : ℝ) : star («prefix» x a (v + s)) * «prefix» x a v =
      ∑ i, ∑ j, star (a i) *
        (intervalStep (x i - s) b v * intervalStep (x j) b v) * a j := by
    have hright : «prefix» x a v = ∑ j, intervalStep (x j) b v * a j := by
      simpa only [add_zero, sub_zero] using
        prefix_interval_expansion x a ha b 0 (by simpa only [sub_zero] using hb₂) v
    rw [prefix_interval_expansion x a ha b s hb₁ v, hright]
    simp only [star_sum, star_mul, intervalStep_star]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : I) : Integrable (fun v : ℝ => star (a i) *
      (intervalStep (x i - s) b v * intervalStep (x j) b v) * a j) :=
    ((intervalStep_overlap (x i - s) (x j) b (hb₁ i) (hb₂ j)).1.const_mul _).mul_const _
  have his : Integrable (fun v : ℝ => ∑ i, ∑ j, star (a i) *
      (intervalStep (x i - s) b v * intervalStep (x j) b v) * a j) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  refine ⟨his.congr (ae_of_all _ (fun v => (he v).symm)), ?_⟩
  have hexp : (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) =
      ∑ i, ∑ j, star (a i) * ((b - max (x i - s) (x j) : ℝ) : ℂ) * a j := by
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, integral_const_mul,
      (intervalStep_overlap (x i - s) (x j) b (hb₁ i) (hb₂ j)).2]
  have hmax (i j : I) :
      ((b - max (x i - s) (x j) : ℝ) : ℂ) =
        (b : ℂ) - (x j : ℂ) - ((max (x i - x j - s) 0 : ℝ) : ℂ) := by
    have hm : max (x i - s) (x j) = x j + max (x i - x j - s) 0 := by
      by_cases h : x j ≤ x i - s
      · rw [max_eq_left h, max_eq_left (by linarith : 0 ≤ x i - x j - s)]
        ring
      · rw [max_eq_right (le_of_not_ge h),
          max_eq_right (by linarith : x i - x j - s ≤ 0)]
        ring
    rw [hm]
    push_cast
    ring
  have hstar : ∑ i, star (a i) = 0 := by
    rw [← star_sum, ha, star_zero]
  have hcancel : (∑ i, ∑ j, star (a i) * a j * ((b : ℂ) - (x j : ℂ))) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hstar, zero_mul, Finset.sum_const_zero]
  rw [hexp]
  calc
    (∑ i, ∑ j, star (a i) * ((b - max (x i - s) (x j) : ℝ) : ℂ) * a j) =
        ∑ i, ∑ j, (star (a i) * a j * ((b : ℂ) - (x j : ℂ)) -
          star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hmax]
      ring
    _ = (∑ i, ∑ j, star (a i) * a j * ((b : ℂ) - (x j : ℂ))) -
        (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
      simp only [Finset.sum_sub_distrib]
    _ = -(∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
      rw [hcancel, zero_sub]

/-- Exact shifted hinge/prefix identity, with integrability and its uniform L² bound.
The index type may be empty, nodes may repeat, and coefficients are arbitrary complex
numbers subject only to zero total mass. All integrals use Lebesgue measure. -/
theorem shifted_hinge_prefix_energy (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (s : ℝ) :
    Integrable (fun v : ℝ => star («prefix» x a (v + s)) * «prefix» x a v) ∧
    Integrable (fun v : ℝ => ‖«prefix» x a v‖ ^ 2) ∧
    (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) =
      -(∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) ∧
    ‖∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)‖ ≤
      ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2 := by
  have hc := correlation_integral x a ha s
  have hc₀ := (correlation_integral x a ha 0).1
  have hsquare : Integrable (fun v : ℝ => ‖«prefix» x a v‖ ^ 2) := by
    have he (v : ℝ) : (star («prefix» x a (v + 0)) * «prefix» x a v).re =
        ‖«prefix» x a v‖ ^ 2 := by
      simp only [add_zero]
      change (star («prefix» x a v) * «prefix» x a v).re = _
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    exact hc₀.re.congr (ae_of_all _ he)
  have hshift : Integrable (fun v : ℝ => ‖«prefix» x a (v + s)‖ ^ 2) :=
    hsquare.comp_add_right s
  have hmajor : Integrable (fun v : ℝ =>
      (‖«prefix» x a (v + s)‖ ^ 2 + ‖«prefix» x a v‖ ^ 2) / 2) :=
    (hshift.add hsquare).div_const 2
  have hyoung (v : ℝ) : ‖star («prefix» x a (v + s)) * «prefix» x a v‖ ≤
      (‖«prefix» x a (v + s)‖ ^ 2 + ‖«prefix» x a v‖ ^ 2) / 2 := by
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖«prefix» x a (v + s)‖ - ‖«prefix» x a v‖)]
  have hmajor_integral : (∫ v : ℝ,
      (‖«prefix» x a (v + s)‖ ^ 2 + ‖«prefix» x a v‖ ^ 2) / 2) =
        ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2 := by
    rw [integral_div, integral_add hshift hsquare,
      integral_add_right_eq_self (fun v : ℝ => ‖«prefix» x a v‖ ^ 2) s]
    ring
  refine ⟨hc.1, hsquare, ?_, ?_⟩
  · rw [hc.2, neg_neg]
  · calc
      ‖∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)‖ =
          ‖∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v‖ := by
        rw [hc.2, norm_neg]
      _ ≤ ∫ v : ℝ, ‖star («prefix» x a (v + s)) * «prefix» x a v‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (‖«prefix» x a (v + s)‖ ^ 2 + ‖«prefix» x a v‖ ^ 2) / 2 :=
        integral_mono hc.1.norm hmajor hyoung
      _ = ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2 := hmajor_integral

/-- Ordinary FTC for the exponential affine primitive. Both signs of `k` are
used below; the primitive has no cusp. -/
private lemma integral_affine_exp (k : ℝ) (hk : k ≠ 0) (t a b : ℝ) :
    (∫ s in a..b, (t - s) * Real.exp (k * s)) =
      Real.exp (k * b) * (k * (t - b) + 1) / k ^ 2 -
        Real.exp (k * a) * (k * (t - a) + 1) / k ^ 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.exp (k * s) * (k * (t - s) + 1) / k ^ 2)
  · intro s _
    have hd := (((hasDerivAt_id s).const_mul k).exp.mul
      ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul k).add_const 1)).div_const
        (k ^ 2)
    convert hd using 1 <;> dsimp <;> field_simp [hk] <;> ring
  · exact (by fun_prop : Continuous (fun s : ℝ =>
      (t - s) * Real.exp (k * s))).intervalIntegrable a b

/-- Exact finite-window exponential hinge representation. Its scalar integrand
is continuous, hence integrable even for a zero-length window. -/
theorem finite_window_exponential_hinge (lam D t : ℝ) (hlam : 0 < lam)
    (hD : 0 ≤ D) (ht : |t| ≤ D) :
    IntegrableOn (fun s : ℝ => max (t - s) 0 * Real.exp (-lam * |s|)) (Icc (-D) D) ∧
    Real.exp (-lam * |t|) = Real.exp (-lam * D) +
      lam * Real.exp (-lam * D) * (t + D) +
      lam ^ 2 * (∫ s in Icc (-D) D, max (t - s) 0 * Real.exp (-lam * |s|)) -
      2 * lam * max t 0 := by
  let f : ℝ → ℝ := fun s => max (t - s) 0 * Real.exp (-lam * |s|)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hbounds : -D ≤ t ∧ t ≤ D := abs_le.mp ht
  have hwindow : (∫ s in Icc (-D) D, f s) = ∫ s in (-D)..D, f s := by
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith : -D ≤ D)]
  have htail : (∫ s in t..D, f s) = 0 := by
    calc
      (∫ s in t..D, f s) = ∫ s in t..D, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hbounds.2] at hs
        dsimp [f]
        rw [max_eq_right (by linarith [hs.1] : t - s ≤ 0), zero_mul]
      _ = 0 := by simp
  have htrunc : (∫ s in (-D)..D, f s) = ∫ s in (-D)..t, f s := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-D) t) (hf.intervalIntegrable t D)
    rw [htail, add_zero] at h
    exact h.symm
  refine ⟨hf.integrableOn_Icc (μ := volume), ?_⟩
  change Real.exp (-lam * |t|) = Real.exp (-lam * D) +
    lam * Real.exp (-lam * D) * (t + D) +
    lam ^ 2 * (∫ s in Icc (-D) D, f s) - 2 * lam * max t 0
  rw [hwindow, htrunc]
  rcases le_total t 0 with ht0 | ht0
  · have hleft : (∫ s in (-D)..t, f s) =
        ∫ s in (-D)..t, (t - s) * Real.exp (lam * s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hbounds.1] at hs
      dsimp [f]
      rw [max_eq_left (by linarith [hs.2] : 0 ≤ t - s),
        abs_of_nonpos (hs.2.trans ht0)]
      congr 2 <;> ring
    rw [hleft, integral_affine_exp lam hlam.ne' t (-D) t,
      abs_of_nonpos ht0, max_eq_right ht0,
      show -lam * -t = lam * t by ring,
      show lam * -D = -lam * D by ring]
    simp only [sub_self, mul_zero, add_zero, mul_one, zero_mul, sub_zero,
      sub_neg_eq_add]
    field_simp [hlam.ne'] <;> ring
  · have hleft : (∫ s in (-D)..0, f s) =
        ∫ s in (-D)..0, (t - s) * Real.exp (lam * s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by linarith : -D ≤ (0 : ℝ))] at hs
      dsimp [f]
      rw [max_eq_left (by linarith [hs.2] : 0 ≤ t - s), abs_of_nonpos hs.2]
      congr 2 <;> ring
    have hright : (∫ s in (0 : ℝ)..t, f s) =
        ∫ s in (0 : ℝ)..t, (t - s) * Real.exp (-lam * s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht0] at hs
      dsimp [f]
      rw [max_eq_left (by linarith [hs.2] : 0 ≤ t - s), abs_of_nonneg hs.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-D) 0) (hf.intervalIntegrable 0 t), hleft, hright,
      integral_affine_exp lam hlam.ne' t (-D) 0,
      integral_affine_exp (-lam) (neg_ne_zero.mpr hlam.ne') t 0 t,
      abs_of_nonneg ht0, max_eq_left ht0,
      show lam * -D = -lam * D by ring]
    simp only [mul_zero, Real.exp_zero, one_mul, sub_zero, sub_self, zero_sub,
      add_zero, mul_one, sub_neg_eq_add]
    field_simp [hlam.ne'] <;> ring

/-- Every affine atom-difference form vanishes at zero total mass. -/
private lemma zero_mass_affine (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (p q r : ℂ) :
    (∑ i, ∑ j, star (a i) * a j * (p + q * ((x i : ℂ) - (x j : ℂ) + r))) = 0 := by
  classical
  have hstar : ∑ i, star (a i) = 0 := by rw [← star_sum, ha, star_zero]
  have hrow (i : I) :
      (∑ j, star (a i) * a j * (p + q * ((x i : ℂ) - (x j : ℂ) + r))) =
        star (a i) * (-(∑ j, a j * (q * (x j : ℂ)))) := by
    calc
      _ = ∑ j, ((star (a i) * (p + q * ((x i : ℂ) + r))) * a j -
          star (a i) * (a j * (q * (x j : ℂ)))) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (star (a i) * (p + q * ((x i : ℂ) + r))) * (∑ j, a j) -
          star (a i) * (∑ j, a j * (q * (x j : ℂ))) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [ha]; ring
  simp_rw [hrow]
  rw [← Finset.sum_mul, hstar, zero_mul]

/-- The exact exponential energy of arbitrary finite complex zero-mass atoms.
All correlations and the norm square are integrable. The correlation is continuous
as a function of the shift, and its exponentially weighted finite-window integral
is integrable. No ordering, distinctness or nonemptiness assumption is used. -/
theorem exponential_prefix_energy (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hx : ∀ i j, |x i - x j| ≤ D) :
    let F := «prefix» x a
    let E : ℝ := ∫ v : ℝ, ‖F v‖ ^ 2
    let C : ℝ → ℂ := fun s => ∫ v : ℝ, star (F (v + s)) * F v
    Integrable (fun v : ℝ => ‖F v‖ ^ 2) ∧
    (∀ s : ℝ, Integrable (fun v : ℝ => star (F (v + s)) * F v)) ∧
    Continuous C ∧
    IntegrableOn (fun s => (Real.exp (-lam * |s|) : ℂ) * C s) (Icc (-D) D) ∧
    (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
      (2 * lam : ℂ) * (E : ℂ) -
        (lam ^ 2 : ℂ) * (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s) := by
  classical
  let C : ℝ → ℂ := fun s => ∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v
  let E : ℝ := ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2
  let H : ℝ → ℂ := fun s =>
    ∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)
  have hHC (s : ℝ) : H s = -C s :=
    (shifted_hinge_prefix_energy x a ha s).2.2.1
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hCeq : C = fun s => -H s := by
    funext s
    rw [hHC, neg_neg]
  have hC : Continuous C := by rw [hCeq]; exact hH.neg
  have hw : Continuous (fun s : ℝ => (Real.exp (-lam * |s|) : ℂ)) := by fun_prop
  refine ⟨(shifted_hinge_prefix_energy x a ha 0).2.1,
    fun s => (shifted_hinge_prefix_energy x a ha s).1,
    hC, (hw.mul hC).integrableOn_Icc, ?_⟩
  change (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
    (2 * lam : ℂ) * (E : ℂ) -
      (lam ^ 2 : ℂ) * (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s)
  have hC0 : C 0 = (E : ℂ) := by
    dsimp [C, E]
    calc
      (∫ v : ℝ, star («prefix» x a (v + 0)) * «prefix» x a v) =
          ∫ v : ℝ, ((‖«prefix» x a v‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun v => by
          simp only [add_zero]
          change star («prefix» x a v) * «prefix» x a v = _
          rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq])
      _ = _ := integral_complex_ofReal
  have hH0 : (∑ i, ∑ j, star (a i) * a j *
      ((max (x i - x j) 0 : ℝ) : ℂ)) = -(E : ℂ) := by
    simpa only [H, sub_zero, hC0] using hHC 0
  let J : I → I → ℂ := fun i j =>
    ∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) *
      ((max (x i - x j - s) 0 : ℝ) : ℂ)
  have hi (i j : I) : IntegrableOn (fun s : ℝ => star (a i) * a j *
      ((Real.exp (-lam * |s|) : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)))
      (Icc (-D) D) :=
    (by fun_prop : Continuous (fun s : ℝ => star (a i) * a j *
      ((Real.exp (-lam * |s|) : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)))).integrableOn_Icc
  have hswap : (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * H s) =
      ∑ i, ∑ j, star (a i) * a j * J i j := by
    calc
      _ = ∫ s in Icc (-D) D, ∑ i, ∑ j, star (a i) * a j *
          ((Real.exp (-lam * |s|) : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun s => by
          dsimp [H]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring)
      _ = ∑ i, ∑ j, ∫ s in Icc (-D) D, star (a i) * a j *
          ((Real.exp (-lam * |s|) : ℂ) * ((max (x i - x j - s) 0 : ℝ) : ℂ)) := by
        rw [integral_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => hi i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun j _ => hi i j)]
      _ = _ := by simp only [J, integral_const_mul]
  have hsumJ : (∑ i, ∑ j, star (a i) * a j * J i j) =
      -(∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s) := by
    rw [← hswap]
    calc
      _ = ∫ s in Icc (-D) D, -((Real.exp (-lam * |s|) : ℂ) * C s) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun s => by dsimp only; rw [hHC]; ring)
      _ = _ := integral_neg _
  have hcastWindow (t : ℝ) :
      ((∫ s in Icc (-D) D, max (t - s) 0 * Real.exp (-lam * |s|) : ℝ) : ℂ) =
        ∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * ((max (t - s) 0 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact ae_of_all _ (fun s => by dsimp only; rw [Complex.ofReal_mul]; ring)
  have hpoint (i j : I) :
      (Real.exp (-lam * |x i - x j|) : ℂ) =
        (Real.exp (-lam * D) : ℂ) + (lam * Real.exp (-lam * D) : ℂ) *
          ((x i : ℂ) - (x j : ℂ) + (D : ℂ)) +
        (lam ^ 2 : ℂ) * J i j -
        (2 * lam : ℂ) * ((max (x i - x j) 0 : ℝ) : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ))
      (finite_window_exponential_hinge lam D (x i - x j) hlam hD (hx i j)).2
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat] at h
    rw [hcastWindow] at h
    simpa only [J, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat] using h
  have hcancel : (∑ i, ∑ j, star (a i) * a j *
      ((Real.exp (-lam * D) : ℂ) + (lam * Real.exp (-lam * D) : ℂ) *
        ((x i : ℂ) - (x j : ℂ) + (D : ℂ)))) = 0 :=
    zero_mass_affine x a ha _ _ _
  calc
    _ = ∑ i, ∑ j,
        (star (a i) * a j * ((Real.exp (-lam * D) : ℂ) +
          (lam * Real.exp (-lam * D) : ℂ) * ((x i : ℂ) - (x j : ℂ) + (D : ℂ))) +
        (lam ^ 2 : ℂ) * (star (a i) * a j * J i j) -
        (2 * lam : ℂ) * (star (a i) * a j * ((max (x i - x j) 0 : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hpoint]
      ring
    _ = (∑ i, ∑ j, star (a i) * a j * ((Real.exp (-lam * D) : ℂ) +
          (lam * Real.exp (-lam * D) : ℂ) * ((x i : ℂ) - (x j : ℂ) + (D : ℂ)))) +
        (lam ^ 2 : ℂ) * (∑ i, ∑ j, star (a i) * a j * J i j) -
        (2 * lam : ℂ) * (∑ i, ∑ j, star (a i) * a j *
          ((max (x i - x j) 0 : ℝ) : ℂ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hcancel, hsumJ, hH0]; ring

/-- The exact mass of the exponential weight on the symmetric finite window.
This is used below before multiplying by the nonnegative prefix energy. -/
private lemma integral_exp_abs_window (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D) :
    (∫ s in Icc (-D) D, Real.exp (-lam * |s|)) =
      2 * (1 - Real.exp (-lam * D)) / lam := by
  have hprimitive (k : ℝ) (hk : k ≠ 0) (a b : ℝ) :
      (∫ s in a..b, Real.exp (k * s)) =
        Real.exp (k * b) / k - Real.exp (k * a) / k := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Real.exp (k * s) / k)
    · intro s _
      simpa only [id_eq, mul_one, mul_div_cancel_right₀ (Real.exp (k * s)) hk] using
        (((hasDerivAt_id s).const_mul k).exp.div_const k)
    · exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (k * s))).intervalIntegrable a b
  have hf : Continuous (fun s : ℝ => Real.exp (-lam * |s|)) := by fun_prop
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -D ≤ D),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-D) 0) (hf.intervalIntegrable 0 D)]
  have hleft : (∫ s in (-D)..0, Real.exp (-lam * |s|)) =
      ∫ s in (-D)..0, Real.exp (lam * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith : -D ≤ (0 : ℝ))] at hs
    dsimp only
    rw [abs_of_nonpos hs.2]
    congr 1
    ring
  have hright : (∫ s in (0 : ℝ)..D, Real.exp (-lam * |s|)) =
      ∫ s in (0 : ℝ)..D, Real.exp (-lam * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hD] at hs
    dsimp only
    rw [abs_of_nonneg hs.1]
  rw [hleft, hright, hprimitive lam hlam.ne' (-D) 0,
    hprimitive (-lam) (neg_ne_zero.mpr hlam.ne') 0 D]
  simp only [mul_zero, Real.exp_zero, show lam * -D = -lam * D by ring]
  field_simp [hlam.ne'] <;> ring

/-- Quantitative exponential coercivity on the zero-mass subspace. The exact
constant retains the whole finite-window exponential mass. Empty families,
repeated nodes and a zero-length window require no separate nondegeneracy premise. -/
theorem exponential_prefix_coercivity (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hx : ∀ i j, |x i - x j| ≤ D) :
    2 * lam * Real.exp (-lam * D) * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
      (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re := by
  classical
  let E : ℝ := ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2
  let C : ℝ → ℂ := fun s => ∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v
  have hfull := exponential_prefix_energy x a ha lam D hlam hD hx
  have hweight : IntegrableOn (fun s => (Real.exp (-lam * |s|) : ℂ) * C s)
      (Icc (-D) D) := hfull.2.2.2.1
  have hC (s : ℝ) : (C s).re ≤ E := by
    have h := shifted_hinge_prefix_energy x a ha s
    have hn : ‖C s‖ ≤ E := by
      have hh := h.2.2.2
      rw [h.2.2.1, norm_neg] at hh
      exact hh
    exact (Complex.re_le_norm _).trans hn
  have hmajor : IntegrableOn (fun s : ℝ => Real.exp (-lam * |s|) * E)
      (Icc (-D) D) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-lam * |s|) * E)).integrableOn_Icc
  have hreal : IntegrableOn (fun s : ℝ => Real.exp (-lam * |s|) * (C s).re)
      (Icc (-D) D) := by
    simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hweight.re
  have hbound : (∫ s in Icc (-D) D, Real.exp (-lam * |s|) * (C s).re) ≤
      (2 * (1 - Real.exp (-lam * D)) / lam) * E := by
    calc
      _ ≤ ∫ s in Icc (-D) D, Real.exp (-lam * |s|) * E :=
        integral_mono hreal hmajor (fun s =>
          mul_le_mul_of_nonneg_left (hC s) (Real.exp_nonneg _))
      _ = _ := by rw [integral_mul_const, integral_exp_abs_window lam D hlam hD]
  have hrealIntegral :
      (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s).re =
        ∫ s in Icc (-D) D, Real.exp (-lam * |s|) * (C s).re := by
    change RCLike.re (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s) = _
    rw [← integral_re hweight, RCLike.re_eq_complex_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hid :
      (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re =
        2 * lam * E - lam ^ 2 *
          (∫ s in Icc (-D) D, Real.exp (-lam * |s|) * (C s).re) := by
    have hc :
        (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
          ((2 * lam * E : ℝ) : ℂ) - ((lam ^ 2 : ℝ) : ℂ) *
            (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s) := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
        using hfull.2.2.2.2
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hrealIntegral]
      using congrArg Complex.re hc
  change 2 * lam * Real.exp (-lam * D) * E ≤ _
  rw [hid]
  calc
    _ = 2 * lam * E - lam ^ 2 *
        ((2 * (1 - Real.exp (-lam * D)) / lam) * E) := by
      field_simp [hlam.ne'] <;> ring
    _ ≤ _ := sub_le_sub_left
      (mul_le_mul_of_nonneg_left hbound (sq_nonneg lam)) _

#print axioms shifted_hinge_prefix_energy
#print axioms finite_window_exponential_hinge
#print axioms exponential_prefix_energy
#print axioms exponential_prefix_coercivity

end D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
