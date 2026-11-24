/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed square-root lower bound for the ordinary-prime triangle on arbitrarily late power windows characterizes RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
import D5.S3.Analytic.Laplace.CriticalGammaWindow
import Mathlib.Analysis.Complex.RemovableSingularity
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! The dyadic triangular filter preserves the simple pole contribution of every
zeta zero in the open critical strip, even after subtraction of a continuous
boundary term. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow

open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit (U_exp_continuous)
open D5.S3.Analytic.Laplace.EulerPoleObstruction (finiteHead finiteHead_entire kernel)

namespace GeneralLaplaceMoments

private def kernel (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (g u : ℂ))

private theorem kernel_continuous {g : ℝ → ℝ} (hg : Continuous g) (k : ℕ) (s : ℂ) :
    Continuous (kernel g k s) := by
  unfold kernel
  have h := Complex.continuous_ofReal.comp hg
  exact (Complex.continuous_ofReal.neg.pow k).mul
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul h)

private theorem kernel_norm (g : ℝ → ℝ) (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel g k s u‖ = u ^ k * (Real.exp (-s.re * u) * |g u|) := by
  simp [kernel, norm_pow, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]

private theorem kernel_bound (g : ℝ → ℝ) (k : ℕ) {a d : ℝ} (hd : 0 < d) {s : ℂ} (hs : a + d ≤ s.re)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel g k s u‖ ≤ (k.factorial : ℝ) / d ^ k * ‖kernel g 0 a u‖ := by
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  have hf : 0 < (k.factorial : ℝ) := by positivity
  have hdk : 0 < d ^ k := pow_pos hd _
  rw [mul_pow, div_le_iff₀ hf] at hp
  have huPow : u ^ k ≤ (k.factorial : ℝ) / d ^ k * Real.exp (d * u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
    simpa [mul_comm] using hp
  rw [kernel_norm g k s hu, kernel_norm g 0 a hu]
  simp only [Complex.ofReal_re, pow_zero, one_mul]
  calc
    _ ≤ ((k.factorial : ℝ) / d ^ k * Real.exp (d * u)) *
        (Real.exp (-s.re * u) * |g u|) :=
      mul_le_mul_of_nonneg_right huPow (by positivity)
    _ = ((k.factorial : ℝ) / d ^ k * Real.exp ((d - s.re) * u)) * |g u| := by
      rw [show (d - s.re) * u = d * u + (-s.re) * u by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      gcongr
      linarith

variable {g : ℝ → ℝ} {σ₀ : ℝ}

private theorem kernel_integrable (hg : Continuous g)
    (hbase : ∀ a : ℝ, σ₀ < a → IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0))
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (kernel g k s) (Ioi 0) := by
  let d := (s.re - σ₀) / 3
  let a := σ₀ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : σ₀ < a := by dsimp [a]; linarith
  have h : IntegrableOn (fun u => (k.factorial : ℝ) / d ^ k * ‖kernel g 0 a u‖) (Ioi 0) :=
    (hbase a ha).norm.const_mul _
  refine h.mono' (kernel_continuous hg k s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  exact kernel_bound g k hd (by dsimp [a,d]; linarith) (le_of_lt hu)

private theorem kernel_derivative (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) :
    HasDerivAt (fun z => kernel g k z u) (kernel g (k+1) s u) s := by
  unfold kernel
  have h := (((hasDerivAt_id s).neg.mul_const (u : ℂ)).cexp.mul_const (g u : ℂ)).const_mul
    ((-(u : ℂ)) ^ k)
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq, neg_one_mul, pow_succ]
  ring

private theorem integral_derivative (hg : Continuous g)
    (hbase : ∀ a : ℝ, σ₀ < a → IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0))
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    HasDerivAt (fun z => ∫ u : ℝ in Ioi 0, kernel g k z u)
      (∫ u : ℝ in Ioi 0, kernel g (k+1) s u) s := by
  let d := (s.re - σ₀) / 3
  let a := σ₀ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : σ₀ < a := by dsimp [a]; linarith
  have hn : {z : ℂ | a + d < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [a,d]; linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) hn
    (Eventually.of_forall fun z => (kernel_continuous hg k z).aestronglyMeasurable)
    (kernel_integrable hg hbase k hs) (kernel_continuous hg (k+1) s).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu z hz
      exact kernel_bound g (k+1) hd (le_of_lt hz) (le_of_lt hu))
    ((hbase a ha).norm.const_mul ((k+1).factorial / d ^ (k+1) : ℝ))
    (Eventually.of_forall fun u z _ => kernel_derivative g k z u)).2

/-- Absolute Laplace convergence on an initial half-plane implies all logarithmic
moments and identifies them with the iterated derivatives of the transform. -/
private theorem iterated_derivative_moment {F : ℂ → ℂ} (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (fun u : ℝ => (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (g u : ℂ))) (Ioi 0) ∧
    iteratedDeriv k F s = ∫ u : ℝ in Ioi 0, (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (g u : ℂ)) := by
  have hbase (a : ℝ) (ha : σ₀ < a) : IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0) := by
    unfold kernel
    simp only [pow_zero, one_mul]
    exact (hF (a : ℂ) (by simpa only [Complex.ofReal_re] using ha)).1
  refine ⟨kernel_integrable hg hbase k hs, ?_⟩
  change iteratedDeriv k F s = ∫ u : ℝ in Ioi 0, kernel g k s u
  induction k generalizing s with
  | zero =>
    simpa only [iteratedDeriv_zero, kernel, pow_zero, one_mul] using (hF s hs).2.symm
  | succ k ih =>
    have hopen : {z : ℂ | σ₀ < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have heq : iteratedDeriv k F =ᶠ[𝓝 s]
        (fun z => ∫ u : ℝ in Ioi 0, kernel g k z u) := by
      filter_upwards [hopen] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq, (integral_derivative hg hbase k hs).deriv]

private def weight (k : ℕ) (σ u : ℝ) : ℝ :=
  u ^ k * Real.exp (-σ * u) / k.factorial

private def normalizedDerivative (F : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s

private def complexMoment (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  ((u : ℂ) ^ k / k.factorial) * (Complex.exp (-s * u) * (g u : ℂ))

variable {F : ℂ → ℂ}

private lemma normalizedDerivative_integral (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (complexMoment g k s) (Ioi 0) ∧
      normalizedDerivative F k s = ∫ u in Ioi 0, complexMoment g k s u := by
  have hm := iterated_derivative_moment hg hF k hs
  have hkernel :
      (fun u : ℝ => ((-1 : ℂ) ^ k / k.factorial) *
        ((-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (g u : ℂ)))) = complexMoment g k s := by
    funext u
    have hpow : (-1 : ℂ) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    unfold complexMoment
    calc
      _ = (((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) / k.factorial) *
          (Complex.exp (-s * u) * (g u : ℂ)) := by ring
      _ = _ := by rw [hpow]
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, hkernel] using hm.1.const_mul ((-1 : ℂ) ^ k / k.factorial)
  · rw [normalizedDerivative, hm.2, ← integral_const_mul, hkernel]

private lemma norm_complexMoment (g : ℝ → ℝ) (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖complexMoment g k s u‖ = |g u| * weight k s.re u := by
  simp [complexMoment, weight, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]
  ring

private lemma complexMoment_real (g : ℝ → ℝ) (k : ℕ) (σ u : ℝ) :
    complexMoment g k (σ : ℂ) u = ((g u * weight k σ u : ℝ) : ℂ) := by
  simp [complexMoment, weight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div]
  ring

private lemma weight_nonneg (k : ℕ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ weight k σ u := by unfold weight; positivity

private lemma weight_bound (k : ℕ) {σ α : ℝ} (hα : α < σ) {u : ℝ} (hu : 0 ≤ u) :
    weight k σ u ≤ (σ - α)⁻¹ ^ k * Real.exp (-α * u) := by
  let d := σ - α
  have hd : 0 < d := sub_pos.mpr hα
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  rw [mul_pow] at hp
  unfold weight
  calc
    _ = (d ^ k * u ^ k / k.factorial) * (d⁻¹ ^ k * Real.exp (-σ * u)) := by
      rw [div_mul_eq_mul_div, mul_assoc (d ^ k), mul_left_comm (u ^ k),
        ← mul_assoc (d ^ k), ← mul_pow, mul_inv_cancel₀ hd.ne', one_pow, one_mul]
    _ ≤ Real.exp (d * u) * (d⁻¹ ^ k * Real.exp (-σ * u)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add, show d * u + -σ * u = -α * u by dsimp [d]; ring]

/-- A paired moment bounds the prescribed sign of the remainder inside a log
window, with the absolute moment as the allowance outside the window. -/
private theorem signed_window_moment_bound (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {p : ℂ} (hp : σ₀ < p.re)
    {a b α e : ℝ} (ha : 0 < a) (hab : a ≤ b) (hα : α < p.re)
    (he : e = 1 ∨ e = -1) :
    let D := fun s : ℂ =>
      ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s
    ‖D p‖ + e * (D (p.re : ℂ)).re ≤
      2 * (p.re - α)⁻¹ ^ k * (∫ u in a..b, max (e * g u) 0 * Real.exp (-α * u)) +
      2 * ∫ u in Ioi (0 : ℝ) \ Icc a b,
        |g u| * (u ^ k * Real.exp (-p.re * u) / k.factorial) := by
  let σ := p.re
  let A := Ioi (0 : ℝ)
  let W := Icc a b
  let K := weight k σ
  let f := fun u => max (e * g u) 0 * K u
  let absoluteMoment := fun u => |g u| * K u
  let G := fun u => max (e * g u) 0 * Real.exp (-α * u)
  have hWA : W ⊆ A := fun _ hu => ha.trans_le hu.1
  have hpMoment := normalizedDerivative_integral hg hF k hp
  have hrealMoment := normalizedDerivative_integral hg hF k (s := (σ : ℂ))
    (by simpa only [Complex.ofReal_re, σ] using hp)
  have hF : IntegrableOn absoluteMoment A := by
    apply (integrable_congr _).mp hpMoment.1.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment g k p hu.le
  have hSigned : IntegrableOn (fun u => g u * K u) A := by
    have h := hrealMoment.1.re
    change IntegrableOn (fun u => (complexMoment g k (σ : ℂ) u).re) A at h
    simpa only [complexMoment_real, Complex.ofReal_re, K] using h
  have hePoint (u : ℝ) : |g u| * K u + e * (g u * K u) = 2 * f u := by
    have h : |g u| + e * g u = 2 * max (e * g u) 0 := by
      rcases he with rfl | rfl
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_left h]; ring
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_right hn]
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_right (neg_nonpos.mpr h)]
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]; ring
    dsimp only [f]
    calc
      _ = (|g u| + e * g u) * K u := by ring
      _ = _ := by rw [h]; ring
  have hf : IntegrableOn f A := by
    have hf' := (hF.add (hSigned.const_mul e)).const_mul (1 / 2 : ℝ)
    refine hf'.congr (ae_of_all _ fun u => ?_)
    symm
    change f u = (1 / 2) * (|g u| * K u + e * (g u * K u))
    rw [hePoint]
    ring
  have hnorm : ‖normalizedDerivative F k p‖ ≤ ∫ u in A, absoluteMoment u := by
    rw [hpMoment.2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment g k p hu.le
  have hre : (normalizedDerivative F k (σ : ℂ)).re = ∫ u in A, g u * K u := by
    rw [hrealMoment.2]
    simp only [complexMoment_real, integral_complex_ofReal, Complex.ofReal_re, A, K]
  have hpair : ‖normalizedDerivative F k p‖ + e * (normalizedDerivative F k (σ : ℂ)).re ≤
      2 * ∫ u in A, f u := by
    rw [hre, ← integral_const_mul e]
    refine (add_le_add_left hnorm _).trans_eq ?_
    rw [← integral_add hF (hSigned.const_mul e), ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hePoint)
  have hsplit : (∫ u in A, f u) = (∫ u in W, f u) + ∫ u in A \ W, f u := by
    rw [setIntegral_sdiff measurableSet_Icc hf hWA]
    ring
  have hG : IntegrableOn G W := by
    have hcont : Continuous G :=
      ((hg.const_mul e).max continuous_const).mul (by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hwindow : (∫ u in W, f u) ≤ (σ - α)⁻¹ ^ k * ∫ u in a..b, G u := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_mono_on (hf.mono_set hWA) (hG.const_mul _) measurableSet_Icc ?_
    intro u hu
    have hu0 : 0 ≤ u := (show 0 < u from hWA hu).le
    change max (e * g u) 0 * K u ≤ (σ - α)⁻¹ ^ k * (max (e * g u) 0 * Real.exp (-α * u))
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (weight_bound k hα hu0) (le_max_right _ _)
  have htail : (∫ u in A \ W, f u) ≤ ∫ u in A \ W, absoluteMoment u := by
    refine setIntegral_mono_on (hf.mono_set sdiff_subset) (hF.mono_set sdiff_subset)
      (measurableSet_Ioi.diff measurableSet_Icc) ?_
    intro u hu
    have hmajor : max (e * g u) 0 ≤ |g u| := by
      apply max_le _ (abs_nonneg _)
      rcases he with rfl | rfl
      · simpa using le_abs_self (g u)
      · simpa using neg_le_abs (g u)
    exact mul_le_mul_of_nonneg_right hmajor (weight_nonneg k σ hu.1.le)
  change ‖normalizedDerivative F k p‖ + e * (normalizedDerivative F k (σ : ℂ)).re ≤
    2 * (σ - α)⁻¹ ^ k * (∫ u in a..b, G u) + 2 * ∫ u in A \ W, absoluteMoment u
  rw [hsplit, mul_add] at hpair
  exact hpair.trans (by linarith only [hwindow, htail])


#print axioms iterated_derivative_moment
#print axioms signed_window_moment_bound

end GeneralLaplaceMoments

namespace PairedLaplacePoleWindow

private def coeff (F : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s

private lemma normalize_coefficients (q c : ℂ) (a : ℕ → ℂ) {r B : ℝ}
    (hq : q ≠ 0) (hc : c ≠ 0) (hr : 0 < r)
    (h : ∀ n : ℕ, ‖a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))‖ ≤
      (n.factorial : ℝ) * B / r^n) :
    let J := fun n : ℕ => q^(n+1) * ((-1 : ℂ)^n / n.factorial) * a n
    (∀ n : ℕ, ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n) ∧
    (‖q‖ < r → Tendsto J atTop (𝓝 c) ∧ ∀ᶠ n in atTop, ‖c‖ / 2 ≤ ‖J n‖) := by
  intro J
  have bound (n : ℕ) : ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n := by
    let K := q^(n+1) * ((-1 : ℂ)^n / n.factorial)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : q^(-1-(n : ℤ)) = (q^(n+1))⁻¹ := by
      rw [show (-1-(n : ℤ)) = -((n+1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hsign : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; simp
    have cancel : K * (c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) = c := by
      rw [hpow]
      dsimp only [K]
      field_simp [hn, hq]
      simpa only [pow_two] using hsign
    have herr : J n - c = K * (a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) := by
      rw [mul_sub, cancel]
    rw [herr, norm_mul]
    apply (mul_le_mul_of_nonneg_left (h n) (norm_nonneg K)).trans_eq
    dsimp only [K]
    simp only [norm_mul, norm_pow, norm_div, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      div_pow, pow_succ]
    field_simp [hr.ne', Nat.factorial_ne_zero]
  refine ⟨bound, fun hqr => ?_⟩
  have hdecay := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (norm_nonneg q) hr.le) ((div_lt_one hr).mpr hqr)).const_mul (B * ‖q‖)
  have hlim : Tendsto J atTop (𝓝 c) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) bound (by simpa using hdecay)
  exact ⟨hlim, (hlim.norm.eventually (eventually_gt_nhds (half_lt_self (norm_pos_iff.mpr hc)))).mono
    fun n hn => hn.le⟩

private lemma complex_disk_dominance {F H : ℂ → ℂ} {p z c : ℂ} {r : ℝ}
    (hpz : p ≠ z) (hc0 : c ≠ 0) (hr : 0 < r) (hdr : ‖p - z‖ < r)
    (haF : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s) :
    ∀ᶠ k : ℕ in atTop, ‖c‖ / 2 ≤ ‖(p - z)^(k+1) * coeff F k p‖ := by
  let P := fun s : ℂ => c / (s - z)
  let G := Function.update (fun s => F s - P s) z (H z)
  have hoff (s : ℂ) (hs : s ≠ z) : G s = F s - P s := Function.update_of_ne hs _ _
  have hgerm : G =ᶠ[𝓝 z] H := by
    have h := eventually_nhdsWithin_iff.mp hprincipal
    filter_upwards [h] with s he
    by_cases hs : s = z
    · subst s
      exact Function.update_self ..
    · rw [hoff s hs, he hs]
      ring
  have haP {s : ℂ} (hs : s ≠ z) : AnalyticAt ℂ P s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
  have hmodel (s : ℂ) (hs : s ≠ z) : G =ᶠ[𝓝 s] fun w => F w - P w :=
    (continuousAt_id.eventually_ne hs).mono fun w hw => hoff w hw
  have ha : AnalyticOnNhd ℂ G (Metric.closedBall p r) := by
    intro s hs
    by_cases hsz : s = z
    · subst s
      exact hH.congr hgerm.symm
    · exact ((haF s hs hsz).sub (haP hsz)).congr (hmodel s hsz).symm
  obtain ⟨B, hB⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn ha.continuousOn
  have hraw (n : ℕ) :
      ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial * (p - z)^(-1-(n : ℤ)))‖ ≤
        (n.factorial : ℝ) * max B 0 / r^n := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (ha.differentiableOn.diffContOnCl_ball (Subset.rfl)) (fun w hw =>
        (hB w (Metric.sphere_subset_closedBall hw)).trans (le_max_left B 0))
    rw [(hmodel p hpz).iteratedDeriv_eq n, iteratedDeriv_fun_sub
      (haF p (Metric.mem_closedBall_self hr.le) hpz).contDiffAt (haP hpz).contDiffAt] at hc
    have hP : iteratedDeriv n P p = c * ((-1 : ℂ)^n * n.factorial * (p - z)^(-1-(n : ℤ))) := by
      dsimp only [P]
      simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field]
      rw [iteratedDeriv_comp_sub_const (f := Inv.inv), iteratedDeriv_eq_iterate]
      exact congrArg (c * ·) (iter_deriv_inv n (p - z))
    rwa [hP] at hc
  simpa only [coeff, mul_assoc] using ((normalize_coefficients (p - z) c
    (fun n => iteratedDeriv n F p) (sub_ne_zero.mpr hpz) hc0 hr hraw).2 hdr).2


private lemma paired_disk_lower {F H : ℂ → ℂ} {p z c : ℂ} {r : ℝ}
    (hc : c ≠ 0) (hd : 0 < ‖p - z‖) (hdr : ‖p - z‖ < r)
    (hcomplex : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hreal : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r))
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ k : ℕ in atTop,
      L ≤ ‖p - z‖^k * (‖coeff F k p‖ - |(coeff F k (p.re : ℂ)).re|) := by
  have hr := hd.trans hdr
  have hpz := sub_ne_zero.mp (norm_pos_iff.mp hd)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hconv := complex_disk_dominance hpz hc hr hdr hcomplex hH hprincipal
  obtain ⟨B, hB⟩ := (isCompact_closedBall (p.re : ℂ) r).exists_bound_of_continuousOn
    hreal.continuousOn
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hr.le)
    ((div_lt_one hr).mpr hdr)).const_mul B
  have herr : ∀ᶠ k : ℕ in atTop, B * (‖p - z‖/r)^k < ‖c‖ / (4*‖p - z‖) := by
    apply (tendsto_order.mp (by simpa using hsmall :
      Tendsto (fun k : ℕ => B * (‖p - z‖/r)^k) atTop (𝓝 0))).2
    positivity
  refine ⟨‖c‖ / (4*‖p - z‖), by positivity, ?_⟩
  filter_upwards [herr, hconv] with k he hk
  have hcr := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    (hreal.differentiableOn.diffContOnCl_ball (Subset.rfl))
    (fun w hw => hB w (Metric.sphere_subset_closedBall hw))
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hrc : ‖coeff F k (p.re : ℂ)‖ ≤ B / r^k := by
    unfold coeff
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    change 1 / (k.factorial : ℝ) * _ ≤ _
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfac]
    exact hcr.trans_eq (by ring)
  have hscale : ‖p - z‖^k * ‖coeff F k (p.re : ℂ)‖ ≤ B * (‖p - z‖/r)^k :=
    (mul_le_mul_of_nonneg_left hrc (pow_nonneg hd.le _)).trans_eq (by rw [div_pow]; ring)
  have hcplx : ‖c‖ / 2 ≤ ‖p - z‖^(k+1) * ‖coeff F k p‖ := by
    rw [← norm_pow, ← norm_mul]
    exact hk
  have hpos : ‖c‖ / (2*‖p - z‖) ≤ ‖p - z‖^k * ‖coeff F k p‖ := by
    rw [div_mul_eq_div_div, div_le_iff₀ hd]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcplx
  have hn := (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (coeff F k (p.re : ℂ)))
    (pow_nonneg hd.le k)).trans hscale
  rw [mul_sub]
  have hid : ‖c‖ / (2*‖p - z‖) = 2 * (‖c‖ / (4*‖p - z‖)) := by ring
  linarith



/-- At a fixed convergence rate, an isolated closer complex pole and two
Gamma tail estimates force values beyond a signed exponential envelope in
every sufficiently late interval of the prescribed relative width. -/
private theorem signed_peaks_of_paired_disks {g : ℝ → ℝ} {F H : ℂ → ℂ}
    {p z c : ℂ} {r b h M α σ₀ : ℝ}
    (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (hM : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (2*u))
    (hM0 : 0 ≤ M)
    (hp : σ₀ < p.re) (hσ : 0 < p.re) (hα : 0 ≤ α)
    (hc : c ≠ 0) (hd : 0 < ‖p - z‖) (hdr : ‖p - z‖ < r)
    (hgap : ‖p - z‖ < p.re - α)
    (hcomplex : ∀ s ∈ Metric.closedBall p r, s ≠ z → AnalyticAt ℂ F s)
    (hreal : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r))
    (hH : AnalyticAt ℂ H z)
    (hprincipal : F =ᶠ[𝓝[≠] z] fun s => c / (s - z) + H s)
    (hh : 1 < h) (hb : h < b)
    (htilt : 2 < p.re * (1 - h/b))
    (hLtail : 0 ≤ p.re*(h*Real.log h-h+1)-2)
    (hRtail : 0 ≤ p.re*(b-h-h*Real.log (b/h))-2*b)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 →
      ∃ u ∈ Icc T (b*T), C * Real.exp (α*u) < e*g u := by
  let σ := p.re
  let d := ‖p - z‖
  let A := M * (1/σ + b/(h*σ))
  have hh0 : 0 < h := by linarith
  have hb1 : 1 < b := hh.trans hb
  have hb0 : 0 < b := by linarith
  have hα' : α < σ := by dsimp [σ]; linarith
  have hdσ : d < σ := hgap.trans_le (sub_le_self _ hα)
  obtain ⟨L, hL, hD⟩ := paired_disk_lower hc hd hdr hcomplex hreal hH hprincipal
  have hgamma := D5.S3.Analytic.Laplace.CriticalGammaWindow.adjustable_window_off_mass hh hb
  let ℓ := σ*(h*Real.log h-h+1)-2
  let r' := σ*(b-h-h*Real.log (b/h))-2*b
  have hK : Tendsto (fun T : ℝ => ⌊σ*h*T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.tendsto_id.const_mul_atTop (mul_pos hσ hh0))
  let q := d/(σ-α)
  let q' := d/σ
  have hq : 0 < q := div_pos hd (sub_pos.mpr hα')
  have hq1 : q < 1 := (div_lt_one (sub_pos.mpr hα')).mpr hgap
  have hq' : 0 < q' := div_pos hd hσ
  have hq1' : q' < 1 := (div_lt_one hσ).mpr hdσ
  have htime (j : ℝ) (hj : 0 < j) (hj1 : j < 1) :
      Tendsto (fun T : ℝ => T * j ^ ⌊σ*h*T⌋₊) atTop (𝓝 0) := by
    have hjlog : Real.log j < 0 := Real.log_neg hj hj1
    let τ := (σ*h) * Real.log j
    have hτ : τ < 0 := mul_neg_of_pos_of_neg (mul_pos hσ hh0) hjlog
    have hExp := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show τ / 2 < 0 by linarith))).const_mul j⁻¹
    have hLin : Tendsto (fun T : ℝ => T * Real.exp ((τ/2)*T)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-(τ/2))
        (neg_pos.mpr (show τ / 2 < 0 by linarith)))
      simpa only [Real.rpow_one, neg_neg] using h
    have hprod := hExp.mul hLin
    rw [mul_zero] at hprod
    apply squeeze_zero' _ _ hprod
    · exact (eventually_ge_atTop (0 : ℝ)).mono fun T hT => mul_nonneg hT (by positivity)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hfloor := Nat.lt_floor_add_one (σ*h*T)
      have he := mul_le_mul_of_nonpos_right (show σ*h*T - 1 ≤ (⌊σ*h*T⌋₊ : ℝ) by linarith)
        hjlog.le
      have hup := Real.exp_le_exp.mpr he
      rw [show Real.exp ((⌊σ*h*T⌋₊ : ℝ) * Real.log j) = j ^ ⌊σ*h*T⌋₊ by
        rw [mul_comm, ← Real.rpow_def_of_pos hj, Real.rpow_natCast],
        show (σ*h*T - 1) * Real.log j = -Real.log j + (τ/2)*T + (τ/2)*T by dsimp [τ]; ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hj] at hup
      exact (mul_le_mul_of_nonneg_left hup hT).trans_eq (by
        simp only [Function.comp_apply, id_eq]
        ring)
  have htailLim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq'.le hq1').comp hK).const_mul (2*A)
  have hboundLim := (htime q hq hq1).const_mul (2*C*(b-1))
  have hsmall : ∀ᶠ T : ℝ in atTop,
      2*C*(b-1) * (T*q^⌊σ*h*T⌋₊) + 2*A*q'^⌊σ*h*T⌋₊ < L := by
    have hh := hboundLim.add htailLim
    rw [mul_zero, mul_zero, add_zero] at hh
    exact hh.eventually_lt_const hL
  filter_upwards [eventually_gt_atTop (0 : ℝ), hK.eventually hD, hsmall] with T hT hdisc hsmallT
  intro e he
  by_contra! hnone
  let k := ⌊σ*h*T⌋₊
  have hTb : T ≤ b*T := le_mul_of_one_le_left hT.le hb1.le
  have hwindow (u : ℝ) (hu : u ∈ Icc T (b*T)) :
      max (e*g u) 0 * Real.exp (-α*u) ≤ C := by
    have hu' : max (e*g u) 0 ≤ C * Real.exp (α*u) :=
      max_le (hnone u hu) (by positivity)
    calc
      _ ≤ (C * Real.exp (α*u))*Real.exp (-α*u) :=
        mul_le_mul_of_nonneg_right hu' (by positivity)
      _ = C := by rw [neg_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hlocal : (∫ u in T..b*T, max (e*g u) 0 * Real.exp (-α*u)) ≤ C*((b-1)*T) := by
    have hcont : Continuous (fun u : ℝ => max (e*g u) 0 * Real.exp (-α*u)) :=
      ((hg.const_mul e).max continuous_const).mul (by fun_prop)
    have hl := intervalIntegral.integral_mono_on (μ := volume) hTb (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const (c := C)) hwindow
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      hl.trans_eq (by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring)
  have hTail := (hgamma.2 htilt hT hg.measurable hM).2
  have ht : (∫ u in Ioi (0 : ℝ) \ Icc T (b*T),
      |g u| * (u^k * Real.exp (-σ*u) / k.factorial)) ≤ A * σ⁻¹^k := by
    simp only [neg_mul]
    apply hTail.trans
    have hleft : Real.exp (-ℓ*T) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hLtail) hT.le)
    have hright : Real.exp (-r'*T) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRtail) hT.le)
    calc
      _ ≤ (M*σ⁻¹^k) * (1/σ + b/(h*σ)*1) := by gcongr
      _ = _ := by dsimp [A]; ring
  have hB := GeneralLaplaceMoments.signed_window_moment_bound hg hF k hp hT hTb hα' he
  change ‖coeff F k p‖ + e * (coeff F k (σ : ℂ)).re ≤ _ at hB
  have hsignLower : -|(coeff F k (σ : ℂ)).re| ≤ e * (coeff F k (σ : ℂ)).re := by
    rcases he with rfl | rfl
    · rw [one_mul]
      exact neg_le.mp (neg_le_abs _)
    · simpa only [neg_one_mul, neg_le_neg_iff] using le_abs_self (coeff F k (σ : ℂ)).re
  have hupper : ‖coeff F k p‖ - |(coeff F k (σ : ℂ)).re| ≤
      2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k) := by
    refine (show _ ≤ ‖coeff F k p‖ + e * (coeff F k (σ : ℂ)).re by linarith).trans
      (hB.trans (add_le_add ?_ (mul_le_mul_of_nonneg_left ht (by norm_num))))
    exact mul_le_mul_of_nonneg_left hlocal (by positivity)
  apply (not_lt_of_ge (hdisc.trans (mul_le_mul_of_nonneg_left hupper (pow_nonneg hd.le _))))
  simpa only [k, q, q', div_pow] using
    (show d^k * (2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k)) < L by
      rw [show d^k * (2*(σ-α)⁻¹^k * (C*((b-1)*T)) + 2*(A*σ⁻¹^k)) =
        2*C*(b-1)*(T*q^k) + 2*A*q'^k by
          simp only [q, q', div_eq_mul_inv, inv_pow]; ring]
      exact hsmallT)

#print axioms signed_peaks_of_paired_disks

end PairedLaplacePoleWindow

open PrimeTriangleLaplace (multiplier)

open private g logHinge logHinge_eq logHinge_transform cutoffCorrection
  cutoffCorrection_entire multiplier_norm_lower from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleLaplace

open private input_growth from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth

private def completedHinge (s : ℂ) : ℂ :=
  multiplier s * CompleteMangoldtAtOne.completed s - cutoffCorrection s

private theorem multiplier_differentiable : Differentiable ℂ multiplier := by
  unfold multiplier
  fun_prop

private theorem completedHinge_regular {s : ℂ} (hs : s ≠ 0) (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ completedHinge s :=
  ((multiplier_differentiable.analyticAt s).mul
    (CompleteMangoldtAtOne.completed_disk_cauchy.1.2.2.1 s hs hz)).sub
    (cutoffCorrection_entire.analyticAt s)

private theorem completedHinge_germ {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ (c : ℂ) (H : ℂ → ℂ), c ≠ 0 ∧ AnalyticAt ℂ H ρ ∧
      completedHinge =ᶠ[𝓝[≠] ρ] fun s => c / (s - ρ) + H s := by
  obtain ⟨_, hc, H, hH, hprincipal⟩ := transform_integral_and_zero_germs.2 ρ hz
  let a := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
  have hρ1' : ρ ≠ 1 := by intro h; subst ρ; norm_num at hρ1
  have hmul : multiplier ρ ≠ 0 := norm_pos_iff.mp
    ((multiplier_norm_lower hρ0 hρ1).1.trans_le (multiplier_norm_lower hρ0 hρ1).2)
  have hdslope : Differentiable ℂ (dslope multiplier ρ) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := univ) univ_mem).mpr
      multiplier_differentiable.differentiableOn
  refine ⟨multiplier ρ * a, fun s => multiplier s * H s + a * dslope multiplier ρ s -
    cutoffCorrection s, mul_ne_zero hmul hc, ?_, ?_⟩
  · exact (((multiplier_differentiable.analyticAt ρ).mul hH).add
      (analyticAt_const.mul (hdslope.analyticAt ρ))).sub (cutoffCorrection_entire.analyticAt ρ)
  · have hneq : ∀ᶠ s : ℂ in 𝓝[≠] ρ, s ≠ 1 :=
      (continuousAt_id.eventually_ne hρ1').filter_mono nhdsWithin_le_nhds
    filter_upwards [hprincipal, hneq, @self_mem_nhdsWithin ℂ _ ρ ({ρ} : Set ℂ)ᶜ]
      with s hs hs1 hsr
    have hsr' : s ≠ ρ := by simpa using hsr
    dsimp only [completedHinge, a]
    rw [CompleteMangoldtAtOne.completed_disk_cauchy.1.1 s hs1, hs,
      dslope_of_ne _ hsr', slope, smul_eq_mul, vsub_eq_sub]
    field_simp [sub_ne_zero.mpr hsr']
    ring

private theorem logHinge_continuous : Continuous logHinge := by
  have hg : Continuous g := U_exp_continuous
  exact ((hg.comp (continuous_id.add continuous_const)).sub
    ((hg.comp (continuous_id.add continuous_const)).const_mul 3)).add (hg.const_mul 2)

private theorem logHinge_growth : ∃ M : ℝ, 0 ≤ M ∧
    ∀ u, 0 ≤ u → |logHinge u| ≤ M * Real.exp (2*u) := by
  obtain ⟨M, hM0, hM⟩ := input_growth
  let h := Real.log 2
  have hh : 0 ≤ h := Real.log_nonneg (by norm_num)
  refine ⟨M * (Real.exp (4*h) + 3*Real.exp (2*h) + 2), by positivity, ?_⟩
  intro u hu
  have hg0 := hM u hu
  have hg1 := hM (u+h) (by linarith)
  have hg2 := hM (u+2*h) (by linarith)
  rw [show 2*(u+h) = 2*u+2*h by ring, Real.exp_add (2*u) (2*h)] at hg1
  rw [show 2*(u+2*h) = 2*u+4*h by ring, Real.exp_add (2*u) (4*h)] at hg2
  calc
    |logHinge u| ≤ |g (u+2*h)| + 3*|g (u+h)| + 2*|g u| := by
      unfold logHinge
      dsimp [h]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      apply add_le_add_left
      exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)])
    _ ≤ M * (Real.exp (2*u) * Real.exp (4*h)) +
        3*(M * (Real.exp (2*u) * Real.exp (2*h))) + 2*(M * Real.exp (2*u)) := by
      exact add_le_add (add_le_add hg2 (mul_le_mul_of_nonneg_left hg1 (by norm_num)))
        (mul_le_mul_of_nonneg_left hg0 (by norm_num))
    _ = _ := by ring

/-- An off-line zeta zero forces both signs of the centered Mangoldt triangle
beyond every fixed multiple of the scale with exponent α, strictly below
the real part of the zero, on every sufficiently late power window. -/
private theorem signed_logHinge_peaks {z₀ : ℂ} (hz : riemannZeta z₀ = 0)
    {α b C : ℝ} (hα : (1/2 : ℝ) ≤ α) (hβ : α < z₀.re)
    (hb : 1 < b) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 →
      ∃ u ∈ Icc T (b*T), C * Real.exp (α*u) < e * PrimeQuarterTriangle.hinge U (Real.exp u) := by
  obtain ⟨h, hh, hhb⟩ := exists_between hb
  let δ := (z₀.re - α)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ' : δ < z₀.re - 1/2 := by dsimp [δ]; linarith
  obtain ⟨σ, hσ, htilt, hL, hR⟩ :=
    ((eventually_gt_atTop (2:ℝ)).and
      ((D5.S3.Analytic.Laplace.CriticalGammaWindow.adjustable_window_off_mass hh hhb).1 0)).exists
  obtain ⟨p, ρ, r, hp, hρ, hd, hdr, hr, hre, hcomplex⟩ :=
    D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks.equal_radius_zero_disks hz hσ hδ hδ'
  have hd' : 0 < ‖p-ρ‖ := by simpa only [dist_eq_norm] using hd
  have hdr' : ‖p-ρ‖ < r := by simpa only [dist_eq_norm] using hdr
  have hρb : ρ ∈ Metric.closedBall p r := Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hdr.le)
  have hρ0 : 0 < ρ.re := by linarith [(hcomplex ρ hρb).1]
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρ
  obtain ⟨c, H, hc, hH, hprincipal⟩ := completedHinge_germ hρ hρ0 hρ1
  obtain ⟨M, hM0, hM⟩ := logHinge_growth
  have hs0 {s : ℂ} (hs : (1/2:ℝ) < s.re) : s ≠ 0 := by
    intro h; subst s; norm_num at hs
  have hF (s : ℂ) (hs : 1 < s.re) :
      IntegrableOn (fun u : ℝ => Complex.exp (-s*u) * (logHinge u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s*u) * (logHinge u : ℂ)) = completedHinge s := by
    have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
    change IntegrableOn (kernel logHinge s) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, kernel logHinge s u) = completedHinge s
    simpa only [completedHinge, CompleteMangoldtAtOne.completed_disk_cauchy.1.1 s hs1]
      using logHinge_transform hs
  have hA (s : ℂ) (hs : s ∈ Metric.closedBall p r) (hsρ : s ≠ ρ) :
      AnalyticAt ℂ completedHinge s :=
    completedHinge_regular (hs0 (hcomplex s hs).1) (fun he => hsρ ((hcomplex s hs).2 he))
  have hB : AnalyticOnNhd ℂ completedHinge (Metric.closedBall (p.re : ℂ) r) := by
    rw [hp]
    exact fun s hs => completedHinge_regular (hs0 (hre s hs).1) (hre s hs).2
  have hgap : ‖p-ρ‖ < p.re - α := by rw [hp]; dsimp [δ] at hr; linarith
  have hpeaks := PairedLaplacePoleWindow.signed_peaks_of_paired_disks
    logHinge_continuous hF hM hM0 (by rw [hp]; linarith) (by rw [hp]; linarith)
    (by linarith : 0 ≤ α) hc hd' hdr' hgap hA hB hH hprincipal hh hhb
    (by rw [hp]; exact htilt) (by rw [hp]; exact hL.le) (by rw [hp]; exact hR.le) hC
  simpa only [logHinge_eq] using hpeaks

#print axioms signed_logHinge_peaks


open private hinge_mangoldtRamp_eq primeTriangle_comparison eventual_hinge_lower_of_rh from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle

/-- On every sufficiently late power window, an off-line zero forces both
signed ordinary-prime triangle discrepancies beyond any fixed multiple of
the power with exponent α whenever 1/2 ≤ α < ρ.re. -/
private theorem signed_prime_triangle_power_windows {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    {α b C : ℝ} (hα : (1/2 : ℝ) ≤ α) (hβ : α < ρ.re)
    (hb : 1 < b) (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 →
      ∃ x ∈ Icc X (X ^ b), C * x ^ α <
        e * (PrimeQuarterTriangle.primeTriangleSum x - 2 * x * Real.log 2) := by
  obtain ⟨A, hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let E := 2 * max A 0
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpeaks := Real.tendsto_log_atTop.eventually
    (signed_logHinge_peaks hρ hα hβ hb (add_nonneg hC hE))
  filter_upwards [hpeaks, eventually_ge_atTop (1:ℝ)] with X hp hX
  intro e he
  have hX0 := zero_lt_one.trans_le hX
  obtain ⟨u, hu, hs⟩ := hp e he
  let x := Real.exp u
  have hx0 : 0 < x := Real.exp_pos _
  have hx : x ∈ Icc X (X ^ b) := by
    refine ⟨?_, ?_⟩
    · rw [← Real.exp_log hX0]
      exact Real.exp_le_exp.mpr hu.1
    · rw [Real.rpow_def_of_pos hX0]
      exact Real.exp_le_exp.mpr (by linarith only [hu.2])
  have hx1 : 1 ≤ x := hX.trans hx.1
  have hpower : x ^ α = Real.exp (α*u) := by
    rw [Real.rpow_def_of_pos hx0, show Real.log x = u from Real.log_exp u, mul_comm]
  have hroot : Real.sqrt x ≤ x ^ α := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hα
  have hEroot := mul_le_mul_of_nonneg_left hroot hE
  rw [← hpower, hinge_mangoldtRamp_eq hx0] at hs
  have hc := (hA (4*x)).trans
    (mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.sqrt_nonneg _))
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hc
  have hc' : Chebyshev.psi (4*x) - Chebyshev.theta (4*x) ≤ E * Real.sqrt x :=
    hc.trans_eq (by dsimp [E]; ring)
  obtain ⟨hlo, hhi⟩ := primeTriangle_comparison hx0.le
  refine ⟨x, hx, ?_⟩
  rcases he with rfl | rfl
  · simp only [one_mul, add_mul] at hs ⊢
    linarith only [hs, hc', hhi, hEroot]
  · simp only [neg_one_mul, add_mul] at hs ⊢
    have he0 : 0 ≤ E * x ^ α := mul_nonneg hE (Real.rpow_nonneg hx0.le _)
    linarith only [hs, hlo, he0]

#print axioms signed_prime_triangle_power_windows

/-- A single uniform lower constant on arbitrarily late full power windows
of the ordinary-prime triangle is equivalent to RH. -/
theorem rh_iff_frequently_prime_triangle_lower {b : ℝ} (hb : 1 < b) :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ X : ℝ in atTop,
      ∀ x ∈ Icc X (X ^ b), 2 * x * Real.log 2 - C * Real.sqrt x ≤
        PrimeQuarterTriangle.primeTriangleSum x := by
  constructor
  · intro rh
    obtain ⟨A, hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    refine ⟨10 + 2 * max A 0, by positivity, ?_⟩
    obtain ⟨T, hT⟩ := eventually_atTop.mp (eventual_hinge_lower_of_rh rh)
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (max T 1)] with X hX x hx
    have hxT := ((le_max_left T 1).trans hX).trans hx.1
    have hx0 : 0 < x := zero_lt_one.trans_le (((le_max_right T 1).trans hX).trans hx.1)
    have hc := (hA (4*x)).trans
      (mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.sqrt_nonneg _))
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hc
    have hd := (primeTriangle_comparison hx0.le).2
    have he := hT x hxT
    rw [hinge_mangoldtRamp_eq hx0] at he
    linarith only [hc, hd, he]
  · rintro ⟨C, hC, hgood⟩
    apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro ρ hρ hβ _
    have hpeaks := signed_prime_triangle_power_windows hρ le_rfl hβ hb hC
    obtain ⟨X, hp, hwin⟩ := (hpeaks.and_frequently hgood).exists
    obtain ⟨x, hx, hs⟩ := hp (-1) (Or.inr rfl)
    rw [← Real.sqrt_eq_rpow, neg_one_mul] at hs
    linarith only [hwin x hx, hs]

#print axioms rh_iff_frequently_prime_triangle_lower

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerWindow
