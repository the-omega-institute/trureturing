/- GID: D5/S3/Weil/Separator/WeilSmallSupportCoercive
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/WeilSmallSupportCoercive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Bounds]
   utility: none
   digest: Prove a fixed-support mass margin for the actual gamma jump and Weil square. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Separator.UnconditionalExplicitFormula
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Coercivity for small-support Weil test functions

For support in `[-1/20, 1/20]`, shifts above `1/20` cost at least one copy
of the squared L² norm and shifts above `1/10` cost two. Integrating a finite
geometric lower bound for the actual gamma density yields a margin of
`1/20` after the constant term. The native explicit formula preserves the
full boundary term, with an empty prime-power window at this support scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.WeilSmallSupportCoercive

open Real Set MeasureTheory Finset
open D5.S3.Weil.TestFunctions D5.S3.Weil.ZeroSum D5.S3.Weil.FourierLaplace
open D5.S3.Weil.Separator.ArchimedeanConvergence
open D5.S3.Weil.Separator.UnconditionalExplicitFormula
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open scoped ComplexConjugate

open private translation_energy_nonnegative integrable_normSq integrable_correlation
  convolution_square_re
  translation_energy_eq_correlation translation_energy_fourier
  integrable_spectral_normSq integrable_spectral_increment from
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

private theorem f_zero_outside (f : WeilTestFunction)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20))
    (x : ℝ) (hx : x ∉ Icc (-(1 / 20 : ℝ)) (1 / 20)) : f x = 0 := by
  by_contra h
  exact hx (hSupport (subset_tsupport _ h))

private theorem mass_nonnegative (f : WeilTestFunction) : 0 ≤ l2Mass f := by
  unfold l2Mass
  exact integral_nonneg fun x => Complex.normSq_nonneg _

/-- Shifts longer than the full support diameter have disjoint support. -/
private theorem translation_two_mass (f : WeilTestFunction)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20))
    {u : ℝ} (hu : 1 / 10 < u) : translationEnergy f u = 2 * l2Mass f := by
  rw [translation_energy_eq_correlation, convolution_square_re]
  have hZero : (∫ x : ℝ, (f x * conj (f (x - u))).re) = 0 := by
    calc
      _ = ∫ _x : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ≤ 1 / 20
        · rw [f_zero_outside f hSupport (x - u) (by rw [Set.mem_Icc]; rintro ⟨hl, hr⟩; linarith)]
          simp
        · rw [f_zero_outside f hSupport x (by rw [Set.mem_Icc]; rintro ⟨hl, hr⟩; linarith)]
          simp
      _ = 0 := by simp
  rw [hZero]
  ring

/-- For a shift larger than half the support diameter the correlation uses
opposite half-intervals, which share no L2 mass. -/
private theorem translation_one_mass (f : WeilTestFunction)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20))
    {u : ℝ} (hu : 1 / 20 < u) : l2Mass f ≤ translationEnergy f u := by
  let g : ℝ → ℝ := fun x => Complex.normSq (f x)
  let gp : ℝ → ℝ := (Ioi (0 : ℝ)).indicator g
  let gm : ℝ → ℝ := (Iic (0 : ℝ)).indicator g
  have hg : Integrable g := integrable_normSq f
  have hgp : Integrable gp := hg.indicator measurableSet_Ioi
  have hgm : Integrable gm := hg.indicator measurableSet_Iic
  have hgmShift := hgm.comp_sub_right u
  have hPoint (x : ℝ) : 2 * (f x * conj (f (x - u))).re ≤ gp x + gm (x - u) := by
    by_cases hx : 0 < x
    · by_cases hy : x - u ≤ 0
      · simp only [gp, gm, Set.mem_Ioi, Set.mem_Iic, hx, hy, indicator_of_mem, g]
        nlinarith [Complex.normSq_nonneg (f x - f (x - u)),
          Complex.normSq_sub (f x) (f (x - u))]
      · have hxf : f x = 0 := f_zero_outside f hSupport x (by
          rw [Set.mem_Icc]; rintro ⟨hl, hr⟩; linarith)
        simp [gp, gm, g, hx, hy, hxf]
    · have hy : x - u ≤ 0 := by linarith
      have hyf : f (x - u) = 0 := f_zero_outside f hSupport (x - u) (by
        rw [Set.mem_Icc]; rintro ⟨hl, hr⟩; linarith)
      simp [gp, gm, g, hx, hy, hyf]
  have hInt : (∫ x : ℝ, 2 * (f x * conj (f (x - u))).re) ≤
      ∫ x : ℝ, gp x + gm (x - u) :=
    integral_mono_ae ((integrable_correlation f u).re.const_mul 2)
      (hgp.add hgmShift) (Filter.Eventually.of_forall hPoint)
  rw [integral_const_mul, integral_add hgp hgmShift,
    integral_sub_right_eq_self gm u] at hInt
  have hParts : (∫ x, gp x) + (∫ x, gm x) = l2Mass f := by
    change (∫ x, (Ioi (0 : ℝ)).indicator g x) +
      (∫ x, (Iic (0 : ℝ)).indicator g x) = ∫ x, g x
    rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iic,
      ← compl_Ioi]
    exact integral_add_compl measurableSet_Ioi hg
  rw [hParts] at hInt
  rw [translation_energy_eq_correlation, convolution_square_re]
  linarith

/-- Actual integrability of the positive continuous gamma-jump integrand. This
reuses the existing product-integrability proof behind the gamma identity. -/
private theorem integrable_jump (f : WeilTestFunction) :
    IntegrableOn (fun u : ℝ => archimedeanJumpDensity u * translationEnergy f u) (Ioi 0) := by
  let F : ℝ × ℝ → ℝ := fun p =>
    (1 / (2 * π)) * Complex.normSq (fourierLaplace f p.2) *
      (2 * archimedeanJumpDensity p.1 * (1 - Real.cos (p.2 * p.1)))
  have hDensity : AEStronglyMeasurable archimedeanJumpDensity
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold archimedeanJumpDensity
    measurability
  have hSpec := (integrable_spectral_normSq f).aestronglyMeasurable
  have hMeas : AEStronglyMeasurable F ((volume.restrict (Ioi 0)).prod volume) := by
    dsimp only [F]
    exact (hSpec.comp_snd.const_mul (1 / (2 * π))).mul
      ((hDensity.comp_fst.const_mul 2).mul (by fun_prop))
  have hSec (t : ℝ) : Integrable (fun u : ℝ => F (u,t)) (volume.restrict (Ioi 0)) := by
    have h := (levy_kernel_integrableOn t).const_mul
      ((1 / (2 * π)) * Complex.normSq (fourierLaplace f t))
    exact h
  have hInner (t : ℝ) : (∫ u : ℝ in Ioi 0, ‖F (u,t)‖) =
      (1 / (2 * π)) * Complex.normSq (fourierLaplace f t) *
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          (Complex.digamma (1 / 4)).re) := by
    have hEq : (∫ u : ℝ in Ioi 0, ‖F (u,t)‖) = ∫ u : ℝ in Ioi 0, F (u,t) := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg]
      dsimp only [F]
      exact mul_nonneg (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) (jump_density_nonnegative hu))
          (sub_nonneg.mpr (Real.cos_le_one _)))
    rw [hEq]
    dsimp only [F]
    rw [integral_const_mul, levy_integral_eq_digamma_increment]
  have hOuter : Integrable (fun t : ℝ => ∫ u : ℝ in Ioi 0, ‖F (u,t)‖) := by
    refine ((integrable_spectral_increment f
      (archimedeanConvergent_of_weilTestFunction (convolutionSquare f))).const_mul
        (1 / (2 * π))).congr ?_
    filter_upwards with t
    rw [hInner]
    ring
  have hF : Integrable F ((volume.restrict (Ioi 0)).prod volume) :=
    (integrable_prod_iff' hMeas).2 ⟨Filter.Eventually.of_forall hSec, hOuter⟩
  refine hF.integral_prod_left.congr ?_
  filter_upwards with u
  rw [translation_energy_fourier]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [F]
  ring

private def rate (j : ℕ) : ℝ := 2 * (j : ℝ) + 1 / 2
private def finiteKernel (u : ℝ) : ℝ :=
  ∑ j ∈ range 24, exp (-(rate j) * u)

private theorem rate_pos (j : ℕ) : 0 < rate j := by unfold rate; positivity

private theorem finite_kernel_le (u : ℝ) (hu : 0 < u) :
    finiteKernel u ≤ archimedeanJumpDensity u := by
  let r := exp (-2 * u)
  have hr : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - r := sub_pos.mpr hr1
  have hEq : finiteKernel u = exp (-u / 2) * ∑ j ∈ range 24, r^j := by
    rw [finiteKernel, mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp only [rate, r]
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    ring
  have hGeom : (∑ j ∈ range 24, r^j) ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ hd).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg hr 24]
  rw [hEq, archimedeanJumpDensity]
  calc
    _ ≤ exp (-u / 2) * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hGeom (exp_pos _).le
    _ = exp (-u / 2) / (1 - exp (-2 * u)) := by dsimp [r]; ring

private theorem finite_kernel_integrable (a : ℝ) : IntegrableOn finiteKernel (Ioi a) := by
  unfold finiteKernel IntegrableOn
  refine integrable_finsetSum (range 24) ?_
  intro j hj
  exact integrableOn_exp_mul_Ioi (neg_neg_of_pos (rate_pos j)) a

private theorem finite_kernel_integral (a : ℝ) :
    (∫ u : ℝ in Ioi a, finiteKernel u) =
      ∑ j ∈ range 24, exp (-(rate j) * a) / rate j := by
  unfold finiteKernel
  rw [integral_finsetSum (range 24)]
  · apply sum_congr rfl
    intro j hj
    rw [integral_exp_mul_Ioi (neg_neg_of_pos (rate_pos j))]
    ring
  · intro j hj
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos (rate_pos j)) a

private theorem exp_neg_lower32 (t : ℝ) (ht : t ≤ 32) :
    (1 - t / 32)^32 ≤ exp (-t) := by
  have hh : 0 ≤ 1 - t / 32 := by linarith
  have h := pow_le_pow_left₀ hh (Real.one_sub_le_exp_neg (t / 32)) 32
  rw [← exp_nat_mul] at h
  convert h using 2
  ring

set_option maxHeartbeats 1000000 in
-- The fixed 48-term rational certificate reduces to exact field arithmetic.
private theorem finite_kernel_integrals_lower :
    (277 / 50 : ℝ) ≤ (∫ u : ℝ in Ioi (1 / 20), finiteKernel u) +
      (∫ u : ℝ in Ioi (1 / 10), finiteKernel u) := by
  rw [finite_kernel_integral, finite_kernel_integral]
  have hBound (a : ℝ) (ha : a ≤ 1 / 10) (j : ℕ) (hj : j ∈ range 24) :
      (1 - rate j * a / 32)^32 / rate j ≤ exp (-(rate j) * a) / rate j := by
    apply div_le_div_of_nonneg_right _ (rate_pos j).le
    have hj' : (j : ℝ) < 24 := by exact_mod_cast mem_range.mp hj
    have ht : rate j * a ≤ 32 := by
      have h1 := mul_le_mul_of_nonneg_left ha (rate_pos j).le
      unfold rate at *
      nlinarith
    simpa only [neg_mul] using exp_neg_lower32 (rate j * a) ht
  have h1 := sum_le_sum (fun j hj => hBound (1 / 20) (by norm_num) j hj)
  have h2 := sum_le_sum (fun j hj => hBound (1 / 10) (by norm_num) j hj)
  have hRat : (277 / 50 : ℝ) ≤
      (∑ j ∈ range 24, (1 - rate j * (1 / 20) / 32)^32 / rate j) +
      (∑ j ∈ range 24, (1 - rate j * (1 / 10) / 32)^32 / rate j) := by
    norm_num [rate, Finset.sum_range_succ]
  linarith

private theorem archimedean_constant_lower : -(549 / 100 : ℝ) ≤ archimedeanConstant := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hLog : log π < 23 / 20 := by
    apply (Real.log_lt_iff_lt_exp Real.pi_pos).mpr
    have hExp := Real.sum_le_exp_of_nonneg (x := (23 / 20 : ℝ)) (by norm_num) 7
    have hRat : (3.15 : ℝ) < ∑ i ∈ range 7, (23 / 20 : ℝ)^i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ]
    exact Real.pi_lt_d2.trans (hRat.trans_le hExp)
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1) -
    ((n : ℝ)+1+1 / 4) / (((n : ℝ)+1+1 / 4)^2 + (0 : ℝ)^2)
  have hSum : Summable v := Zeta23.MuFields.summable_re_terms
    (a := 1 / 4) (by norm_num) (by norm_num) 0
  have hPos (n : ℕ) : 0 ≤ v n := by
    have hn : 0 < (n : ℝ)+1+1 / 4 := by positivity
    have h1 : ((n : ℝ)+1+1 / 4) / (((n : ℝ)+1+1 / 4)^2 + (0 : ℝ)^2) =
        1 / ((n : ℝ)+1+1 / 4) := by field_simp; ring
    dsimp only [v]
    rw [h1]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hPart : (329 / 1000 : ℝ) ≤ ∑ j ∈ range 12, v j := by
    norm_num [v, Finset.sum_range_succ]
  have hTotal := hSum.sum_le_tsum (range 12) (fun j _ => hPos j)
  have hPsi := Zeta23.MuFields.re_digamma_vertical
    (a := 1 / 4) (by norm_num) (by norm_num) 0
  have hPsi' : (Complex.digamma (1 / 4)).re =
      -Real.eulerMascheroniConstant - 4 + ∑' n, v n := by
    norm_num [v] at hPsi ⊢
    exact hPsi
  rw [archimedeanConstant, hPsi']
  linarith only [hγ, hLog, hPart.trans hTotal]

/-- The actual gamma-jump energy pays a uniform explicit mass margin on the
fixed interval. The proof integrates two overlapping positive tail lower bounds. -/
theorem smallSupport_gamma_coercive (f : WeilTestFunction)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20)) :
    (1 / 20 : ℝ) * l2Mass f ≤
      archimedeanConstant * l2Mass f + archimedeanJumpEnergy f := by
  let M := l2Mass f
  let H : ℝ → ℝ := fun u => M * finiteKernel u
  let G : ℝ → ℝ := fun u => (Ioi (1 / 20 : ℝ)).indicator H u +
    (Ioi (1 / 10 : ℝ)).indicator H u
  have hM : 0 ≤ M := mass_nonnegative f
  have hH (a : ℝ) : IntegrableOn H (Ioi a) := (finite_kernel_integrable a).const_mul M
  have hG1 : Integrable ((Ioi (1 / 20 : ℝ)).indicator H) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hH (1 / 20))
  have hG2 : Integrable ((Ioi (1 / 10 : ℝ)).indicator H) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hH (1 / 10))
  have hGi : Integrable G := hG1.add hG2
  have hPoint (u : ℝ) (hu : 0 < u) : G u ≤ archimedeanJumpDensity u * translationEnergy f u := by
    have hk := finite_kernel_le u hu
    have hk0 := jump_density_nonnegative hu
    have hE0 := translation_energy_nonnegative f u
    by_cases h10 : 1 / 10 < u
    · have h20 : 1 / 20 < u := by linarith
      simp only [G, H, Set.mem_Ioi, h20, h10, indicator_of_mem]
      rw [translation_two_mass f hSupport h10]
      have h := mul_le_mul_of_nonneg_right hk hM
      dsimp [M] at *
      nlinarith
    · by_cases h20 : 1 / 20 < u
      · dsimp only [G]
        rw [indicator_of_mem (show u ∈ Ioi (1 / 20 : ℝ) from h20),
          indicator_of_notMem (show u ∉ Ioi (1 / 10 : ℝ) from h10), add_zero]
        calc
          M * finiteKernel u ≤ M * archimedeanJumpDensity u := mul_le_mul_of_nonneg_left hk hM
          _ ≤ archimedeanJumpDensity u * translationEnergy f u := by
            rw [mul_comm M]
            exact mul_le_mul_of_nonneg_left (translation_one_mass f hSupport h20) hk0
      · dsimp only [G]
        rw [indicator_of_notMem (show u ∉ Ioi (1 / 20 : ℝ) from h20),
          indicator_of_notMem (show u ∉ Ioi (1 / 10 : ℝ) from h10), add_zero]
        exact mul_nonneg hk0 hE0
  have hCompare : (∫ u : ℝ in Ioi (0 : ℝ), G u) ≤
      ∫ u : ℝ in Ioi (0 : ℝ), archimedeanJumpDensity u * translationEnergy f u := by
    refine setIntegral_mono_ae_restrict hGi.integrableOn (integrable_jump f) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact hPoint u hu
  have hGAll : (∫ u : ℝ in Ioi (0 : ℝ), G u) = ∫ u : ℝ, G u := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : 0 < u
    · simp [hu]
    · have h1 : ¬ (1 / 20 : ℝ) < u := by linarith
      have h2 : ¬ (1 / 10 : ℝ) < u := by linarith
      rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]
      dsimp only [G]
      rw [indicator_of_notMem (show u ∉ Ioi (1 / 20 : ℝ) from h1),
        indicator_of_notMem (show u ∉ Ioi (1 / 10 : ℝ) from h2), add_zero]
  have hGValue : (∫ u : ℝ, G u) = M *
      ((∫ u : ℝ in Ioi (1 / 20), finiteKernel u) +
        (∫ u : ℝ in Ioi (1 / 10), finiteKernel u)) := by
    dsimp only [G]
    rw [integral_add hG1 hG2, integral_indicator measurableSet_Ioi,
      integral_indicator measurableSet_Ioi]
    dsimp only [H]
    rw [integral_const_mul, integral_const_mul, mul_add]
  rw [hGAll, hGValue] at hCompare
  have hEnergy : (277 / 50 : ℝ) * M ≤ archimedeanJumpEnergy f := by
    unfold archimedeanJumpEnergy
    calc
      _ ≤ M * ((∫ u : ℝ in Ioi (1 / 20), finiteKernel u) +
        (∫ u : ℝ in Ioi (1 / 10), finiteKernel u)) := by
          rw [mul_comm (277 / 50 : ℝ)]
          exact mul_le_mul_of_nonneg_left finite_kernel_integrals_lower hM
      _ ≤ _ := hCompare
  have hConst := mul_le_mul_of_nonneg_right archimedean_constant_lower hM
  dsimp only [M] at hEnergy hConst
  linarith

/-- Actual Weil-square coercivity for the fixed support, with both convergence
witnesses supplied by the native explicit formula. -/
theorem smallSupport_weil_positive (Z : ZeroData) (f : WeilTestFunction)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-(1 / 20 : ℝ)) (1 / 20)) :
    2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
      (1 / 20 : ℝ) * l2Mass f ≤
    (zeroSum Z (convolutionSquare f)
      (symmetricConvergent_of_zeroData Z (convolutionSquare f))).re := by
  have hL : Real.exp (2 * (1 / 20 : ℝ)) < 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 10 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hE := energyIdentity_unconditional Z f (1 / 20) (by simpa using hSupport)
  have hEmpty := activePrimePowers_eq_empty_of_exp_lt_two (1 / 20) hL
  rw [hE]
  simp only [totalPrimeWeight, arithmeticJumpEnergy, hEmpty, Finset.sum_empty,
    Complex.ofReal_re]
  linarith [smallSupport_gamma_coercive f hSupport]

#print axioms smallSupport_gamma_coercive
#print axioms smallSupport_weil_positive

end
end D5.S3.Weil.Separator.WeilSmallSupportCoercive
