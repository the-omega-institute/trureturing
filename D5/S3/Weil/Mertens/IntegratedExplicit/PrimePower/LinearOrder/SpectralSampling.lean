/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/SpectralSampling
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/SpectralSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local energy and separated samples for finite spectra with repeated frequencies. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Algebra.Order.ToIntervalMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Complex MeasureTheory Finset Set Function

private def gaussPhase (c d v : ℝ) : ℂ :=
  Complex.exp (-((v - c : ℝ) : ℂ)^2 + Complex.I * (d : ℂ) * (v : ℂ))

private theorem gaussPhase_integrable (c d : ℝ) : Integrable (gaussPhase c d) := by
  convert integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num)
    (2 * (c : ℂ) + Complex.I * (d : ℂ)) (-((c : ℂ)^2)) using 1
  ext v
  unfold gaussPhase
  push_cast
  congr 1
  ring

private theorem integral_gaussPhase (c d : ℝ) :
    ∫ v, gaussPhase c d v =
      ((Real.pi : ℂ) ^ (1/2 : ℂ)) *
        Complex.exp (-((d : ℂ)^2) / 4 + Complex.I * (d : ℂ) * (c : ℂ)) := by
  rw [show gaussPhase c d = (fun v : ℝ =>
    Complex.exp ((-1 : ℂ) * (v : ℂ)^2 + (2 * (c : ℂ) + Complex.I * (d : ℂ)) * (v : ℂ) -
      (c : ℂ)^2)) by
    funext v
    unfold gaussPhase
    push_cast
    congr 1
    ring]
  simp_rw [sub_eq_add_neg]
  rw [integral_cexp_quadratic (by norm_num : ((-1 : ℂ)).re < 0)]
  simp only [neg_neg, div_one]
  congr 2
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul]
  ring

private theorem norm_integral_gaussPhase (c d : ℝ) :
    ‖∫ v, gaussPhase c d v‖ =
      ‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * Real.exp (-(d^2) / 4) := by
  rw [integral_gaussPhase, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, pow_two]

private theorem separated_gauss_bound {k l : ℤ} {x y : ℝ}
    (hx : x ∈ Set.Ioc (k : ℝ) ((k : ℝ) + 1))
    (hy : y ∈ Set.Ioc (l : ℝ) ((l : ℝ) + 1)) :
    Real.exp (-((x-y)^2) / 4) ≤ Real.exp (1/2 - |(k : ℝ) - l| / 4) := by
  apply Real.exp_le_exp.mpr
  have h : |(k : ℝ)-l| ≤ |x-y| + 1 := by
    have hx' : (k : ℝ) < x ∧ x ≤ (k : ℝ) + 1 := hx
    have hy' : (l : ℝ) < y ∧ y ≤ (l : ℝ) + 1 := hy
    rw [abs_le]
    constructor
    · have hl := neg_abs_le (x-y)
      linarith only [hx'.2, hy'.1, hl]
    · have hr := le_abs_self (x-y)
      linarith only [hx'.1, hy'.2, hr]
  have hs : |x-y| ≤ (x-y)^2 + 1 := by
    nlinarith only [sq_abs (x-y), sq_nonneg (|x-y| - 1/2)]
  linarith

def finiteModes (S : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (v : ℝ) : ℂ :=
  ∑ i ∈ S, a i * Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ))

private def spectralWeight (c v : ℝ) : ℝ := Real.exp (-(v - c)^2)

private theorem finiteModes_weight_eq (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (c v : ℝ) :
    ((spectralWeight c v * ‖finiteModes S γ a v‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * (starRingEnd ℂ) (a j)) * gaussPhase c (γ i - γ j) v := by
  unfold finiteModes
  push_cast
  rw [← Complex.mul_conj', ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hphase :
      ((spectralWeight c v : ℝ) : ℂ) * Complex.exp (Complex.I * (γ i : ℂ) * (v : ℂ)) *
          (starRingEnd ℂ) (Complex.exp (Complex.I * (γ j : ℂ) * (v : ℂ))) =
        gaussPhase c (γ i - γ j) v := by
    unfold spectralWeight gaussPhase
    rw [Complex.ofReal_exp, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    congr 1
    ring
  rw [← hphase]
  ring

private theorem finiteModes_weight_integrable (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (c : ℝ) :
    Integrable (fun v => spectralWeight c v * ‖finiteModes S γ a v‖^2) := by
  have h : Integrable (fun v => ((spectralWeight c v * ‖finiteModes S γ a v‖^2 : ℝ) : ℂ)) := by
    simp_rw [finiteModes_weight_eq]
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (gaussPhase_integrable c (γ i - γ j)).const_mul _
  have hr := h.re
  change Integrable (fun v => ((spectralWeight c v * ‖finiteModes S γ a v‖^2 : ℝ) : ℂ).re) at hr
  simpa only [Complex.ofReal_re] using hr

private theorem finiteModes_weight_integral (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (c : ℝ) :
    ((∫ v, spectralWeight c v * ‖finiteModes S γ a v‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * (starRingEnd ℂ) (a j)) *
        (∫ v, gaussPhase c (γ i - γ j) v) := by
  rw [← integral_complex_ofReal]
  simp_rw [finiteModes_weight_eq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro j hj
      exact (gaussPhase_integrable c (γ i - γ j)).const_mul _
  · intro i hi
    exact integrable_finsetSum _ (fun j hj =>
      (gaussPhase_integrable c (γ i - γ j)).const_mul _)

private def binKernel (d : ℤ) : ℝ := Real.exp (1/2 - |(d : ℝ)| / 4)

private theorem binKernel_summable : Summable binKernel := by
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-1/4 : ℝ)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1/4 : ℝ) < 0))
  have h : Summable (fun n : ℕ => Real.exp (1/2) * Real.exp (-1/4 : ℝ)^n) :=
    hg.mul_left _
  rw [summable_int_iff_summable_nat_and_neg]
  have hp : ∀ n : ℕ, binKernel (n : ℤ) = Real.exp (1/2) * Real.exp (-1/4 : ℝ)^n := by
    intro n
    unfold binKernel
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  exact ⟨h.congr fun n => (hp n).symm, h.congr fun n => by
    simpa [binKernel, Int.cast_neg, abs_neg] using (hp n).symm⟩

private theorem binKernel_row_le (B : Finset ℤ) (k : ℤ) :
    ∑ l ∈ B, binKernel (k-l) ≤ ∑' d : ℤ, binKernel d := by
  let e : ℤ ≃ ℤ := Equiv.subLeft k
  have h : ∑ l ∈ B, binKernel (k-l) = ∑ d ∈ B.map e.toEmbedding, binKernel d := by
    rw [Finset.sum_map]
    rfl
  rw [h]
  exact binKernel_summable.sum_le_tsum _ (fun d _ => (Real.exp_pos _).le)

private theorem binKernel_symm (k l : ℤ) : binKernel (k-l) = binKernel (l-k) := by
  unfold binKernel
  rw [show l-k = -(k-l) by omega, Int.cast_neg, abs_neg]

private theorem binEnergy_le (B : Finset ℤ) (mass : ℤ → ℝ) :
    ∑ k ∈ B, ∑ l ∈ B, mass k * mass l * binKernel (k-l) ≤
      (∑' d : ℤ, binKernel d) * (∑ k ∈ B, mass k ^ 2) := by
  have hrow : (∑ k ∈ B, ∑ l ∈ B, mass k ^ 2 * binKernel (k-l)) ≤
      (∑' d : ℤ, binKernel d) * (∑ k ∈ B, mass k ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.mul_sum, mul_comm (∑' d : ℤ, binKernel d)]
    exact mul_le_mul_of_nonneg_left (binKernel_row_le B k) (sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ B, ∑ l ∈ B, (mass k ^ 2 + mass l ^ 2) / 2 * binKernel (k-l) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith only [sq_nonneg (mass k - mass l)]
    _ = ∑ k ∈ B, ∑ l ∈ B, mass k ^ 2 * binKernel (k-l) := by
      have hswap :
          (∑ k ∈ B, ∑ l ∈ B, mass l ^ 2 * binKernel (k-l)) =
            ∑ k ∈ B, ∑ l ∈ B, mass k ^ 2 * binKernel (k-l) := by
        rw [Finset.sum_comm]
        simp_rw [binKernel_symm]
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ ≤ _ := hrow

def frequencyBin (γ : ℝ) : ℤ := ⌈γ⌉ - 1

theorem mem_frequencyBin (x : ℝ) :
    x ∈ Set.Ioc (frequencyBin x : ℝ) ((frequencyBin x : ℝ) + 1) := by
  unfold frequencyBin
  simp only [Int.cast_sub, Int.cast_one, Set.mem_Ioc]
  constructor
  · have h := (Int.le_ceil_iff (a := x) (z := ⌈x⌉)).mp le_rfl
    linarith
  · have h := Int.le_ceil x
    linarith

def binMass (S : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (k : ℤ) : ℝ :=
  ∑ i ∈ S with frequencyBin (γ i) = k, ‖a i‖

private theorem regroup_binEnergy (S : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ * binKernel (frequencyBin (γ i) - frequencyBin (γ j))) =
      ∑ k ∈ S.image (frequencyBin ∘ γ), ∑ l ∈ S.image (frequencyBin ∘ γ),
        binMass S γ a k * binMass S γ a l * binKernel (k-l) := by
  classical
  let g := frequencyBin ∘ γ
  let B := S.image g
  have hg : ∀ i ∈ S, g i ∈ B := fun i hi => Finset.mem_image_of_mem g hi
  calc
    _ = ∑ k ∈ B, ∑ i ∈ S with g i = k, ∑ l ∈ B, ∑ j ∈ S with g j = l,
        ‖a i‖ * ‖a j‖ * binKernel (g i - g j) := by
      rw [Finset.sum_fiberwise_of_maps_to hg]
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.sum_fiberwise_of_maps_to hg _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      unfold binMass
      change _ = (∑ i ∈ S with g i = k, ‖a i‖) *
        (∑ j ∈ S with g j = l, ‖a j‖) * binKernel (k-l)
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]

private theorem gaussian_bin_energy_le (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (c : ℝ) :
    (∫ v, spectralWeight c v * ‖finiteModes S γ a v‖^2) ≤
      (‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * (∑' d : ℤ, binKernel d)) *
        (∑ k ∈ S.image (frequencyBin ∘ γ), binMass S γ a k ^ 2) := by
  let C : ℝ := ‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖
  have hnonneg : 0 ≤ ∫ v, spectralWeight c v * ‖finiteModes S γ a v‖^2 :=
    integral_nonneg (fun v => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖((∫ v, spectralWeight c v * ‖finiteModes S γ a v‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖a i * (starRingEnd ℂ) (a j) *
        (∫ v, gaussPhase c (γ i - γ j) v)‖ := by
      rw [finiteModes_weight_integral]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_sum_le _ _)
    _ ≤ C * (∑ i ∈ S, ∑ j ∈ S,
        ‖a i‖ * ‖a j‖ * binKernel (frequencyBin (γ i) - frequencyBin (γ j))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul, RCLike.norm_conj, norm_integral_gaussPhase]
      change ‖a i‖ * ‖a j‖ * (C * Real.exp (-((γ i - γ j)^2) / 4)) ≤ _
      rw [show C * (‖a i‖ * ‖a j‖ * binKernel (frequencyBin (γ i) - frequencyBin (γ j))) =
          ‖a i‖ * ‖a j‖ * (C * binKernel (frequencyBin (γ i) - frequencyBin (γ j))) by ring]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold binKernel
      rw [Int.cast_sub]
      exact separated_gauss_bound (mem_frequencyBin _) (mem_frequencyBin _)
    _ ≤ _ := by
      rw [regroup_binEnergy, mul_assoc]
      exact mul_le_mul_of_nonneg_left (binEnergy_le _ _) (norm_nonneg _)

private theorem local_bin_energy_le (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (c : ℝ) :
    (∫ v in Set.Icc (c-1) (c+1), ‖finiteModes S γ a v‖^2) ≤
      (Real.exp 1 * (‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * (∑' d : ℤ, binKernel d))) *
        (∑ k ∈ S.image (frequencyBin ∘ γ), binMass S γ a k ^ 2) := by
  have hcont : Continuous (fun v => finiteModes S γ a v) := by
    unfold finiteModes
    fun_prop
  have hInt := finiteModes_weight_integrable S γ a c
  calc
    _ ≤ ∫ v in Set.Icc (c-1) (c+1), Real.exp 1 *
        (spectralWeight c v * ‖finiteModes S γ a v‖^2) := by
      apply setIntegral_mono_on ((hcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
        ((hInt.const_mul _).integrableOn) measurableSet_Icc
      intro v hv
      have hv' : |v-c| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
      have hs : (v-c)^2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith only [hv', abs_nonneg (v-c), mul_nonneg (sub_nonneg.mpr hv')
          (show 0 ≤ 1 + |v-c| by positivity)]
      have hw : 1 ≤ Real.exp (1 + -(v-c)^2) := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 + -(v-c)^2 by linarith))
      change ‖finiteModes S γ a v‖^2 ≤ _
      rw [← mul_assoc, spectralWeight, ← Real.exp_add]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hw (sq_nonneg ‖finiteModes S γ a v‖)
    _ ≤ ∫ v, Real.exp 1 * (spectralWeight c v * ‖finiteModes S γ a v‖^2) := by
      apply integral_mono_measure Measure.restrict_le_self _ (hInt.const_mul _)
      exact Filter.Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ ≤ _ := by
      rw [integral_const_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (gaussian_bin_energy_le S γ a c) (Real.exp_pos _).le

private theorem integrated_abs_difference_le {f f' : ℝ → ℂ} {l r x y : ℝ}
    (hf : ∀ z, HasDerivAt f (f' z) z) (hcont : Continuous f')
    (hx : x ∈ Set.Icc l r) (hy : y ∈ Set.Icc l r) :
    ‖f x - f y‖ ≤ ∫ z in Set.Ioc l r, ‖f' z‖ := by
  have hsub : uIoc y x ⊆ Set.Ioc l r := by
    intro z hz
    simp only [uIoc, Set.mem_Ioc] at hz
    exact ⟨(le_min hy.1 hx.1).trans_lt hz.1, hz.2.trans (max_le hy.2 hx.2)⟩
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hf z)
    (hcont.intervalIntegrable y x)]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  exact integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall fun z => norm_nonneg _)
    (hcont.norm.intervalIntegrable l r).1

private theorem point_le_interval_average {f f' : ℝ → ℂ} {l r x : ℝ}
    (hf : ∀ z, HasDerivAt f (f' z) z) (hcont : Continuous f')
    (hlr : l < r) (hx : x ∈ Set.Icc l r) :
    ‖f x‖ ≤ (∫ z in Set.Ioc l r, ‖f z‖) / (r-l) +
      ∫ z in Set.Ioc l r, ‖f' z‖ := by
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)
  let D : ℝ := ∫ z in Set.Ioc l r, ‖f' z‖
  have hpoint : ∀ z ∈ Set.Ioc l r, ‖f x‖ ≤ ‖f z‖ + D := by
    intro z hz
    calc
      ‖f x‖ = ‖(f x - f z) + f z‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f z‖ + ‖f z‖ := norm_add_le _ _
      _ ≤ D + ‖f z‖ := add_le_add_left
        (integrated_abs_difference_le hf hcont hx ⟨hz.1.le, hz.2⟩) _
      _ = _ := add_comm _ _
  have hI : IntegrableOn (fun z => ‖f z‖) (Set.Ioc l r) :=
    (hfc.norm.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hC (t : ℝ) : IntegrableOn (fun _ : ℝ => t) (Set.Ioc l r) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hi := setIntegral_mono_on (hC ‖f x‖) (hI.add (hC D)) measurableSet_Ioc hpoint
  change (∫ z in Set.Ioc l r, ‖f x‖) ≤ ∫ z in Set.Ioc l r, ‖f z‖ + D at hi
  rw [integral_add hI (hC D)] at hi
  simp only [setIntegral_const, smul_eq_mul,
    Real.volume_real_Ioc_of_le hlr.le] at hi
  change ‖f x‖ ≤ (∫ z in Set.Ioc l r, ‖f z‖) / (r-l) + D
  rw [← sub_le_iff_le_add, le_div_iff₀ (sub_pos.mpr hlr)]
  nlinarith only [hi]

private theorem sum_disjoint_interval_integrals_le {S : Finset ℕ} {l r : ℕ → ℝ} {J : Set ℝ}
    {F : ℝ → ℝ} (hF : IntegrableOn F J) (hn : ∀ x, 0 ≤ F x)
    (hsub : ∀ i ∈ S, Set.Ioc (l i) (r i) ⊆ J)
    (hdisj : Set.Pairwise (↑S : Set ℕ) (Disjoint on fun i => Set.Ioc (l i) (r i))) :
    ∑ i ∈ S, (∫ v in Set.Ioc (l i) (r i), F v) ≤ ∫ v in J, F v := by
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc) hdisj
    (fun i hi => hF.mono_set (hsub i hi))]
  apply integral_mono_measure (Measure.restrict_mono _ le_rfl) (Filter.Eventually.of_forall hn) hF
  exact Set.iUnion₂_subset hsub

private theorem separated_samples_le {S : Finset ℕ} {v : ℕ → ℝ} {f f' : ℝ → ℂ} {h c : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (hv : ∀ i ∈ S, v i ∈ Set.Icc (c-1/2) (c+1/2))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → h ≤ |v i - v j|)
    (hf : ∀ z, HasDerivAt f (f' z) z) (hcont : Continuous f') :
    ∑ i ∈ S, ‖f (v i)‖ ≤
      (∫ z in Set.Icc (c-1) (c+1), ‖f z‖) / h +
        ∫ z in Set.Icc (c-1) (c+1), ‖f' z‖ := by
  let l (i : ℕ) := v i - h/2
  let r (i : ℕ) := v i + h/2
  have hsub : ∀ i ∈ S, Set.Ioc (l i) (r i) ⊆ Set.Icc (c-1) (c+1) := by
    intro i hi z hz
    obtain ⟨hzl, hzr⟩ := hz
    dsimp [l, r] at hzl hzr
    exact ⟨by linarith only [(hv i hi).1, hzl, hh₁],
      by linarith only [(hv i hi).2, hzr, hh₁]⟩
  have hdisj : Set.Pairwise (↑S : Set ℕ) (Disjoint on fun i => Set.Ioc (l i) (r i)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hi' hj'
    rcases le_total (v i) (v j) with hvij | hvji
    · have hs := hsep i hi j hj hij
      rw [abs_of_nonpos (sub_nonpos.mpr hvij)] at hs
      have hi'' := hi'.2
      have hj'' := hj'.1
      dsimp [l, r] at hi'' hj''
      linarith only [hi'', hj'', hs]
    · have hs := hsep i hi j hj hij
      rw [abs_of_nonneg (sub_nonneg.mpr hvji)] at hs
      have hi'' := hi'.1
      have hj'' := hj'.2
      dsimp [l, r] at hi'' hj''
      linarith only [hi'', hj'', hs]
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)
  calc
    _ ≤ ∑ i ∈ S, ((∫ z in Set.Ioc (l i) (r i), ‖f z‖) / h +
        ∫ z in Set.Ioc (l i) (r i), ‖f' z‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hlr : l i < r i := by dsimp [l, r]; linarith
      have hv' : v i ∈ Set.Icc (l i) (r i) := ⟨by dsimp [l]; linarith, by dsimp [r]; linarith⟩
      have hlen : r i - l i = h := by dsimp [l, r]; ring
      simpa only [hlen] using point_le_interval_average hf hcont hlr hv' 
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      apply add_le_add
      · exact div_le_div_of_nonneg_right (sum_disjoint_interval_integrals_le
          (hfc.norm.continuousOn.integrableOn_compact isCompact_Icc)
          (fun z => norm_nonneg _) hsub hdisj) hh.le
      · exact sum_disjoint_interval_integrals_le
          (hcont.norm.continuousOn.integrableOn_compact isCompact_Icc)
          (fun z => norm_nonneg _) hsub hdisj

private theorem local_integral_norm_le_of_energy {f : ℝ → ℂ} (hf : Continuous f)
    {A c : ℝ} (hA : 0 < A)
    (hE : (∫ z in Set.Icc (c-1) (c+1), ‖f z‖^2) ≤ A^2) :
    (∫ z in Set.Icc (c-1) (c+1), ‖f z‖) ≤ 2*A := by
  let J := Set.Icc (c-1) (c+1)
  have hi : IntegrableOn (fun z => ‖f z‖) J :=
    hf.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun z => ‖f z‖^2) J :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hic : IntegrableOn (fun _ : ℝ => A^2) J :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on (hi.const_mul (2*A)) (hi2.add hic) measurableSet_Icc
    (fun z _ => (show 2*A*‖f z‖ ≤ ‖f z‖^2 + A^2 by
      nlinarith only [sq_nonneg (‖f z‖ - A)]))
  change (∫ z in J, 2*A*‖f z‖) ≤ (∫ z in J, ‖f z‖^2 + A^2) at hm
  rw [integral_const_mul, integral_add hi2 hic, setIntegral_const, smul_eq_mul] at hm
  have hvol : volume.real J = 2 := by
    dsimp [J]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hvol] at hm
  have hbound : 2*A * (∫ z in J, ‖f z‖) ≤ 2*A * (2*A) := by
    change (∫ z in J, ‖f z‖^2) ≤ A^2 at hE
    nlinarith only [hm, hE, sq_nonneg A]
  exact le_of_mul_le_mul_left hbound (by positivity)

def phaseDerivCoeff (γ : ℕ → ℝ) (a : ℕ → ℂ) (i : ℕ) : ℂ :=
  a i * (Complex.I * (γ i : ℂ))

private theorem finiteModes_hasDerivAt (S : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (v : ℝ) :
    HasDerivAt (finiteModes S γ a) (finiteModes S γ (phaseDerivCoeff γ a) v) v := by
  unfold finiteModes
  apply HasDerivAt.fun_sum
  intro i hi
  have hl : HasDerivAt (fun x : ℝ => Complex.I * (γ i : ℂ) * (x : ℂ))
      (Complex.I * (γ i : ℂ)) v := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (Complex.I * (γ i : ℂ))
  convert hl.cexp.const_mul (a i) using 1
  unfold phaseDerivCoeff
  ring

private theorem finiteModes_continuous (S : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) :
    Continuous (finiteModes S γ a) := by
  unfold finiteModes
  fun_prop

private theorem local_mode_energy_le_of_majorant (S : Finset ℕ) (γ : ℕ → ℝ)
    (a : ℕ → ℂ) (b : ℤ → ℝ)
    (hbs : Summable fun k => b k^2) {C c : ℝ}
    (hcoeff : ∀ k, binMass S γ a k ≤ C * b k) :
    (∫ v in Set.Icc (c-1) (c+1), ‖finiteModes S γ a v‖^2) ≤
      (Real.exp 1 * (‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * (∑' d : ℤ, binKernel d))) *
        (C^2 * ∑' k : ℤ, b k^2) := by
  let W := Real.exp 1 * (‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * (∑' d : ℤ, binKernel d))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _)
      (tsum_nonneg fun d => (Real.exp_pos _).le))
  apply (local_bin_energy_le S γ a c).trans
  apply mul_le_mul_of_nonneg_left _ hW
  calc
    _ ≤ ∑ k ∈ S.image (frequencyBin ∘ γ), C^2 * b k^2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun i hi => norm_nonneg _) (hcoeff k) 2
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hbs.sum_le_tsum _ (fun k _ => sq_nonneg _)) (sq_nonneg _)

theorem exists_local_mode_integral_le (b : ℤ → ℝ) (hbs : Summable fun k => b k ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : Finset ℕ) (γ : ℕ → ℝ) (a : ℕ → ℂ) (C : ℝ), 0 < C →
      (∀ k, binMass T γ a k ≤ C * b k) →
      ∀ c : ℝ, (∫ v in Set.Icc (c-1) (c+1), ‖finiteModes T γ a v‖) ≤ K * C := by
  let E := (Real.exp 1 * (‖((Real.pi : ℂ) ^ (1/2 : ℂ))‖ * (∑' d : ℤ, binKernel d))) *
    (∑' k : ℤ, b k^2)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _)
        (tsum_nonneg fun d => (Real.exp_pos _).le)))
      (tsum_nonneg fun k => sq_nonneg _)
  let A := 1 + Real.sqrt E
  have hA : 0 < A := by dsimp [A]; positivity
  have hAsq : E ≤ A^2 := by
    dsimp [A]
    nlinarith only [Real.sq_sqrt hE, Real.sqrt_nonneg E]
  refine ⟨2*A, by positivity, fun T γ a C hC hcoeff c => ?_⟩
  have henergy := local_mode_energy_le_of_majorant T γ a b hbs (c := c) hcoeff
  have henergy' : (∫ v in Set.Icc (c-1) (c+1), ‖finiteModes T γ a v‖^2) ≤ E * C^2 :=
    henergy.trans_eq (by dsimp [E]; ring)
  have hcontrol := henergy'.trans (mul_le_mul_of_nonneg_right hAsq (sq_nonneg C))
  rw [← mul_pow] at hcontrol
  exact (local_integral_norm_le_of_energy (finiteModes_continuous T γ a)
    (mul_pos hA hC) hcontrol).trans_eq (by ring)

theorem separated_mode_samples_le {T S : Finset ℕ} {γ v : ℕ → ℝ} {a : ℕ → ℂ}
    {h c U V : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hv : ∀ i ∈ S, v i ∈ Set.Icc (c-1/2) (c+1/2))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → h ≤ |v i - v j|)
    (hU : (∫ z in Set.Icc (c-1) (c+1), ‖finiteModes T γ a z‖) ≤ U)
    (hV : (∫ z in Set.Icc (c-1) (c+1), ‖finiteModes T γ (phaseDerivCoeff γ a) z‖) ≤ V) :
    ∑ i ∈ S, ‖finiteModes T γ a (v i)‖ ≤ U / h + V :=
  (separated_samples_le hh hh₁ hv hsep (finiteModes_hasDerivAt T γ a)
    (finiteModes_continuous T γ _)).trans
    (add_le_add (div_le_div_of_nonneg_right hU hh.le) hV)

private theorem norm_varying_sample_le {f : ℕ → ℝ → ℂ} {v : ℝ} {p n : ℕ}
    (hpn : p ≤ n) :
    ‖f n v‖ ≤ ‖f p v‖ + ∑ r ∈ Finset.Ico p n, ‖f (r+1) v - f r v‖ := by
  induction n, hpn using Nat.le_induction with
  | base => simp
  | succ n hpn ih =>
    rw [Finset.sum_Ico_succ_top hpn]
    calc
      ‖f (n+1) v‖ = ‖f (n+1) v - f n v + f n v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f (n+1) v - f n v‖ + ‖f n v‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add_right ih _ |>.trans_eq (by ac_rfl)

theorem varying_sample_sum_le {S : Finset ℕ} {f : ℕ → ℝ → ℂ} {v : ℕ → ℝ}
    {p q : ℕ} {A B : ℝ} (hq : ∀ n ∈ S, n ∈ Finset.Icc p q)
    (hbase : ∑ n ∈ S, ‖f p (v n)‖ ≤ A)
    (hdiff : ∀ r ∈ Finset.Ico p q, ∑ n ∈ S, ‖f (r+1) (v n) - f r (v n)‖ ≤ B) :
    ∑ n ∈ S, ‖f n (v n)‖ ≤ A + (Finset.Ico p q).card * B := by
  calc
    _ ≤ ∑ n ∈ S, (‖f p (v n)‖ +
        ∑ r ∈ Finset.Ico p q, ‖f (r+1) (v n) - f r (v n)‖) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hpn, hnq⟩ := Finset.mem_Icc.mp (hq n hn)
      apply (norm_varying_sample_le hpn).trans
      apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        have hr' := Finset.mem_Ico.mp hr
        exact Finset.mem_Ico.mpr ⟨hr'.1, hr'.2.trans_le hnq⟩
      · intro r hr hnot
        exact norm_nonneg _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      apply add_le_add hbase
      exact (Finset.sum_le_sum hdiff).trans_eq (by simp [nsmul_eq_mul])

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
