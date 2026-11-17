/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily strong finite-cell coercivity for the complete original positive kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The finite-cell condition concerns literal complex integrals of the inclusive
atomic prefix. No completed detail space or hat-function equivalence is used.
Finite-cell cancellation uniformly suppresses low-band spectral mass, giving
the original full-kernel inequality from the logarithmic multiplier bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open OriginalActualFourier

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

private lemma phase_sub_bound (w u v : ℝ) :
    ‖phase w u - phase w v‖ ≤ |w| * |u - v| := by
  have he : phase w u - phase w v = phase w v * (phase w (u-v) - 1) := by
    rw [mul_sub, mul_one, ← phase_add, show v + (u-v) = u by ring]
  rw [he, norm_mul, phase_norm, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := w * (u-v))
  have he' : phase w (u-v) = Complex.exp (Complex.I * ((w * (u-v) : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  simpa only [he', Real.norm_eq_abs, abs_mul] using h

private lemma cell_transform_bound (A : ℝ → ℂ) (hA : Integrable A)
    (l r w : ℝ) (hlr : l ≤ r) (hz : (∫ u in l..r, A u) = 0) :
    ‖∫ u in l..r, A u * phase (-w) u‖ ≤
      (|w| * (r-l)) * ∫ u in l..r, ‖A u‖ := by
  have he : (∫ u in l..r, A u * phase (-w) u) =
      ∫ u in l..r, A u * (phase (-w) u - phase (-w) l) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub
      ((transform_integrable hA w).intervalIntegrable)
      ((hA.mul_const _).intervalIntegrable), intervalIntegral.integral_mul_const, hz]
    simp
  rw [he, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hlr ?_
    ((hA.norm.const_mul _).intervalIntegrable)
  apply ae_of_all
  intro u hu
  have hu' : l ≤ u ∧ u ≤ r := ⟨hu.1.le, hu.2⟩
  have hp : ‖phase (-w) u - phase (-w) l‖ ≤ |w| * (r-l) := by
    calc
      _ ≤ |-w| * |u-l| := phase_sub_bound (-w) u l
      _ ≤ |w| * (r-l) := by
        rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hu'.1)]
        gcongr
        linarith [hu'.2]
  rw [norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (A u))]

private lemma cell_fourier_bound (A : ℝ → ℂ) (hA : Integrable A)
    (D h : ℝ) (n : ℕ) (hn : 0 < n) (hh : 0 < h) (hend : (n : ℝ) * h = D)
    (hs : ∀ u, u ∉ Icc 0 D → A u = 0)
    (hz : ∀ k < n, (∫ u in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, A u) = 0)
    (w : ℝ) : ‖Ahat A w‖ ≤ (|w| * h) * ∫ u, ‖A u‖ := by
  have hD : 0 ≤ D := by rw [← hend]; positivity
  have window (f : ℝ → ℂ) (hf : ∀ u, u ∉ Icc 0 D → f u = 0) :
      (∫ u, f u) = ∫ u in (0 : ℝ)..D, f u := by
    rw [intervalIntegral.integral_of_le hD, ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
  have hwindow : Ahat A w = ∫ u in (0 : ℝ)..D, A u * phase (-w) u :=
    window _ (fun u hu => by rw [hs u hu, zero_mul])
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * h) (n := n)
    (fun k _ => (transform_integrable hA w).intervalIntegrable)
  have hnrm := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u => ‖A u‖) (a := fun k : ℕ => (k : ℝ) * h) (n := n)
    (fun k _ => hA.norm.intervalIntegrable)
  simp only [Nat.cast_zero, zero_mul, hend] at hsum hnrm
  rw [hwindow, ← hsum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖∫ u in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h,
        A u * phase (-w) u‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (|w| * h) *
        ∫ u in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, ‖A u‖ := by
      apply Finset.sum_le_sum
      intro k hk
      have he : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
      simpa only [he] using cell_transform_bound A hA ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h)
        w (by push_cast; nlinarith) (hz k (Finset.mem_range.mp hk))
    _ = (|w| * h) * ∫ u, ‖A u‖ := by
      rw [← Finset.mul_sum, hnrm, intervalIntegral.integral_of_le hD,
        ← integral_Icc_eq_integral_Ioc,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro u hu
      simp [hs u hu]

private lemma window_l1_sq (A : ℝ → ℂ) (_hA : Integrable A)
    (hA2 : MemLp A 2) (D : ℝ) (hD : 0 < D)
    (hs : ∀ u, u ∉ Icc 0 D → A u = 0) :
    (∫ u, ‖A u‖)^2 ≤ D * ∫ u, ‖A u‖^2 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 D)
  have he1 : (∫ u, ‖A u‖ ∂μ) = ∫ u, ‖A u‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hs u hu])
  have he2 : (∫ u, ‖A u‖^2 ∂μ) = ∫ u, ‖A u‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hs u hu])
  have hv : μ.real univ = D := by simp [μ, hD.le]
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) Real.HolderConjugate.two_two
    (f := fun u => ‖A u‖) (g := fun _ : ℝ => (1 : ℝ))
    (by simpa using hA2.norm.restrict (s := Icc 0 D))
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ))
  simp only [Real.norm_eq_abs, abs_norm, norm_one, mul_one,
    Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    ← Real.sqrt_eq_rpow, he1, he2, hv] at h
  have hE : 0 ≤ ∫ u, ‖A u‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hL : 0 ≤ ∫ u, ‖A u‖ := integral_nonneg (fun _ => norm_nonneg _)
  have he := mul_self_le_mul_self hL h
  simpa only [← pow_two, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hD.le, mul_comm] using he

private lemma actual_mass {I : Type*} [Fintype I]
    (D : ℝ) (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (hx : ∀ i, x i ≤ D) :
    (∫ _ξ, (1 : ℝ) ∂rho («prefix» x a)) = energy x a := by
  let A := «prefix» x a
  have hA := (prefix_L1_L2 x a ha D hx).1
  have hAq := (prefix_L1_L2 x a ha D hx).2
  have hA2 : MemLp A 2 :=
    (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mpr hAq
  have hh : Ahat A = ZetaGamma.FormCore.LineFourier.angularFourier A := by
    funext w
    rw [ZetaGamma.FormCore.LineFourier.angularFourier_eq_integral]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    change A u * phase (-w) u = Complex.exp ((-(w*u) : ℝ)*Complex.I) * A u
    have hp : phase (-w) u = Complex.exp ((-(w*u) : ℝ)*Complex.I) := by
      unfold phase
      congr 1
      push_cast
      ring
    rw [hp, mul_comm]
  have he (f : ℝ → ℂ) (hf : Integrable (fun u => ‖f u‖^2)) :
      (∫⁻ u, ‖f u‖ₑ^2) = ENNReal.ofReal (∫ u, ‖f u‖^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ (fun _ => sq_nonneg _))]
    apply lintegral_congr_ae
    exact ae_of_all _ fun u => by
      dsimp only
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hp := ZetaGamma.FormCore.LineFourier.angular_extended_plancherel hA hA2
  rw [he A hAq, ← hh, he (Ahat A) (normSq_Ahat_integrable x a ha D hx)] at hp
  have hr := congrArg ENNReal.toReal hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1/(2*Real.pi))] at hr
  rw [rho, integral_withDensity_eq_integral_toReal_smul
    ((density_continuous hA).measurable.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (density_nonneg _ _), smul_eq_mul, mul_one]
  unfold density
  rw [integral_div]
  change (∫ ξ, ‖Ahat A ξ‖^2) / (2*Real.pi) = ∫ u, ‖A u‖^2
  rw [hr]
  ring

private lemma low_band_mass {I : Type*} [Fintype I]
    (D h R : ℝ) (hD : 0 < D) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (hh : 0 < h) (hend : (n : ℝ) * h = D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc 0 D) (ha : ∑ i, a i = 0)
    (hz : ∀ k < n, (∫ u in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, «prefix» x a u) = 0) :
    (∫ _ξ in Icc (-R) R, (1 : ℝ) ∂rho («prefix» x a)) ≤
      (D * R^3 / Real.pi * h^2) * energy x a := by
  let A := «prefix» x a
  have hA := (prefix_L1_L2 x a ha D (fun i => (hx i).2)).1
  have hAq := (prefix_L1_L2 x a ha D (fun i => (hx i).2)).2
  have hA2 : MemLp A 2 :=
    (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mpr hAq
  have hL := window_l1_sq A hA hA2 D hD (prefix_zero_off_window x a ha hx)
  have hb (ξ : ℝ) (hξ : ξ ∈ Icc (-R) R) :
      density A ξ ≤ R^2 * h^2 * D * energy x a / (2*Real.pi) := by
    have hf := cell_fourier_bound A hA D h n hn hh hend
      (prefix_zero_off_window x a ha hx) hz ξ
    have hξR : |ξ| ≤ R := abs_le.mpr hξ
    have hL0 : 0 ≤ ∫ u, ‖A u‖ := integral_nonneg (fun _ => norm_nonneg _)
    have hf' : ‖Ahat A ξ‖ ≤ (R*h) * ∫ u, ‖A u‖ :=
      hf.trans (by gcongr)
    have hsq := mul_self_le_mul_self (norm_nonneg _) hf'
    have hLL := mul_le_mul_of_nonneg_left hL (sq_nonneg (R*h))
    dsimp only [density]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp only [energy] at *
    nlinarith only [hsq, hLL]
  rw [rho, restrict_withDensity measurableSet_Icc,
    integral_withDensity_eq_integral_toReal_smul
      ((density_continuous hA).measurable.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (density_nonneg _ _), smul_eq_mul, mul_one]
  calc
    _ ≤ ∫ _ξ in Icc (-R) R, R^2*h^2*D*energy x a/(2*Real.pi) := by
      apply setIntegral_mono_on
        (((normSq_Ahat_integrable x a ha D (fun i => (hx i).2)).div_const _).integrableOn)
        (integrableOn_const (by simp [Real.volume_Icc])) measurableSet_Icc hb
    _ = _ := by
      rw [integral_const]
      simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_real_Icc, sub_neg_eq_add]
      rw [max_eq_left (by linarith : 0 ≤ R+R), smul_eq_mul]
      field_simp; ring

universe u

/-- A strict finite grid, chosen before the arbitrary finite atomic family,
forces the literal original positive-kernel energy above any positive multiple
of the entire inclusive-prefix L2 energy. -/
theorem original_coarse_cell_coercivity (D β : ℝ) (hD : 0 < D) (hβ : 0 < β) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ g : ℕ → ℝ,
      g 0 = 0 ∧ g N = D ∧ StrictMono g ∧
      ∀ (I : Type u) (_ : Fintype I) (x : I → ℝ) (a : I → ℂ),
        (∀ i, x i ∈ Icc 0 D) → (∑ i, a i = 0) →
        (∀ k < N, (∫ u in g k..g (k + 1), «prefix» x a u) = 0) →
        β * (∫ u : ℝ, ‖«prefix» x a u‖^2) ≤ (quadratic x a P).re := by
  let R : ℝ := Real.exp (2*β + Real.log 13/2) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have htail (ξ : ℝ) (hξ : ξ ∉ Icc (-R) R) : 2*β ≤ pMultiplier ξ := by
    have hξR : R < |ξ| := lt_of_not_ge (fun h => hξ (abs_le.mp h))
    have hr : Real.exp (2*β+Real.log 13/2) ≤ 2+|ξ| := by dsimp [R] at hξR; linarith
    have hl := Real.log_le_log (Real.exp_pos _) hr
    rw [Real.log_exp] at hl
    linarith [(pMultiplier_logarithmic_bounds ξ).2.2.2.1]
  have ht : Tendsto (fun n : ℕ => D*R^3/Real.pi * (D/(n : ℝ))^2) atTop (𝓝 0) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat D).pow 2).const_mul
      (D*R^3/Real.pi)
  obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2))).exists
  have hN0 : 0 < N := by omega
  let h : ℝ := D / N
  have hh : 0 < h := div_pos hD (by exact_mod_cast hN0)
  have hend : (N : ℝ) * h = D := by dsimp [h]; field_simp
  refine ⟨N, hN, (fun k => (k : ℝ) * h), by simp, hend, ?_, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hh
  intro I inst x a hx ha hz
  let A := «prefix» x a
  let μ := rho A
  let B := Icc (-R) R
  haveI : IsFiniteMeasure μ := actual_rho_finite x a ha D (fun i => (hx i).2)
  have hspec := complete_positive_mixture_spectral_identity D hD.le x a hx ha
  have hmass := actual_mass D x a ha (fun i => (hx i).2)
  have hlow := low_band_mass D h R hD hR N hN0 hh hend x a hx ha hz
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  have hhalf : (∫ ξ in B, (1 : ℝ) ∂μ) ≤ energy x a / 2 := by
    exact hlow.trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall.le hE])
  have hi : Integrable (B.indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const _).indicator measurableSet_Icc
  have hbound : 2*β * (energy x a - ∫ ξ in B, (1 : ℝ) ∂μ) ≤
      ∫ ξ, pMultiplier ξ ∂μ := by
    calc
      _ = ∫ ξ, 2*β * ((1 : ℝ) - B.indicator (fun _ => (1 : ℝ)) ξ) ∂μ := by
        rw [integral_const_mul, integral_sub (integrable_const _) hi,
          integral_indicator measurableSet_Icc, hmass]
      _ ≤ _ := by
        apply integral_mono (((integrable_const (1 : ℝ)).sub hi).const_mul _) hspec.1
        intro ξ
        change 2*β * (1 - B.indicator (fun _ : ℝ => (1 : ℝ)) ξ) ≤ pMultiplier ξ
        by_cases hξ : ξ ∈ B
        · simp only [indicator_of_mem hξ, sub_self, mul_zero]
          exact (pMultiplier_logarithmic_bounds ξ).2.1
        · simp only [indicator_of_notMem hξ, sub_zero, mul_one]
          exact htail ξ hξ
  rw [← hspec.2] at hbound
  change β * energy x a ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hhalf hβ.le]

#print axioms original_coarse_cell_coercivity

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
