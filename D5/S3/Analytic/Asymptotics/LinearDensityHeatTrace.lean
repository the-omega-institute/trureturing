/- GID: D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/LinearDensityHeatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear spectral density gives a heat trace with a bounded leading-term residual. -/

/- Library-search audit trail (2026-08-28):
* Repository searches found no existing generic counting-density-to-heat-trace theorem.
  UniversalHeatTrace defines the exponential tsum, but only proves convergence thresholds.
* Pinned Mathlib provides `Real.integral_rpow_mul_exp_neg_mul_Ioi`,
  `Real.integrableOn_exp_mul_Ioi`, `MeasureTheory.lintegral_tsum`, and
  `Asymptotics.IsBigO.of_bound`; these are reused below.
* Loogle, LeanSearch, Reservoir, and GitHub searches found no exact third-party theorem.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter
open MeasureTheory
open scoped ENNReal Topology

namespace D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace

noncomputable section

/-- The number of spectral values at most `u`. The finiteness premise in the theorem makes
`Set.ncard` the genuine cardinality rather than its junk value on infinite sets. -/
def spectralCounting (lambda : ℕ → ℝ) (u : ℝ) : ℝ :=
  Set.ncard {n | lambda n ≤ u}

/-- The heat trace of a real spectrum. -/
def spectralHeatTrace (lambda : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-t * lambda n)

private lemma spectralCounting_monotone (lambda : ℕ → ℝ)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u}) :
    Monotone (spectralCounting lambda) := by
  intro u v huv
  dsimp only [spectralCounting]
  exact_mod_cast Set.ncard_le_ncard (by
    rintro n hn
    exact hn.trans huv) (hfinite v)

private lemma spectralCounting_nonneg (lambda : ℕ → ℝ) (u : ℝ) :
    0 ≤ spectralCounting lambda u := by
  unfold spectralCounting
  positivity

private lemma counting_residual_bounded_on_Ioi (lambda : ℕ → ℝ) (c : ℝ)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Set.Ioi (0 : ℝ),
      ‖spectralCounting lambda u - c * u‖ ≤ K := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdensity
  simp only [norm_one, mul_one] at hC
  obtain ⟨U, hU⟩ := (eventually_atTop.1 hC)
  let U0 : ℝ := max U 1
  let K : ℝ := max C (spectralCounting lambda U0 + |c| * U0)
  have hU0_pos : 0 < U0 := lt_of_lt_of_le zero_lt_one (le_max_right U 1)
  have htail : ∀ u, U0 ≤ u → ‖spectralCounting lambda u - c * u‖ ≤ C := by
    intro u hu
    exact hU u ((le_max_left U 1).trans hu)
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (norm_nonneg (spectralCounting lambda U0 - c * U0)) (htail U0 le_rfl)
  refine ⟨K, hC_nonneg.trans (le_max_left _ _), ?_⟩
  intro u hu
  by_cases hUu : U0 ≤ u
  · exact (htail u hUu).trans (le_max_left _ _)
  · have huU0 : u ≤ U0 := le_of_not_ge hUu
    have hcount : spectralCounting lambda u ≤ spectralCounting lambda U0 :=
      spectralCounting_monotone lambda hfinite huU0
    have hu_nonneg : 0 ≤ u := hu.le
    calc
      ‖spectralCounting lambda u - c * u‖
          ≤ spectralCounting lambda u + |c| * u := by
            rw [Real.norm_eq_abs]
            calc
              |spectralCounting lambda u - c * u|
                  ≤ |spectralCounting lambda u| + |c * u| := abs_sub _ _
              _ = spectralCounting lambda u + |c| * u := by
                rw [abs_of_nonneg (spectralCounting_nonneg lambda u), abs_mul,
                  abs_of_nonneg hu_nonneg]
      _ ≤ spectralCounting lambda U0 + |c| * U0 := by gcongr
      _ ≤ K := le_max_right _ _

private lemma counting_residual_mul_exp_integrable (lambda : ℕ → ℝ) (c K t : ℝ)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u}) (ht : 0 < t)
    (hK : ∀ u ∈ Set.Ioi (0 : ℝ), ‖spectralCounting lambda u - c * u‖ ≤ K) :
    IntegrableOn
      (fun u => (spectralCounting lambda u - c * u) * Real.exp (-(t * u)))
      (Set.Ioi (0 : ℝ)) := by
  have hexp : Integrable (fun u : ℝ => Real.exp (-t * u))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0).integrable
  have hdom : Integrable (fun u : ℝ => K * Real.exp (-(t * u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [neg_mul] using Integrable.const_mul hexp K
  have hK_nonneg : 0 ≤ K := by
    have hone := hK 1 (by simp)
    simp only [mul_one] at hone
    exact (norm_nonneg (spectralCounting lambda 1 - c)).trans hone
  have hmeas : AEStronglyMeasurable
      (fun u => (spectralCounting lambda u - c * u) * Real.exp (-(t * u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (((spectralCounting_monotone lambda hfinite).measurable.sub
      (measurable_const.mul measurable_id)).mul
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_id).neg)).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg hK_nonneg] using
      mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hK u hu)
        (Real.exp_nonneg _)

private lemma linear_mul_exp_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(t * u))) (Set.Ioi (0 : ℝ)) := by
  exact .of_integral_ne_zero (by
    have hformula :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ht
    have heq : (∫ u : ℝ in Set.Ioi 0, u * Real.exp (-(t * u))) =
        (1 / t) ^ (2 : ℝ) * Real.Gamma 2 := by
      convert hformula using 1
      · congr 1
        funext u
        norm_num [Real.rpow_one]
    rw [heq]
    positivity)

private lemma counting_mul_exp_integrable (lambda : ℕ → ℝ) (c K t : ℝ)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u}) (ht : 0 < t)
    (hK : ∀ u ∈ Set.Ioi (0 : ℝ), ‖spectralCounting lambda u - c * u‖ ≤ K) :
    IntegrableOn (fun u => spectralCounting lambda u * Real.exp (-(t * u)))
      (Set.Ioi (0 : ℝ)) := by
  have hmain : Integrable (fun u => c * (u * Real.exp (-(t * u))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (linear_mul_exp_integrable t ht) c
  have herr : Integrable
      (fun u => (spectralCounting lambda u - c * u) * Real.exp (-(t * u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (counting_residual_mul_exp_integrable lambda c K t hfinite ht hK).integrable
  change Integrable _ (volume.restrict (Set.Ioi (0 : ℝ)))
  exact Integrable.congr (Integrable.add hmain herr) (by
    filter_upwards with u
    change c * (u * Real.exp (-(t * u))) +
      (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) = _
    ring)

private def heatLayer (lambda : ℕ → ℝ) (t : ℝ) (n : ℕ) (u : ℝ) : ℝ≥0∞ :=
  (Set.Ici (lambda n)).indicator
    (fun v => ENNReal.ofReal (t * Real.exp (-(t * v)))) u

private lemma heatLayer_aemeasurable (lambda : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    AEMeasurable (heatLayer lambda t n) volume := by
  apply Measurable.aemeasurable
  unfold heatLayer
  apply Measurable.indicator
  · fun_prop
  · exact measurableSet_Ici

private lemma lintegral_heatLayer (lambda : ℕ → ℝ) (t : ℝ) (n : ℕ) (ht : 0 < t) :
    ∫⁻ u : ℝ, heatLayer lambda t n u =
      ENNReal.ofReal (Real.exp (-t * lambda n)) := by
  have hexpIoi : IntegrableOn (fun u : ℝ => Real.exp (-t * u))
      (Set.Ioi (lambda n)) := by
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -t) (by linarith) (lambda n)
  have hexpIci : IntegrableOn (fun u : ℝ => Real.exp (-t * u))
      (Set.Ici (lambda n)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hexpIoi
  have hkernel : Integrable (fun u : ℝ => t * Real.exp (-(t * u)))
      (volume.restrict (Set.Ici (lambda n))) := by
    simpa only [neg_mul] using Integrable.const_mul hexpIci.integrable t
  have hkernel_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ici (lambda n))]
        (fun u : ℝ => t * Real.exp (-(t * u))) :=
    Eventually.of_forall fun _ => mul_nonneg ht.le (Real.exp_nonneg _)
  change (∫⁻ u : ℝ, (Set.Ici (lambda n)).indicator
    (fun v => ENNReal.ofReal (t * Real.exp (-(t * v)))) u) = _
  rw [lintegral_indicator measurableSet_Ici]
  rw [← ofReal_integral_eq_lintegral_ofReal hkernel hkernel_nonneg]
  apply congr_arg ENNReal.ofReal
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi]
  have hexp := integral_exp_mul_Ioi (a := -t) (by linarith) (lambda n)
  rw [show (∫ u : ℝ in Set.Ioi (lambda n), Real.exp (-(t * u))) =
      -Real.exp (-t * lambda n) / -t by simpa only [neg_mul] using hexp]
  field_simp

private lemma tsum_heatLayer (lambda : ℕ → ℝ) (t u : ℝ)
    (hfinite : Set.Finite {n | lambda n ≤ u}) (ht : 0 ≤ t) :
    ∑' n : ℕ, heatLayer lambda t n u =
      ENNReal.ofReal (t * spectralCounting lambda u * Real.exp (-(t * u))) := by
  let s : Set ℕ := {n | lambda n ≤ u}
  let a : ℝ≥0∞ := ENNReal.ofReal (t * Real.exp (-(t * u)))
  calc
    ∑' n : ℕ, heatLayer lambda t n u = ∑' n : ℕ, s.indicator (fun _ => a) n := by
      apply tsum_congr
      intro n
      by_cases hn : lambda n ≤ u <;> simp [heatLayer, s, a, hn]
    _ = ∑' _n : s, a := (tsum_subtype s (fun _ => a)).symm
    _ = s.encard * a := ENNReal.tsum_set_const s a
    _ = ENNReal.ofReal (t * spectralCounting lambda u * Real.exp (-(t * u))) := by
      rw [show s.encard = s.ncard by exact hfinite.cast_ncard_eq.symm]
      simp only [s, a, spectralCounting]
      calc
        (Set.ncard {n | lambda n ≤ u} : ℝ≥0∞) *
              ENNReal.ofReal (t * Real.exp (-(t * u))) =
            (Set.ncard {n | lambda n ≤ u} : ℝ≥0∞) *
              (ENNReal.ofReal t * ENNReal.ofReal (Real.exp (-(t * u)))) := by
                rw [ENNReal.ofReal_mul ht]
        _ = (ENNReal.ofReal t * ENNReal.ofReal
              (Set.ncard {n | lambda n ≤ u} : ℝ)) *
              ENNReal.ofReal (Real.exp (-(t * u))) := by
                rw [ENNReal.ofReal_natCast]
                ac_rfl
        _ = ENNReal.ofReal (t * (Set.ncard {n | lambda n ≤ u} : ℝ)) *
              ENNReal.ofReal (Real.exp (-(t * u))) := by
                rw [ENNReal.ofReal_mul ht]
        _ = ENNReal.ofReal
              ((t * (Set.ncard {n | lambda n ≤ u} : ℝ)) * Real.exp (-(t * u))) := by
                rw [ENNReal.ofReal_mul (mul_nonneg ht (Nat.cast_nonneg _))]

private lemma spectralCounting_eq_zero_of_nonpos (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) {u : ℝ} (hu : u ≤ 0) :
    spectralCounting lambda u = 0 := by
  have hempty : {n | lambda n ≤ u} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt (hu.trans_lt (hpos n))
  simp [spectralCounting, hempty]

private lemma heatTrace_eq_laplaceCounting (lambda : ℕ → ℝ) (c K t : ℝ)
    (hpos : ∀ n, 0 < lambda n)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u}) (ht : 0 < t)
    (hK : ∀ u ∈ Set.Ioi (0 : ℝ), ‖spectralCounting lambda u - c * u‖ ≤ K) :
    spectralHeatTrace lambda t =
      t * ∫ u : ℝ in Set.Ioi 0,
        spectralCounting lambda u * Real.exp (-(t * u)) := by
  let g : ℝ → ℝ := fun u =>
    t * spectralCounting lambda u * Real.exp (-(t * u))
  have hgOn : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    have hN := counting_mul_exp_integrable lambda c K t hfinite ht hK
    change Integrable g (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa only [g, mul_assoc] using Integrable.const_mul hN.integrable t
  have hg_zero : ∀ u, u ∉ Set.Ioi (0 : ℝ) → g u = 0 := by
    intro u hu
    have hu0 : u ≤ 0 := le_of_not_gt hu
    simp [g, spectralCounting_eq_zero_of_nonpos lambda hpos hu0]
  have hg : Integrable g volume := hgOn.integrable_of_forall_notMem_eq_zero hg_zero
  have hg_nonneg : 0 ≤ᵐ[volume] g := Eventually.of_forall fun u => by
    exact mul_nonneg (mul_nonneg ht.le (spectralCounting_nonneg lambda u))
      (Real.exp_nonneg _)
  have hTonelli := lintegral_tsum (fun n => heatLayer_aemeasurable lambda t n)
  have hENN : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-t * lambda n))) =
      ∫⁻ u : ℝ, ENNReal.ofReal (g u) := by
    calc
      (∑' n : ℕ, ENNReal.ofReal (Real.exp (-t * lambda n))) =
          ∑' n : ℕ, ∫⁻ u : ℝ, heatLayer lambda t n u := by
            apply tsum_congr
            intro n
            exact (lintegral_heatLayer lambda t n ht).symm
      _ = ∫⁻ u : ℝ, ∑' n : ℕ, heatLayer lambda t n u := hTonelli.symm
      _ = ∫⁻ u : ℝ, ENNReal.ofReal (g u) := by
        apply lintegral_congr
        intro u
        exact tsum_heatLayer lambda t u (hfinite u) ht.le
  have hright_ne_top : (∫⁻ u : ℝ, ENNReal.ofReal (g u)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg hg_nonneg]
    exact ENNReal.ofReal_ne_top
  have hleft_ne_top : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-t * lambda n))) ≠ ∞ := by
    rwa [hENN]
  have hsum : Summable (fun n : ℕ => Real.exp (-t * lambda n)) := by
    have hsumToReal := ENNReal.summable_toReal hleft_ne_top
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hsumToReal
  have hreal : spectralHeatTrace lambda t = ∫ u : ℝ, g u := by
    apply (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => Real.exp_nonneg _)
      (integral_nonneg_of_ae hg_nonneg)).mp
    calc
      ENNReal.ofReal (spectralHeatTrace lambda t) =
          ∑' n : ℕ, ENNReal.ofReal (Real.exp (-t * lambda n)) := by
            exact ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.exp_nonneg _) hsum
      _ = ∫⁻ u : ℝ, ENNReal.ofReal (g u) := hENN
      _ = ENNReal.ofReal (∫ u : ℝ, g u) :=
        (ofReal_integral_eq_lintegral_ofReal hg hg_nonneg).symm
  rw [hreal]
  have g_eq : g = (Set.Ioi (0 : ℝ)).indicator g := by
    funext u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · simp [hu]
    · simp [hu, hg_zero u hu]
  rw [g_eq, integral_indicator measurableSet_Ioi]
  simp only [g]
  simpa only [mul_assoc] using
    (integral_const_mul (μ := volume.restrict (Set.Ioi (0 : ℝ))) t
      (fun u : ℝ => spectralCounting lambda u * Real.exp (-(t * u))))

private lemma integral_linear_mul_exp (t : ℝ) (ht : 0 < t) :
    (∫ u : ℝ in Set.Ioi 0, u * Real.exp (-(t * u))) = 1 / t ^ 2 := by
  have hformula :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ht
  calc
    (∫ u : ℝ in Set.Ioi 0, u * Real.exp (-(t * u))) =
        (∫ u : ℝ in Set.Ioi 0, u ^ ((2 : ℝ) - 1) * Real.exp (-(t * u))) := by
          congr 1
          funext u
          norm_num [Real.rpow_one]
    _ = (1 / t) ^ (2 : ℝ) * Real.Gamma 2 := hformula
    _ = 1 / t ^ 2 := by
      have hGamma : Real.Gamma 2 = 1 := by
        convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
      rw [Real.rpow_two, hGamma]
      ring

private lemma heatTrace_residual_eq_integral (lambda : ℕ → ℝ) (c K t : ℝ)
    (hpos : ∀ n, 0 < lambda n)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u}) (ht : 0 < t)
    (hK : ∀ u ∈ Set.Ioi (0 : ℝ), ‖spectralCounting lambda u - c * u‖ ≤ K) :
    spectralHeatTrace lambda t - c / t =
      t * ∫ u : ℝ in Set.Ioi 0,
        (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) := by
  have hbridge := heatTrace_eq_laplaceCounting lambda c K t hpos hfinite ht hK
  have hmain : Integrable
      (fun u : ℝ => c * (u * Real.exp (-(t * u))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.const_mul (linear_mul_exp_integrable t ht).integrable c
  have herr : Integrable
      (fun u => (spectralCounting lambda u - c * u) * Real.exp (-(t * u)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (counting_residual_mul_exp_integrable lambda c K t hfinite ht hK).integrable
  have hdecomp :
      (∫ u : ℝ in Set.Ioi 0, spectralCounting lambda u * Real.exp (-(t * u))) =
        c * (∫ u : ℝ in Set.Ioi 0, u * Real.exp (-(t * u))) +
          ∫ u : ℝ in Set.Ioi 0,
            (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) := by
    calc
      (∫ u : ℝ in Set.Ioi 0, spectralCounting lambda u * Real.exp (-(t * u))) =
          ∫ u : ℝ in Set.Ioi 0,
            c * (u * Real.exp (-(t * u))) +
              (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) := by
                apply integral_congr_ae
                filter_upwards with u
                ring
      _ = (∫ u : ℝ in Set.Ioi 0, c * (u * Real.exp (-(t * u)))) +
            ∫ u : ℝ in Set.Ioi 0,
              (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) :=
          integral_add hmain herr
      _ = c * (∫ u : ℝ in Set.Ioi 0, u * Real.exp (-(t * u))) +
            ∫ u : ℝ in Set.Ioi 0,
              (spectralCounting lambda u - c * u) * Real.exp (-(t * u)) := by
                rw [integral_const_mul]
  rw [hbridge, hdecomp, integral_linear_mul_exp t ht]
  field_simp
  ring

private lemma heatTrace_residual_norm_le (lambda : ℕ → ℝ) (c K t : ℝ) (ht : 0 < t)
    (hK : ∀ u ∈ Set.Ioi (0 : ℝ), ‖spectralCounting lambda u - c * u‖ ≤ K) :
    ‖t * ∫ u : ℝ in Set.Ioi 0,
      (spectralCounting lambda u - c * u) * Real.exp (-(t * u))‖ ≤ K := by
  let residualKernel : ℝ → ℝ := fun u =>
    (spectralCounting lambda u - c * u) * Real.exp (-(t * u))
  let dominator : ℝ → ℝ := fun u => K * Real.exp (-(t * u))
  have hdom : Integrable dominator (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hexp := integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
    change Integrable dominator (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa only [dominator, neg_mul] using Integrable.const_mul hexp.integrable K
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖residualKernel u‖ ≤ dominator u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [residualKernel, dominator, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hK u hu) (Real.exp_nonneg _)
  have hnorm : ‖∫ u : ℝ in Set.Ioi 0, residualKernel u‖ ≤
      ∫ u : ℝ in Set.Ioi 0, dominator u :=
    norm_integral_le_of_norm_le hdom hpoint
  have hdomIntegral : (∫ u : ℝ in Set.Ioi 0, dominator u) = K / t := by
    simp only [dominator]
    rw [integral_const_mul]
    have hexp := integral_exp_mul_Ioi (a := -t) (by linarith) 0
    have hexp' : (∫ u : ℝ in Set.Ioi 0, Real.exp (-(t * u))) = 1 / t := by
      calc
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-(t * u))) =
            -Real.exp (-(t * 0)) / -t := by simpa only [neg_mul] using hexp
        _ = 1 / t := by
          rw [mul_zero, neg_zero, Real.exp_zero]
          field_simp
    rw [hexp']
    ring
  have hnorm' : ‖∫ u : ℝ in Set.Ioi 0,
      (spectralCounting lambda u - c * u) * Real.exp (-(t * u))‖ ≤ K / t := by
    simpa only [residualKernel, hdomIntegral] using hnorm
  calc
    ‖t * ∫ u : ℝ in Set.Ioi 0,
        (spectralCounting lambda u - c * u) * Real.exp (-(t * u))‖ =
      t * ‖∫ u : ℝ in Set.Ioi 0,
        (spectralCounting lambda u - c * u) * Real.exp (-(t * u))‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ t * (K / t) := mul_le_mul_of_nonneg_left hnorm' ht.le
    _ = K := by field_simp

/-- If a positive strictly increasing spectrum has finite counting sets and counting function
`N(u) = c*u + O(1)` at infinity, then its exponential heat trace is `c/t + O(1)` as `t`
decreases to zero through positive values. -/
theorem linear_density_heat_trace (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    (fun t => spectralHeatTrace lambda t - c / t) =O[𝓝[>] 0]
      (fun _ => (1 : ℝ)) := by
  have _hstrict := hstrict
  obtain ⟨K, _, hK⟩ :=
    counting_residual_bounded_on_Ioi lambda c hfinite hdensity
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [norm_one, mul_one]
  rw [heatTrace_residual_eq_integral lambda c K t hpos hfinite ht hK]
  exact heatTrace_residual_norm_le lambda c K t ht hK

/-- Reverse fidelity probe: the public theorem implies that the heat-trace residual is
eventually uniformly bounded as positive `t` tends to zero. -/
example (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖spectralHeatTrace lambda t - c / t‖ ≤ K := by
  obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp
    (linear_density_heat_trace lambda c hpos hstrict hfinite hdensity)
  exact ⟨K, by simpa only [norm_one, mul_one] using hK⟩

end

end D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
