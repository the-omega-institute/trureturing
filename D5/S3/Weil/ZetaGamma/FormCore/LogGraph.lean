/- GID: D5/S3/Weil/ZetaGamma/FormCore/LogGraph
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/LogGraph
   mirror-E: none(waiver:analytic-Gamma-log-graph)
   anchors: []
   utility: none
   digest: Exact extended Gamma jump/log graph estimates on the original complex Ioc domain. -/

import D5.S3.Weil.ZetaGamma.FormCore.SmoothCore
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.GammaStirlingVert
import D5.S3.Weil.ZetaGamma.LogarithmicFormContinuity
import D5.S3.Weil.ZetaCore.PaperFT

/-!
All mass and graph estimates are first in ENNReal. Ordinary integrals below have
explicit finiteness guards. The spatial function is complex and unrestricted by
parity. `paperFT` uses PLUS: reflection of frequency, never conjugation of input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform ComplexConjugate

namespace D5.S3.Weil.ZetaGamma.FormCore.LogGraph

open D5.S3.Weil.ZetaGamma

def d0 : ℝ := (Complex.digamma (1 / 4)).re
def ell (t : ℝ) : ℝ := Real.log (|t| + 3)
def C1 : ℝ := |d0| + 5 + Real.log 5
def C2 : ℝ := 6 + |d0|

/-- The extended PLUS log Fourier square integral; no finiteness is built in. -/
def logFourierMass (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (ell t) * ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2

private abbrev delta := LineFourier.actualIncrement
private abbrev kappa : ℝ := 1 / (2 * Real.pi)
private abbrev kappaE : ℝ≥0∞ := ENNReal.ofReal kappa

private theorem ell_continuous : Continuous ell := by
  unfold ell
  exact (continuous_abs.add continuous_const).log (fun t => by
    change |t| + 3 ≠ 0
    have := abs_nonneg t
    linarith)

private theorem ell_ge_one (t : ℝ) : 1 ≤ ell t := by
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    convert Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> norm_num
  exact h3.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))

private theorem ell_nonneg (t : ℝ) : 0 ≤ ell t := (by norm_num : (0 : ℝ) ≤ 1).trans (ell_ge_one t)
private theorem C1_ge_one : 1 ≤ C1 := by
  dsimp [C1]
  linarith [abs_nonneg d0, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)]
private theorem C2_nonneg : 0 ≤ C2 := by unfold C2; positivity
private theorem kappa_pos : 0 < kappa := by unfold kappa; positivity

private theorem delta_nonneg (t : ℝ) : 0 ≤ delta t :=
  ArchimedeanJumpDecomposition.digamma_increment_nonnegative t

theorem delta_eq_mu (t : ℝ) :
    delta t = 2 * Real.pi * Zeta23.mu t + Real.log Real.pi - d0 := by
  have harg : (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) =
      (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2 := by push_cast; ring
  dsimp [delta, LineFourier.actualIncrement, Zeta23.mu, d0]
  rw [harg]
  field_simp [Real.pi_ne_zero]
  ring

private theorem delta_even (t : ℝ) : delta (-t) = delta t := by
  rw [delta_eq_mu, delta_eq_mu, Zeta23.mu_even]

private theorem stirling_scaled {t : ℝ} (ht : 2 ≤ |t|) :
    |(Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
      Real.log (|t| / 2)| ≤ 5 := by
  have hv : 1 / 2 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling'
    (a := 1 / 4) (by norm_num) (by norm_num) hv
  have hv2 : 1 ≤ (t / 2) ^ 2 := by
    have hsq : (2 : ℝ) ^ 2 ≤ |t| ^ 2 :=
      (sq_le_sq₀ (by norm_num) (abs_nonneg t)).mpr ht
    rw [sq_abs] at hsq
    nlinarith
  rw [abs_div, abs_two] at h
  have hdiv : (5 : ℝ) / (t / 2) ^ 2 ≤ 5 :=
    (div_le_iff₀ (by linarith : 0 < (t / 2) ^ 2)).mpr (by nlinarith)
  norm_num at h ⊢
  exact h.trans hdiv

/-- Exact scalar comparison on the whole real line. In the small region the
owner's n=0 series term and its entire tail are retained; in the large region
Stirling is applied at `t/2`. -/
theorem actual_gamma_scalar_bounds (t : ℝ) :
    0 ≤ LineFourier.actualIncrement t ∧
    LineFourier.actualIncrement (-t) = LineFourier.actualIncrement t ∧
    ell t ≤ C1 * (1 + LineFourier.actualIncrement t) ∧
    LineFourier.actualIncrement t ≤ C2 * ell t := by
  have hnn := delta_nonneg t
  have hlog := ell_ge_one t
  have hlog5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hdabs := le_abs_self d0
  have hndabs := neg_le_abs d0
  have hlow : ell t ≤ delta t + C1 := by
    by_cases ht : 2 ≤ |t|
    · have htpos : 0 < |t| := by linarith
      have hs := (abs_le.mp (stirling_scaled ht)).1
      have hcomp : ell t ≤ Real.log (|t| / 2) + Real.log 5 := by
        calc
          ell t ≤ Real.log ((|t| / 2) * 5) :=
            Real.log_le_log (by positivity) (by nlinarith)
          _ = _ := Real.log_mul (by positivity) (by norm_num)
      dsimp [delta, LineFourier.actualIncrement, C1, d0] at *
      linarith
    · have ht' : |t| ≤ 2 := (lt_of_not_ge ht).le
      have hcomp : ell t ≤ Real.log 5 := Real.log_le_log (by positivity) (by linarith)
      dsimp [C1]
      linarith [abs_nonneg d0]
  have hupp : delta t ≤ C2 * ell t := by
    by_cases ht : 2 ≤ |t|
    · have htpos : 0 < |t| := by linarith
      have hs := (abs_le.mp (stirling_scaled ht)).2
      have hcomp : Real.log (|t| / 2) ≤ ell t :=
        Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
      have hprod : 5 + |d0| ≤ (5 + |d0|) * ell t :=
        le_mul_of_one_le_right (by positivity) hlog
      dsimp [delta, LineFourier.actualIncrement, C2, d0] at *
      nlinarith
    · have hsmall : delta t ≤ 6 :=
        ArchimedeanJumpDecomposition.digamma_increment_le_six_of_abs_le_two
          (lt_of_not_ge ht).le
      have hprod : (6 : ℝ) ≤ 6 * ell t := by nlinarith
      dsimp [C2]
      nlinarith [mul_nonneg (abs_nonneg d0) (ell_nonneg t)]
  refine ⟨hnn, delta_even t, ?_, hupp⟩
  have hprod : delta t ≤ C1 * delta t := le_mul_of_one_le_left hnn C1_ge_one
  nlinarith [hlow]

private theorem one_add_delta_le (t : ℝ) : 1 + delta t ≤ (1 + C2) * ell t := by
  have h := (actual_gamma_scalar_bounds t).2.2.2
  nlinarith [ell_ge_one t]

private theorem paper_eq_angular_reflect (f : ℝ → ℂ) (t : ℝ) :
    Zeta23.paperFT f (t : ℂ) = LineFourier.angularFourier f (-t) := by
  rw [Zeta23.paperFT_ofReal_eq_fourier]
  rfl

theorem paper_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun t : ℝ => Zeta23.paperFT f (t : ℂ)) := by
  simp_rw [Zeta23.paperFT_ofReal_eq_fourier]
  exact (LineFourier.continuous_raw_fourier hf).comp (by fun_prop)

private theorem squared_gap_integrable {f : ℝ → ℂ} (hf : MemLp f 2) (s : ℝ) :
    Integrable (fun x : ℝ => ‖f x - f (x - s)‖ ^ 2) := by
  have hshift := hf.comp_measurePreserving
    (measurePreserving_sub_right (volume : Measure ℝ) s)
  exact (hf.sub hshift).integrable_norm_pow (p := 2) (by norm_num)

private theorem gap_mass_eq_lintegral {f : ℝ → ℂ} (hf : MemLp f 2) (s : ℝ) :
    ENNReal.ofReal (LineFourier.lineGapMass f s) =
      ∫⁻ x : ℝ, ‖f x - f (x - s)‖ₑ ^ 2 := by
  calc
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (‖f x - f (x - s)‖ ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal (squared_gap_integrable hf s)
        (Eventually.of_forall fun _ => sq_nonneg _)
    _ = _ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

theorem energy_eq_density_of_measurable {f : ℝ → ℂ}
    (hfm : Measurable f) (hf : MemLp f 2) :
    directionalEnergy actualGammaExitMeasure f =
      ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (LineFourier.actualDensity s) *
        ENNReal.ofReal (LineFourier.lineGapMass f s) := by
  have hρ : Measurable (fun s => ENNReal.ofReal (LineFourier.actualDensity s)) := by
    unfold LineFourier.actualDensity ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hgap : Measurable (fun p : ℝ × ℝ => ‖f p.2 - f (p.2 - p.1)‖ₑ ^ 2) :=
    ((hfm.comp measurable_snd).sub
      (hfm.comp (measurable_snd.sub measurable_fst))).enorm.pow_const 2
  have hm : Measurable (fun s : ℝ => ∫⁻ x : ℝ, ‖f x - f (x - s)‖ₑ ^ 2) :=
    hgap.lintegral_prod_right'
  -- This change unfolds the two aliases from the paid CornerTransport owner.
  change (∫⁻ s : ℝ, (∫⁻ x : ℝ, ‖f x - f (x - s)‖ₑ ^ 2)
      ∂((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (LineFourier.actualDensity s)))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ hm]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    dsimp only [Pi.mul_apply]
    rw [gap_mass_eq_lintegral hf s]

/-- The same density identity for an arbitrary L2 representative. Translation
preserves the a.e. equality used to choose its measurable representative. -/
theorem energy_eq_density_of_memLp {f : ℝ → ℂ} (hf : MemLp f 2) :
    directionalEnergy actualGammaExitMeasure f =
      ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (LineFourier.actualDensity s) *
        ENNReal.ofReal (LineFourier.lineGapMass f s) := by
  let g := hf.aestronglyMeasurable.aemeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.aemeasurable.measurable_mk
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hg : MemLp g 2 := (memLp_congr_ae hfg).mp hf
  have hgap (s : ℝ) : LineFourier.lineGapMass f s = LineFourier.lineGapMass g s := by
    apply integral_congr_ae
    have hshift := (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq_comp hfg
    filter_upwards [hfg, hshift] with x hx hs
    simp only [LineFourier.lineGapMass, Function.comp_apply] at *
    rw [hx, hs]
  calc
    _ = directionalEnergy actualGammaExitMeasure g := directionalEnergy_congr_ae _ hfg
    _ = _ := energy_eq_density_of_measurable hgm hg
    _ = _ := by simp_rw [hgap]

private theorem energy_eq_plus {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    directionalEnergy actualGammaExitMeasure f = kappaE *
      ∫⁻ t : ℝ, ENNReal.ofReal (delta t) * ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
  -- Measurable replacement is for Tonelli only. The final representative is f.
  let g := hf₂.aestronglyMeasurable.aemeasurable.mk f
  have hgm : Measurable g := hf₂.aestronglyMeasurable.aemeasurable.measurable_mk
  have hfg : f =ᵐ[volume] g := hf₂.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hg₁ : Integrable g := hf₁.congr hfg
  have hg₂ : MemLp g 2 := (memLp_congr_ae hfg).mp hf₂
  -- Only real frequencies are needed here. Both functions are L1, so these
  -- are actual absolutely convergent Fourier integrals.
  have hFT (t : ℝ) : Zeta23.paperFT f (t : ℂ) = Zeta23.paperFT g (t : ℂ) := by
    unfold Zeta23.paperFT
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  have hreflect :
      (∫⁻ t : ℝ, ENNReal.ofReal (delta t) * ‖LineFourier.angularFourier g t‖ₑ ^ 2) =
        ∫⁻ t : ℝ, ENNReal.ofReal (delta t) * ‖Zeta23.paperFT g (t : ℂ)‖ₑ ^ 2 := by
    calc
      _ = ∫⁻ t : ℝ, ENNReal.ofReal (delta (-t)) *
          ‖LineFourier.angularFourier g (-t)‖ₑ ^ 2 :=
        (lintegral_neg_eq_self (μ := (volume : Measure ℝ))
          (fun t => ENNReal.ofReal (delta t) * ‖LineFourier.angularFourier g t‖ₑ ^ 2)).symm
      _ = _ := by simp_rw [delta_even, ← paper_eq_angular_reflect]
  calc
    _ = directionalEnergy actualGammaExitMeasure g := directionalEnergy_congr_ae _ hfg
    _ = _ := energy_eq_density_of_measurable hgm hg₂
    _ = kappaE * ∫⁻ t : ℝ, ENNReal.ofReal (delta t) *
        ‖LineFourier.angularFourier g t‖ₑ ^ 2 :=
      LineFourier.actual_gamma_whole_line_energy_eq_angular_integral hg₁ hg₂
    _ = kappaE * ∫⁻ t : ℝ, ENNReal.ofReal (delta t) *
        ‖Zeta23.paperFT g (t : ℂ)‖ₑ ^ 2 := by rw [hreflect]
    _ = _ := by simp_rw [← hFT]

private theorem mass_eq_plus {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    coreL2Mass f = kappaE * ∫⁻ t : ℝ, ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
  have h := LineFourier.angular_extended_plancherel hf₁ hf₂
  have hreflect : (∫⁻ t : ℝ, ‖LineFourier.angularFourier f t‖ₑ ^ 2) =
      ∫⁻ t : ℝ, ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
    calc
      _ = ∫⁻ t : ℝ, ‖LineFourier.angularFourier f (-t)‖ₑ ^ 2 :=
        (lintegral_neg_eq_self (μ := (volume : Measure ℝ))
          (fun t => ‖LineFourier.angularFourier f t‖ₑ ^ 2)).symm
      _ = _ := by simp_rw [← paper_eq_angular_reflect]
  simpa only [coreL2Mass, hreflect] using h

private theorem graph_eq_plus {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    coreGraphSize actualGammaExitMeasure f = kappaE *
      ∫⁻ t : ℝ, ENNReal.ofReal (1 + delta t) * ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
  have hm : Measurable (fun t : ℝ => ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2) :=
    (paper_continuous hf₁).measurable.enorm.pow_const 2
  have hsum : (∫⁻ t : ℝ, ENNReal.ofReal (1 + delta t) *
      ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2) =
        (∫⁻ t : ℝ, ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2) +
        ∫⁻ t : ℝ, ENNReal.ofReal (delta t) * ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
    have hpoint (t : ℝ) : ENNReal.ofReal (1 + delta t) *
        ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 = ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 +
          ENNReal.ofReal (delta t) * ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (delta_nonneg t),
        ENNReal.ofReal_one, add_mul, one_mul]
    simp_rw [hpoint]
    exact lintegral_add_left hm _
  rw [coreGraphSize, mass_eq_plus hf₁ hf₂, energy_eq_plus hf₁ hf₂, hsum, mul_add]

/-- The actual whole-line jump graph and PLUS spectral identities, followed by
both exact extended graph/log estimates. Infinite energy is retained. -/
theorem actual_gamma_graph_log_bounds {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    directionalEnergy actualGammaExitMeasure f =
        ENNReal.ofReal (1 / (2 * Real.pi)) *
          (∫⁻ t : ℝ, ENNReal.ofReal (LineFourier.actualIncrement t) *
            ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2) ∧
    coreL2Mass f = ENNReal.ofReal (1 / (2 * Real.pi)) *
        (∫⁻ t : ℝ, ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2) ∧
    logFourierMass f ≤ ENNReal.ofReal (2 * Real.pi * C1) *
        coreGraphSize actualGammaExitMeasure f ∧
    coreGraphSize actualGammaExitMeasure f ≤
        ENNReal.ofReal ((1 + C2) / (2 * Real.pi)) * logFourierMass f := by
  refine ⟨energy_eq_plus hf₁ hf₂, mass_eq_plus hf₁ hf₂, ?_, ?_⟩
  · have hcoeff : ENNReal.ofReal (2 * Real.pi * C1) * kappaE = ENNReal.ofReal C1 := by
      have hC1 : 0 ≤ C1 := by linarith [C1_ge_one]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi * C1)]
      congr 1
      change (2 * Real.pi * C1) * (1 / (2 * Real.pi)) = C1
      field_simp [Real.pi_ne_zero]
    rw [graph_eq_plus hf₁ hf₂, ← mul_assoc, hcoeff]
    unfold logFourierMass
    calc
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (C1 * (1 + delta t)) *
          ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 :=
        lintegral_mono fun t => mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (actual_gamma_scalar_bounds t).2.2.1) (by positivity)
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul (by linarith [C1_ge_one] : 0 ≤ C1), mul_assoc]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · have hcoeff : ENNReal.ofReal ((1 + C2) / (2 * Real.pi)) =
        kappaE * ENNReal.ofReal (1 + C2) := by
      rw [← ENNReal.ofReal_mul kappa_pos.le]
      congr 1
      change (1 + C2) / (2 * Real.pi) = (1 / (2 * Real.pi)) * (1 + C2)
      ring
    rw [graph_eq_plus hf₁ hf₂, hcoeff, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold logFourierMass
    calc
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal ((1 + C2) * ell t) *
          ‖Zeta23.paperFT f (t : ℂ)‖ₑ ^ 2 :=
        lintegral_mono fun t => mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (one_add_delta_le t)) (by positivity)
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul (by linarith [C2_nonneg] : 0 ≤ 1 + C2), mul_assoc]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem mass_lt_top {f : ℝ → ℂ} (hf : MemLp f 2) : coreL2Mass f < ⊤ := by
  rw [coreL2Mass, LineFourier.squared_mass_eq_eLpNorm f hf.aestronglyMeasurable]
  exact ENNReal.pow_lt_top hf

private theorem graph_lt_top {f : ℝ → ℂ} (hf : MemLp f 2)
    (hE : directionalEnergy actualGammaExitMeasure f < ⊤) :
    coreGraphSize actualGammaExitMeasure f < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨mass_lt_top hf, hE⟩

private theorem log_mass_eq_lintegral (f : ℝ → ℂ) :
    logFourierMass f = ∫⁻ t : ℝ,
      ENNReal.ofReal (ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) := by
  unfold logFourierMass
  apply lintegral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [ENNReal.ofReal_mul (ell_nonneg t),
      ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

private theorem integrable_log_iff {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) ↔
      logFourierMass f < ⊤ := by
  have hm : AEStronglyMeasurable
      (fun t : ℝ => ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) volume :=
    (ell_continuous.mul ((paper_continuous hf).norm.pow 2)).aestronglyMeasurable
  have hnn : ∀ᵐ t : ℝ, 0 ≤ ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2 :=
    Eventually.of_forall fun t => mul_nonneg (ell_nonneg t) (sq_nonneg _)
  rw [log_mass_eq_lintegral]
  exact ⟨fun h => (hasFiniteIntegral_iff_ofReal hnn).mp h.2,
    fun h => ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).mpr h⟩⟩

/-- Finiteness is obtained from the extended estimates, before asserting an
ordinary log-weight integrability conclusion. -/
theorem actual_gamma_finite_energy_iff_log_integrable {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    directionalEnergy actualGammaExitMeasure f < ⊤ ↔
      Integrable (fun t : ℝ => ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) := by
  have hbounds := actual_gamma_graph_log_bounds hf₁ hf₂
  rw [integrable_log_iff hf₁]
  constructor
  · intro hE
    have hH := graph_lt_top hf₂ hE
    exact lt_of_le_of_lt hbounds.2.2.1 (by finiteness)
  · intro hL
    have hH : coreGraphSize actualGammaExitMeasure f < ⊤ :=
      lt_of_le_of_lt hbounds.2.2.2 (by finiteness)
    exact lt_of_le_of_lt (le_add_left le_rfl) hH

private theorem mass_toReal {f : ℝ → ℂ} (hf : MemLp f 2) :
    (coreL2Mass f).toReal = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hsq := hf.integrable_norm_pow (p := 2) (by norm_num)
  have h : ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) = coreL2Mass f := by
    rw [coreL2Mass]
    calc
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun _ => sq_nonneg _)
      _ = _ := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  rw [← h, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]

private theorem graph_toReal {f : ℝ → ℂ} (hf : MemLp f 2)
    (hE : directionalEnergy actualGammaExitMeasure f < ⊤) :
    (coreGraphSize actualGammaExitMeasure f).toReal =
      (∫ x : ℝ, ‖f x‖ ^ 2) + (directionalEnergy actualGammaExitMeasure f).toReal := by
  rw [coreGraphSize, ENNReal.toReal_add (mass_lt_top hf).ne hE.ne, mass_toReal hf]

private theorem log_mass_toReal {f : ℝ → ℂ}
    (hL : Integrable (fun t : ℝ => ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2)) :
    (logFourierMass f).toReal = ∫ t : ℝ, ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2 := by
  rw [log_mass_eq_lintegral, ← ofReal_integral_eq_lintegral_ofReal hL
    (Eventually.of_forall fun t => mul_nonneg (ell_nonneg t) (sq_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg fun t => mul_nonneg (ell_nonneg t) (sq_nonneg _))]

/-- Ordinary real estimates, guarded by actual jump-energy finiteness. The
spatial mass and the log integral are integrable, and the ENNReal energy is
converted to a real number only under that guard. -/
theorem actual_gamma_graph_log_real_bounds {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hE : directionalEnergy actualGammaExitMeasure f < ⊤) :
    Integrable (fun t : ℝ => ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) ∧
    (∫ t : ℝ, ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) ≤
      (2 * Real.pi * C1) *
        ((∫ x : ℝ, ‖f x‖ ^ 2) + (directionalEnergy actualGammaExitMeasure f).toReal) ∧
    ((∫ x : ℝ, ‖f x‖ ^ 2) + (directionalEnergy actualGammaExitMeasure f).toReal) ≤
      ((1 + C2) / (2 * Real.pi)) *
        (∫ t : ℝ, ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) := by
  have hL := (actual_gamma_finite_energy_iff_log_integrable hf₁ hf₂).mp hE
  have hLf := (integrable_log_iff hf₁).mp hL
  have hHf := graph_lt_top hf₂ hE
  have hC1 : 0 ≤ 2 * Real.pi * C1 := by
    have := C1_ge_one
    positivity
  have hC2 : 0 ≤ (1 + C2) / (2 * Real.pi) := by
    have := C2_nonneg
    positivity
  have hb := actual_gamma_graph_log_bounds hf₁ hf₂
  have hlow := ENNReal.toReal_mono
    (by finiteness : ENNReal.ofReal (2 * Real.pi * C1) *
      coreGraphSize actualGammaExitMeasure f ≠ ⊤) hb.2.2.1
  have hupp := ENNReal.toReal_mono
    (by finiteness : ENNReal.ofReal ((1 + C2) / (2 * Real.pi)) *
      logFourierMass f ≠ ⊤) hb.2.2.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC1, log_mass_toReal hL,
    graph_toReal hf₂ hE] at hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC2, log_mass_toReal hL,
    graph_toReal hf₂ hE] at hupp
  exact ⟨hL, hlow, hupp⟩

private theorem ioc_L1_L2 (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Integrable (PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) ∧
      MemLp (PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) 2 := by
  have hend : -a + 2 * a = a := by ring
  have hI : IntegrableOn u (Ioc (-a) a) := hu.integrable (by norm_num)
  constructor
  · simpa only [PeriodicEnergyTransport.zeroExtension, hend] using
      (integrable_indicator_iff measurableSet_Ioc).mpr hI
  · apply PeriodicEnergyTransport.zero_extension_memLp
    simpa only [PeriodicEnergyTransport.windowMeasure, hend] using hu

/-- The exact original Ioc L2 carrier: literal `zeroExtension (2*a) (-a)`,
the actual exit measure, both extended constants and the finite-domain iff.
The statement even permits degenerate intervals; no parity restriction occurs. -/
theorem actual_ioc_gamma_graph_log_equivalence (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    let F := PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    logFourierMass F ≤ ENNReal.ofReal (2 * Real.pi * C1) *
        coreGraphSize actualGammaExitMeasure F ∧
    coreGraphSize actualGammaExitMeasure F ≤
        ENNReal.ofReal ((1 + C2) / (2 * Real.pi)) * logFourierMass F ∧
    (directionalEnergy actualGammaExitMeasure F < ⊤ ↔
      Integrable (fun t : ℝ => ell t * ‖Zeta23.paperFT F (t : ℂ)‖ ^ 2)) := by
  dsimp only
  obtain ⟨hF₁, hF₂⟩ := ioc_L1_L2 a u hu
  have hb := actual_gamma_graph_log_bounds hF₁ hF₂
  exact ⟨hb.2.2.1, hb.2.2.2, actual_gamma_finite_energy_iff_log_integrable hF₁ hF₂⟩

private theorem paperFT_sub_real {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    Zeta23.paperFT (fun x => f x - g x) (t : ℂ) =
      Zeta23.paperFT f (t : ℂ) - Zeta23.paperFT g (t : ℂ) := by
  simp_rw [Zeta23.paperFT_ofReal_eq_fourier]
  exact LineFourier.raw_fourier_sub hf hg _

private theorem ioc_difference_mass_eq (a : ℝ) (u v : ℝ → ℂ) :
    coreL2Mass (fun x => PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x -
      PeriodicEnergyTransport.zeroExtension (2 * a) (-a) v x) =
        ∫⁻ x in Ioc (-a) a, ‖u x - v x‖ₑ ^ 2 := by
  have hend : -a + 2 * a = a := by ring
  unfold coreL2Mass
  calc
    _ = ∫⁻ x : ℝ, (Ioc (-a) a).indicator (fun x => ‖u x - v x‖ₑ ^ 2) x := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc (-a) a <;>
          simp [PeriodicEnergyTransport.zeroExtension, hend, hx]
    _ = _ := lintegral_indicator measurableSet_Ioc _

/-- Difference/error consumer on the original interval. Both extended bounds
apply to the physical difference, and the finite-domain iff uses the actual
difference of the two PLUS Fourier profiles. -/
theorem actual_ioc_difference_graph_log_bounds (a : ℝ) (u v : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (hv : MemLp v 2 (volume.restrict (Ioc (-a) a))) :
    let F := PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    let G := PeriodicEnergyTransport.zeroExtension (2 * a) (-a) v
    let e := fun x => F x - G x
    coreL2Mass e = (∫⁻ x in Ioc (-a) a, ‖u x - v x‖ₑ ^ 2) ∧
    (∀ t : ℝ, Zeta23.paperFT e (t : ℂ) =
      Zeta23.paperFT F (t : ℂ) - Zeta23.paperFT G (t : ℂ)) ∧
    logFourierMass e ≤ ENNReal.ofReal (2 * Real.pi * C1) *
      coreGraphSize actualGammaExitMeasure e ∧
    coreGraphSize actualGammaExitMeasure e ≤
      ENNReal.ofReal ((1 + C2) / (2 * Real.pi)) * logFourierMass e ∧
    (directionalEnergy actualGammaExitMeasure e < ⊤ ↔ Integrable (fun t : ℝ =>
      ell t * ‖Zeta23.paperFT F (t : ℂ) - Zeta23.paperFT G (t : ℂ)‖ ^ 2)) := by
  dsimp only
  obtain ⟨hF₁, hF₂⟩ := ioc_L1_L2 a u hu
  obtain ⟨hG₁, hG₂⟩ := ioc_L1_L2 a v hv
  have hFT := paperFT_sub_real hF₁ hG₁
  have hz : PeriodicEnergyTransport.zeroExtension (2 * a) (-a) (fun x => u x - v x) =
      (fun x => PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x -
        PeriodicEnergyTransport.zeroExtension (2 * a) (-a) v x) := by
    funext x
    by_cases hx : x ∈ Ioc (-a) (-a + 2 * a) <;>
      simp [PeriodicEnergyTransport.zeroExtension, hx]
  have hb := actual_ioc_gamma_graph_log_equivalence a (fun x => u x - v x) (hu.sub hv)
  dsimp only at hb
  rw [hz] at hb
  refine ⟨ioc_difference_mass_eq a u v, hFT, hb.1, hb.2.1, ?_⟩
  simpa only [hFT] using hb.2.2

private abbrev continuityWeight (t : ℝ) : ℝ := 1 + Real.log (1 + |t|)

private theorem continuityWeight_nonneg (t : ℝ) : 0 ≤ continuityWeight t := by
  have hlog : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  dsimp [continuityWeight]
  linarith

private theorem continuityWeight_continuous : Continuous continuityWeight := by
  exact continuous_const.add ((continuous_const.add continuous_abs).log
    (fun t => by
      change 1 + |t| ≠ 0
      have := abs_nonneg t
      linarith))

/-- The exact dictionary to the existing continuity theorem's weight.
This is a comparison of weights, with explicit constants, rather than a new
Gamma growth or quadratic continuity theorem. -/
theorem log_weight_dictionary (t : ℝ) :
    ell t ≤ Real.log 3 * (1 + Real.log (1 + |t|)) ∧
    (1 + Real.log (1 + |t|)) ≤ 2 * ell t := by
  have hlog1 : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    convert Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> norm_num
  have hcomp : ell t ≤ Real.log 3 + Real.log (1 + |t|) := by
    calc
      ell t ≤ Real.log (3 * (1 + |t|)) :=
        Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
      _ = _ := Real.log_mul (by norm_num) (by positivity)
  have hprod : Real.log (1 + |t|) ≤ Real.log 3 * Real.log (1 + |t|) :=
    le_mul_of_one_le_left hlog1 hlog3
  have hcomp' : Real.log (1 + |t|) ≤ ell t :=
    Real.log_le_log (by positivity) (by linarith)
  constructor <;> nlinarith [ell_ge_one t]

private theorem weighted_integrable_of_log {P : ℝ → ℂ} (hP : Continuous P)
    (hL : Integrable (fun t : ℝ => ell t * ‖P t‖ ^ 2)) :
    Integrable (fun t : ℝ => continuityWeight t * Complex.normSq (P t)) := by
  refine (hL.const_mul 2).mono'
    (continuityWeight_continuous.mul
      (Complex.continuous_normSq.comp hP)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (continuityWeight_nonneg t)
      (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_right (log_weight_dictionary t).2 (sq_nonneg ‖P t‖)]

private theorem log_integrable_of_weighted {P : ℝ → ℂ} (hP : Continuous P)
    (hW : Integrable (fun t : ℝ => continuityWeight t * Complex.normSq (P t))) :
    Integrable (fun t : ℝ => ell t * ‖P t‖ ^ 2) := by
  refine (hW.const_mul (Real.log 3)).mono'
    (ell_continuous.mul (hP.norm.pow 2)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ell_nonneg t) (sq_nonneg _)),
      Complex.normSq_eq_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_right (log_weight_dictionary t).1 (sq_nonneg ‖P t‖)]

/-- A measurable finite-domain dictionary for arbitrary continuous complex
frequency profiles, including the exact `normSq` weight of the reused consumer. -/
theorem log_weight_integrable_iff {P : ℝ → ℂ} (hP : Continuous P) :
    Integrable (fun t : ℝ => ell t * ‖P t‖ ^ 2) ↔
      Integrable (fun t : ℝ =>
        (1 + Real.log (1 + |t|)) * Complex.normSq (P t)) :=
  ⟨weighted_integrable_of_log hP, log_integrable_of_weighted hP⟩

private theorem weighted_error_bound {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hE : directionalEnergy actualGammaExitMeasure f < ⊤) :
    Integrable (fun t : ℝ => continuityWeight t * Complex.normSq (Zeta23.paperFT f (t : ℂ))) ∧
    kappa * (∫ t : ℝ, continuityWeight t * Complex.normSq (Zeta23.paperFT f (t : ℂ))) ≤
      (2 * C1) * (coreGraphSize actualGammaExitMeasure f).toReal := by
  have hr := actual_gamma_graph_log_real_bounds hf₁ hf₂ hE
  have hW := (log_weight_integrable_iff (paper_continuous hf₁)).mp hr.1
  have hI : (∫ t : ℝ, continuityWeight t * Complex.normSq (Zeta23.paperFT f (t : ℂ))) ≤
      2 * (∫ t : ℝ, ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono hW (hr.1.const_mul 2)
    intro t
    dsimp only
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_right (log_weight_dictionary t).2
      (sq_nonneg ‖Zeta23.paperFT f (t : ℂ)‖)]
  refine ⟨hW, ?_⟩
  calc
    _ ≤ kappa * (2 * (∫ t : ℝ, ell t * ‖Zeta23.paperFT f (t : ℂ)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hI kappa_pos.le
    _ ≤ kappa * (2 * ((2 * Real.pi * C1) *
        ((∫ x : ℝ, ‖f x‖ ^ 2) + (directionalEnergy actualGammaExitMeasure f).toReal))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr.2.1 (by norm_num)) kappa_pos.le
    _ = _ := by
      rw [graph_toReal hf₂ hE]
      unfold kappa
      field_simp [Real.pi_ne_zero]

/-- Original-domain error consumer. Extended graph convergence of literal
zero extensions gives the exact log-weight error required by the EXISTING
public Gamma quadratic continuity theorem, which is applied at the last line.
The filter may be arbitrary; energy finiteness of errors is derived eventually
from extended convergence, rather than assumed or imposed on all approximants. -/
theorem actual_ioc_gamma_quadratic_tendsto_of_graph_error
    {α : Type*} {l : Filter α} (a : ℝ) (u : ℝ → ℂ) (v : α → ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Ioc (-a) a)))
    (hE : directionalEnergy actualGammaExitMeasure
      (PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < ⊤)
    (hgraph : Tendsto (fun i => coreGraphSize actualGammaExitMeasure
      (fun x => PeriodicEnergyTransport.zeroExtension (2 * a) (-a) (v i) x -
        PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)) l (𝓝 (0 : ℝ≥0∞))) :
    let F := PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
    let G := fun i => PeriodicEnergyTransport.zeroExtension (2 * a) (-a) (v i)
    Tendsto (fun i => (1 / (2 * Real.pi)) * ∫ t : ℝ,
      (2 * Real.pi * Zeta23.mu t) * Complex.normSq (Zeta23.paperFT (G i) (t : ℂ))) l
      (𝓝 ((1 / (2 * Real.pi)) * ∫ t : ℝ,
        (2 * Real.pi * Zeta23.mu t) * Complex.normSq (Zeta23.paperFT F (t : ℂ)))) := by
  dsimp only
  let F := PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
  let G := fun i => PeriodicEnergyTransport.zeroExtension (2 * a) (-a) (v i)
  let e := fun i x => G i x - F x
  obtain ⟨hF₁, hF₂⟩ := ioc_L1_L2 a u hu
  have hG : ∀ i, Integrable (G i) ∧ MemLp (G i) 2 := fun i => ioc_L1_L2 a (v i) (hv i)
  have he₁ : ∀ i, Integrable (e i) := fun i => (hG i).1.sub hF₁
  have he₂ : ∀ i, MemLp (e i) 2 := fun i => (hG i).2.sub hF₂
  have hFT (i : α) (t : ℝ) : Zeta23.paperFT (e i) (t : ℂ) =
      Zeta23.paperFT (G i) (t : ℂ) - Zeta23.paperFT F (t : ℂ) :=
    paperFT_sub_real (hG i).1 hF₁ t
  have hgraph' : Tendsto (fun i => coreGraphSize actualGammaExitMeasure (e i))
      l (𝓝 (0 : ℝ≥0∞)) := hgraph
  have hsmall : ∀ᶠ i in l, coreGraphSize actualGammaExitMeasure (e i) < 1 :=
    hgraph'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have heE : ∀ᶠ i in l, directionalEnergy actualGammaExitMeasure (e i) < ⊤ := by
    filter_upwards [hsmall] with i hi
    have hH : coreGraphSize actualGammaExitMeasure (e i) < ⊤ :=
      hi.trans (by norm_num)
    exact lt_of_le_of_lt (le_add_left le_rfl) hH
  have hWU := (weighted_error_bound hF₁ hF₂ hE).1
  have hWE : ∀ᶠ i in l, Integrable (fun t : ℝ => continuityWeight t *
      Complex.normSq (Zeta23.paperFT (G i) (t : ℂ) - Zeta23.paperFT F (t : ℂ))) := by
    filter_upwards [heE] with i hi
    have hlog := (actual_ioc_difference_graph_log_bounds a (v i) u (hv i) hu).2.2.2.2.mp hi
    exact (log_weight_integrable_iff
      ((paper_continuous (hG i).1).sub (paper_continuous hF₁))).mp hlog
  have ht : Tendsto (fun i => (coreGraphSize actualGammaExitMeasure (e i)).toReal)
      l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgraph'
  have hb : Tendsto (fun i => (2 * C1) *
      (coreGraphSize actualGammaExitMeasure (e i)).toReal) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have hlim : Tendsto (fun i => kappa * ∫ t : ℝ, continuityWeight t *
      Complex.normSq (Zeta23.paperFT (G i) (t : ℂ) - Zeta23.paperFT F (t : ℂ)))
      l (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev := (tendsto_order.1 hb).2 ε hε
    filter_upwards [heE, hev] with i hi hbi
    have hbound := (weighted_error_bound (he₁ i) (he₂ i) hi).2
    simp only [hFT] at hbound
    have hnonneg : 0 ≤ kappa * ∫ t : ℝ, continuityWeight t *
        Complex.normSq (Zeta23.paperFT (G i) (t : ℂ) - Zeta23.paperFT F (t : ℂ)) :=
      mul_nonneg kappa_pos.le (integral_nonneg fun t =>
        mul_nonneg (continuityWeight_nonneg t) (Complex.normSq_nonneg _))
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hbound.trans_lt hbi
  exact LogarithmicFormContinuity.actual_gamma_quadratic_tendsto_of_log_weight_error
    (paper_continuous hF₁) hWU
    (Eventually.of_forall fun i => paper_continuous (hG i).1) hWE hlim

end D5.S3.Weil.ZetaGamma.FormCore.LogGraph
