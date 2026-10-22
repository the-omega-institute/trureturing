/-
Source-only continuation r4056, retaining the r4039 analytic bodies.
UNCOMPILED throughout; no native acceptance is claimed.
The sealed r4033 file is evidence, not an import: its false image split,
whole-line periodic carrier, and placeholder bridges are deliberately replaced.
Original definitions/owners and all signed modes are retained below.

The general weighted-lattice theorem consumed here was inspected in immutable
5860a2489d25479eed8a8fc3ee91719f543189ff, PeriodicEnergyTransport.lean.
Mathlib API inspection is at 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import D5.S3.Weil.ZetaCore.Defs
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.LogGraph
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation.BoundaryMixedRates
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

/-- Ordinary norm-square expansion; used to establish the four finite profiles. -/
lemma normSq_linear (a b z w : ℂ) :
    Complex.normSq (a*z+b*w) = Complex.normSq a * Complex.normSq z +
      Complex.normSq b * Complex.normSq w + 2*(conj a*b*(conj z*w)).re := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- Finiteness of ALL polarization profiles is derived from actual diagonal
energies and the already-paid absolute mixed pairing, rather than assumed. -/
lemma profile_energy_integrable (L : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hEf : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) f s) (Ioi 0))
    (hEg : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) g s) (Ioi 0)) (a b : ℂ) :
    IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) (a • f+b • g) s) (Ioi 0) := by
  have hfw := continuous_memLp_window L hf
  have hgw := continuous_memLp_window L hg
  have hmix := finite_energy_mixed_integrable L (-L/2) f g hfw hgw hEf hEg
  let q : ℝ → ℂ := fun s => ∫ x,
    conj (zeroGapMap L (-L/2) s f x)*zeroGapMap L (-L/2) s g x
  have hformula (s : ℝ) :
      zeroTranslationEnergy L (-L/2) (a • f+b • g) s =
        Complex.normSq a * zeroTranslationEnergy L (-L/2) f s +
        Complex.normSq b * zeroTranslationEnergy L (-L/2) g s +
        2*(conj a*b*q s).re := by
    have hf0 := zero_extension_memLp L (-L/2) f hfw
    have hg0 := zero_extension_memLp L (-L/2) g hgw
    have hdf := hf0.sub (hf0.comp_measurePreserving (measurePreserving_sub_right volume s))
    have hdg := hg0.sub (hg0.comp_measurePreserving (measurePreserving_sub_right volume s))
    have hF : Integrable (fun x => Complex.normSq (zeroGapMap L (-L/2) s f x)) := by
      simpa only [Complex.normSq_eq_norm_sq, zeroGapMap, LinearMap.coe_mk,
        AddHom.coe_mk, Pi.sub_apply, Function.comp_apply] using
        hdf.integrable_norm_pow (p:=2) (by norm_num)
    have hG : Integrable (fun x => Complex.normSq (zeroGapMap L (-L/2) s g x)) := by
      simpa only [Complex.normSq_eq_norm_sq, zeroGapMap, LinearMap.coe_mk,
        AddHom.coe_mk, Pi.sub_apply, Function.comp_apply] using
        hdg.integrable_norm_pow (p:=2) (by norm_num)
    have hC : Integrable (fun x => (conj a*b)*
        (conj (zeroGapMap L (-L/2) s f x)*zeroGapMap L (-L/2) s g x)) := by
      simpa only [zeroGapMap, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.sub_apply, Function.comp_apply] using
        (l2_complex_correlation_integrable hdf hdg).const_mul (conj a*b)
    change (∫ x, Complex.normSq (zeroGapMap L (-L/2) s (a • f+b • g) x)) = _
    simp_rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, normSq_linear]
    have hAB : Integrable (fun x =>
        Complex.normSq a * Complex.normSq (zeroGapMap L (-L/2) s f x) +
        Complex.normSq b * Complex.normSq (zeroGapMap L (-L/2) s g x)) :=
      (hF.const_mul _).add (hG.const_mul _)
    have hR : Integrable (fun x =>
        2*((conj a*b)*(conj (zeroGapMap L (-L/2) s f x)*
          zeroGapMap L (-L/2) s g x)).re) := hC.re.const_mul 2
    have hCre := integral_re hC
    simp only [RCLike.re_eq_complex_re] at hCre
    rw [integral_add hAB hR,
      integral_add (hF.const_mul _) (hG.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul, hCre, integral_const_mul]
    rfl
  have hI := ((hEf.const_mul (Complex.normSq a)).add
    (hEg.const_mul (Complex.normSq b))).add
      ((hmix.const_mul (conj a*b)).re.const_mul 2)
  apply hI.congr
  exact Eventually.of_forall fun s => by
    change Complex.normSq a *
        (ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
          zeroTranslationEnergy L (-L/2) f s) +
      Complex.normSq b *
        (ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
          zeroTranslationEnergy L (-L/2) g s) +
      2*((conj a*b)*((ArchimedeanJumpDecomposition.archimedeanJumpDensity s:ℂ)*q s)).re =
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) (a • f+b • g) s
    rw [hformula]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring

lemma zeroExtension_linear (L : ℝ) (f g : ℝ → ℂ) (a b : ℂ) :
    zeroExtension L (-L/2) (a • f+b • g) =
      a • zeroExtension L (-L/2) f + b • zeroExtension L (-L/2) g := by
  funext x
  by_cases hx : x ∈ Ioc (-L/2) (-L/2+L) <;>
    simp [zeroExtension, hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Real-frequency kernel integrability pays Fourier linearity on L1 inputs. -/
lemma paperFT_linear (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (a b : ℂ) (t : ℝ) :
    Zeta23.paperFT (a • f+b • g) (t : ℂ) =
      a*Zeta23.paperFT f (t : ℂ)+b*Zeta23.paperFT g (t : ℂ) := by
  have hk (u : ℝ → ℂ) (hu : Integrable u) : Integrable
      (fun x => u x*Complex.exp (Complex.I*(t:ℂ)*(x:ℂ))) := by
    apply hu.norm.mono' (hu.aestronglyMeasurable.mul
      (show Continuous (fun x : ℝ => Complex.exp (Complex.I*(t:ℂ)*(x:ℂ))) by
        fun_prop).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]
      rw [norm_mul, Complex.norm_exp]
      simp
  unfold Zeta23.paperFT
  have hp (x : ℝ) : (a • f+b • g) x*Complex.exp (Complex.I*(t:ℂ)*(x:ℂ)) =
      a*(f x*Complex.exp (Complex.I*(t:ℂ)*(x:ℂ)))+
        b*(g x*Complex.exp (Complex.I*(t:ℂ)*(x:ℂ))) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hp]
  rw [integral_add ((hk f hf).const_mul a) ((hk g hg).const_mul b),
    integral_const_mul, integral_const_mul]

/-- Every norm-square integral here is first known finite in ENNReal.
The PLUS reflection and the t/2 scale are inherited from the original public
LogGraph owner; its existing density proof is exposed by the companion patch. -/
theorem finite_plus_quadratics_of_memLp (L : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L (-L/2)))
    (hE : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) (Ioi 0)) :
    let F := zeroExtension L (-L/2) u
    Integrable (fun t : ℝ => ‖Zeta23.paperFT F (t:ℂ)‖^2) ∧
    Integrable (fun t : ℝ => FormCore.LineFourier.actualIncrement t *
      ‖Zeta23.paperFT F (t:ℂ)‖^2) ∧
    (∫ x, ‖F x‖^2) = (1/(2*Real.pi)) * ∫ t : ℝ, ‖Zeta23.paperFT F (t:ℂ)‖^2 ∧
    (∫ s in Ioi 0, ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) =
      (1/(2*Real.pi))*∫ t : ℝ, FormCore.LineFourier.actualIncrement t *
        ‖Zeta23.paperFT F (t:ℂ)‖^2 := by
  dsimp only
  let F := zeroExtension L (-L/2) u
  have hF₂ : MemLp F 2 := zero_extension_memLp L (-L/2) u hu
  have hF₁ : Integrable F := by
    have hw : Integrable u (windowMeasure L (-L/2)) :=
      hu.integrable (by norm_num)
    exact (integrable_indicator_iff measurableSet_Ioc).mpr hw
  have hFT := FormCore.LogGraph.paper_continuous hF₁
  have hscalar := FormCore.LogGraph.actual_gamma_scalar_bounds
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) u s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hrealE : ENNReal.ofReal (∫ s in Ioi 0,
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) u s) =
      FormCore.directionalEnergy FormCore.actualGammaExitMeasure F := by
    rw [FormCore.LogGraph.energy_eq_density_of_memLp hF₂]
    rw [ofReal_integral_eq_lintegral_ofReal hE hnn]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [ENNReal.ofReal_mul (ArchimedeanJumpDecomposition.jump_density_nonnegative hs)]
    congr 1
    simp only [FormCore.LineFourier.lineGapMass, zeroTranslationEnergy, F,
      Complex.normSq_eq_norm_sq]
  have hmassI := hF₂.integrable_norm_pow (p:=2) (by norm_num)
  have hrealM : ENNReal.ofReal (∫ x, ‖F x‖^2) = FormCore.coreL2Mass F := by
    rw [ofReal_integral_eq_lintegral_ofReal hmassI (Eventually.of_forall fun x => sq_nonneg _)]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have howner := FormCore.LogGraph.actual_gamma_graph_log_bounds hF₁ hF₂
  have hM : ENNReal.ofReal (∫ x, ‖F x‖^2) = ENNReal.ofReal (1/(2*Real.pi)) *
      ∫⁻ t : ℝ, ENNReal.ofReal (‖Zeta23.paperFT F (t:ℂ)‖^2) := by
    rw [hrealM, howner.2.1]
    congr 1
    apply lintegral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hD : ENNReal.ofReal (∫ s in Ioi 0,
      ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) u s) = ENNReal.ofReal (1/(2*Real.pi)) *
      ∫⁻ t : ℝ, ENNReal.ofReal (FormCore.LineFourier.actualIncrement t *
        ‖Zeta23.paperFT F (t:ℂ)‖^2) := by
    rw [hrealE, howner.1]
    congr 1
    apply lintegral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [ENNReal.ofReal_mul (hscalar t).1,
        ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hδm : Measurable FormCore.LineFourier.actualIncrement := by
    have heq : FormCore.LineFourier.actualIncrement = fun t : ℝ =>
        2*Real.pi*Zeta23.mu t+Real.log Real.pi-(Complex.digamma (1/4)).re := by
      funext t
      exact FormCore.LogGraph.delta_eq_mu t
    rw [heq]
    exact (((continuous_const.mul Zeta23.mu_smooth.continuous).add
      continuous_const).sub continuous_const).measurable
  have hmass := finite_scaled_lintegral volume _ (hFT.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun t => sq_nonneg _) (1/(2*Real.pi)) _ (by positivity)
    (integral_nonneg fun x => sq_nonneg _) hM
  have hdelta := finite_scaled_lintegral volume _
    (hδm.aestronglyMeasurable.mul (hFT.norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun t => mul_nonneg (hscalar t).1 (sq_nonneg _))
    (1/(2*Real.pi)) _ (by positivity) (integral_nonneg_of_ae hnn) hD
  exact ⟨hmass.1, hdelta.1, hmass.2, hdelta.2⟩

/-- The original continuous-profile API is preserved. -/
theorem finite_plus_quadratics (L : ℝ) (u : ℝ → ℂ) (hu : Continuous u)
    (hE : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) (Ioi 0)) :
    let F := zeroExtension L (-L/2) u
    Integrable (fun t : ℝ => ‖Zeta23.paperFT F (t:ℂ)‖^2) ∧
    Integrable (fun t : ℝ => FormCore.LineFourier.actualIncrement t *
      ‖Zeta23.paperFT F (t:ℂ)‖^2) ∧
    (∫ x, ‖F x‖^2) = (1/(2*Real.pi)) * ∫ t : ℝ, ‖Zeta23.paperFT F (t:ℂ)‖^2 ∧
    (∫ s in Ioi 0, ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) =
      (1/(2*Real.pi))*∫ t : ℝ, FormCore.LineFourier.actualIncrement t *
        ‖Zeta23.paperFT F (t:ℂ)‖^2 := by
  exact finite_plus_quadratics_of_memLp L u (continuous_memLp_window L hu) hE

/-- Literal mu quadratic, including its signed constant, after finite conversion. -/
theorem mu_quadratic_of_memLp (L : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure L (-L/2)))
    (hE : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) (Ioi 0)) :
    let F := zeroExtension L (-L/2) u
    Integrable (fun t : ℝ => Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t:ℂ))) ∧
    (∫ t : ℝ, Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t:ℂ))) =
      ((Complex.digamma (1/4)).re-Real.log Real.pi) * (∫ x, Complex.normSq (F x)) +
      ∫ s in Ioi 0, ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) u s := by
  dsimp only
  have hd := finite_plus_quadratics_of_memLp L u hu hE
  simp only [Complex.normSq_eq_norm_sq]
  have hμ (t : ℝ) : Zeta23.mu t = (1/(2*Real.pi))*
      (((Complex.digamma (1/4)).re-Real.log Real.pi)+FormCore.LineFourier.actualIncrement t) := by
    have hs := FormCore.LogGraph.delta_eq_mu t
    change FormCore.LineFourier.actualIncrement t =
      2*Real.pi*Zeta23.mu t+Real.log Real.pi-(Complex.digamma (1/4)).re at hs
    field_simp [Real.pi_ne_zero]
    nlinarith [hs]
  have hi := ((hd.1.const_mul ((Complex.digamma (1/4)).re-Real.log Real.pi)).add
    hd.2.1).const_mul (1/(2*Real.pi))
  have hfun : (fun t : ℝ => Zeta23.mu t *
      ‖Zeta23.paperFT (zeroExtension L (-L/2) u) (t:ℂ)‖^2) =
    fun t : ℝ => (1/(2*Real.pi))*
      ((((Complex.digamma (1/4)).re-Real.log Real.pi)*
        ‖Zeta23.paperFT (zeroExtension L (-L/2) u) (t:ℂ)‖^2)+
        FormCore.LineFourier.actualIncrement t *
        ‖Zeta23.paperFT (zeroExtension L (-L/2) u) (t:ℂ)‖^2) := by
    funext t
    rw [hμ]
    ring
  refine ⟨hi.congr (Eventually.of_forall fun t => (congrFun hfun t).symm), ?_⟩
  rw [hfun, integral_const_mul,
    integral_add (hd.1.const_mul _) hd.2.1, integral_const_mul]
  calc
    _ = ((Complex.digamma (1/4)).re-Real.log Real.pi) *
          ((1/(2*Real.pi))*∫ t : ℝ,
            ‖Zeta23.paperFT (zeroExtension L (-L/2) u) (t:ℂ)‖^2) +
        (1/(2*Real.pi))*∫ t : ℝ, FormCore.LineFourier.actualIncrement t *
          ‖Zeta23.paperFT (zeroExtension L (-L/2) u) (t:ℂ)‖^2 := by ring
    _ = ((Complex.digamma (1/4)).re-Real.log Real.pi) *
          (∫ x, ‖zeroExtension L (-L/2) u x‖^2) +
        (∫ s in Ioi 0, ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
          zeroTranslationEnergy L (-L/2) u s) := by
      rw [← hd.2.2.1, ← hd.2.2.2]
    _ = _ := by ring

/-- The original continuous-profile mu statement is preserved. -/
theorem mu_quadratic (L : ℝ) (u : ℝ → ℂ) (hu : Continuous u)
    (hE : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) u s) (Ioi 0)) :
    let F := zeroExtension L (-L/2) u
    Integrable (fun t : ℝ => Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t:ℂ))) ∧
    (∫ t : ℝ, Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t:ℂ))) =
      ((Complex.digamma (1/4)).re-Real.log Real.pi) * (∫ x, Complex.normSq (F x)) +
      ∫ s in Ioi 0, ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
        zeroTranslationEnergy L (-L/2) u s := by
  exact mu_quadratic_of_memLp L u (continuous_memLp_window L hu) hE

/-- Conjugate-FIRST weighted polarization, with its minus-i coefficient.
Four finite quadratic integrands yield actual L1 of the mixed integrand. -/
lemma spectral_weight_polarization (w : ℝ → ℝ) (F G : ℝ → ℂ)
    (h1 : Integrable (fun t => w t*Complex.normSq (F t+G t)))
    (h2 : Integrable (fun t => w t*Complex.normSq (F t-G t)))
    (h3 : Integrable (fun t => w t*Complex.normSq (F t+Complex.I*G t)))
    (h4 : Integrable (fun t => w t*Complex.normSq (F t-Complex.I*G t))) :
    Integrable (fun t => (w t:ℂ)*conj (F t)*G t) ∧
    (∫ t, (w t:ℂ)*conj (F t)*G t) =
      qPol (∫ t, w t*Complex.normSq (F t+G t))
        (∫ t, w t*Complex.normSq (F t-G t))
        (∫ t, w t*Complex.normSq (F t+Complex.I*G t))
        (∫ t, w t*Complex.normSq (F t-Complex.I*G t)) := by
  have hp (t : ℝ) : (w t:ℂ)*conj (F t)*G t =
      qPol (w t*Complex.normSq (F t+G t)) (w t*Complex.normSq (F t-G t))
        (w t*Complex.normSq (F t+Complex.I*G t))
        (w t*Complex.normSq (F t-Complex.I*G t)) := by
    rw [mul_assoc, complex_polarization]
    unfold qPol
    push_cast
    ring
  have hcast (h : ℝ → ℝ) (hh : Integrable (fun t => w t*h t)) :
      Integrable (fun t => (w t:ℂ)*(h t:ℂ)) := by
    apply (Complex.ofRealCLM.integrable_comp hh).congr
    exact Eventually.of_forall fun t => Complex.ofReal_mul _ _
  have h1c := hcast (fun t => Complex.normSq (F t+G t)) h1
  have h2c := hcast (fun t => Complex.normSq (F t-G t)) h2
  have h3c := hcast (fun t => Complex.normSq (F t+Complex.I*G t)) h3
  have h4c := hcast (fun t => Complex.normSq (F t-Complex.I*G t)) h4
  have hi := ((h1c.sub h2c).sub ((h3c.sub h4c).const_mul Complex.I)).div_const 4
  refine ⟨hi.congr (Eventually.of_forall fun t => ?_), ?_⟩
  · simpa only [qPol, Pi.sub_apply] using (hp t).symm
  calc
    _ = ∫ t, qPol (w t*Complex.normSq (F t+G t)) (w t*Complex.normSq (F t-G t))
        (w t*Complex.normSq (F t+Complex.I*G t))
        (w t*Complex.normSq (F t-Complex.I*G t)) :=
      integral_congr_ae (Eventually.of_forall hp)
    _ = _ := integral_qPol h1c h2c h3c h4c
/-- Literal original-mu mixed form. No frequency-space equality is a premise:
it is obtained from the original extended owner on four actual finite profiles. -/
theorem mu_mixed_of_finite_energy (L : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hEf : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) f s) (Ioi 0))
    (hEg : IntegrableOn (fun s => ArchimedeanJumpDecomposition.archimedeanJumpDensity s *
      zeroTranslationEnergy L (-L/2) g s) (Ioi 0)) :
    let F := zeroExtension L (-L/2) f
    let G := zeroExtension L (-L/2) g
    Integrable (fun t : ℝ => (Zeta23.mu t:ℂ)*conj (Zeta23.paperFT F (t:ℂ))*
      Zeta23.paperFT G (t:ℂ)) ∧
    (∫ t : ℝ, (Zeta23.mu t:ℂ)*conj (Zeta23.paperFT F (t:ℂ))*
      Zeta23.paperFT G (t:ℂ)) =
      (((Complex.digamma (1/4)).re-Real.log Real.pi : ℝ) : ℂ) *
        (∫ x, conj (F x)*G x) +
      ∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s:ℂ)*
        ∫ x, conj (F x-F (x-s))*(G x-G (x-s)) := by
  dsimp only
  let F := zeroExtension L (-L/2) f
  let G := zeroExtension L (-L/2) g
  have hf0 : MemLp F 2 := zero_extension_memLp L (-L/2) f (continuous_memLp_window L hf)
  have hg0 : MemLp G 2 := zero_extension_memLp L (-L/2) g (continuous_memLp_window L hg)
  have hf1 : Integrable F := (integrable_indicator_iff measurableSet_Ioc).mpr
    ((continuous_memLp_window L hf).integrable (by norm_num))
  have hg1 : Integrable G := (integrable_indicator_iff measurableSet_Ioc).mpr
    ((continuous_memLp_window L hg).integrable (by norm_num))
  have hE (a b : ℂ) := profile_energy_integrable L f g hf hg hEf hEg a b
  have hFourier (a b : ℂ) (t : ℝ) :
      Zeta23.paperFT (zeroExtension L (-L/2) (a • f+b • g)) (t:ℂ) =
        a*Zeta23.paperFT F (t:ℂ)+b*Zeta23.paperFT G (t:ℂ) := by
    rw [zeroExtension_linear]
    exact paperFT_linear F G hf1 hg1 a b t
  have hQ (a b : ℂ) := mu_quadratic L (a • f+b • g)
    ((continuous_const.smul hf).add (continuous_const.smul hg)) (hE a b)
  have hW (a b : ℂ) : Integrable (fun t : ℝ => Zeta23.mu t *
      Complex.normSq (a*Zeta23.paperFT F (t:ℂ)+b*Zeta23.paperFT G (t:ℂ))) := by
    simpa only [hFourier] using (hQ a b).1
  have hspec := spectral_weight_polarization Zeta23.mu
    (fun t => Zeta23.paperFT F (t:ℂ)) (fun t => Zeta23.paperFT G (t:ℂ))
    (by simpa using hW 1 1) (by simpa [sub_eq_add_neg] using hW 1 (-1))
    (by simpa using hW 1 Complex.I) (by simpa [sub_eq_add_neg] using hW 1 (-Complex.I))
  have hspatial := integral_polarization hf0 hg0
  simp only [integral_complex_ofReal] at hspatial
  have hgap := weighted_linear_polarization volume (volume.restrict (Ioi 0))
    (fun s => zeroGapMap L (-L/2) s)
    ArchimedeanJumpDecomposition.archimedeanJumpDensity f g
    (fun s => hf0.sub (hf0.comp_measurePreserving (measurePreserving_sub_right volume s)))
    (fun s => hg0.sub (hg0.comp_measurePreserving (measurePreserving_sub_right volume s)))
    (by simpa only [one_smul, zeroTranslationEnergy, zeroGapMap,
      LinearMap.coe_mk, AddHom.coe_mk, IntegrableOn] using hE 1 1)
    (by simpa only [one_smul, neg_one_smul, sub_eq_add_neg,
      zeroTranslationEnergy, zeroGapMap, LinearMap.coe_mk, AddHom.coe_mk,
      IntegrableOn] using hE 1 (-1))
    (by simpa only [one_smul, zeroTranslationEnergy, zeroGapMap,
      LinearMap.coe_mk, AddHom.coe_mk, IntegrableOn] using hE 1 Complex.I)
    (by simpa only [one_smul, neg_smul, sub_eq_add_neg,
      zeroTranslationEnergy, zeroGapMap, LinearMap.coe_mk, AddHom.coe_mk,
      IntegrableOn] using hE 1 (-Complex.I))
  have hQeq (a b : ℂ) := (hQ a b).2
  simp_rw [hFourier] at hQeq
  simp_rw [zeroExtension_linear] at hQeq
  have hQ1 := hQeq 1 1
  have hQ2 := hQeq 1 (-1)
  have hQ3 := hQeq 1 Complex.I
  have hQ4 := hQeq 1 (-Complex.I)
  simp only [one_smul, one_mul, neg_one_smul,
    neg_one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    neg_mul, sub_eq_add_neg] at hQ1 hQ2 hQ3 hQ4
  simp only [← Complex.ofReal_mul, integral_complex_ofReal] at hspec hgap
  dsimp only [zeroGapMap, LinearMap.coe_mk, AddHom.coe_mk] at hgap
  simp only [zeroTranslationEnergy] at hQ1 hQ2 hQ3 hQ4
  simp only [sub_eq_add_neg, neg_mul] at hspec hspatial hgap
  refine ⟨hspec.1, ?_⟩
  rw [hspec.2, hQ1, hQ2, hQ3, hQ4]
  simp only [sub_eq_add_neg, neg_mul]
  rw [hspatial, hgap.2]
  unfold qPol
  push_cast
  simp only [F, G]
  simp only [Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg, neg_smul, neg_mul]
  ring

/-- The actual whole-line zero-mode inner product equals the literal window one. -/
lemma zeroMode_inner (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    (∫ x, conj (zeroMode L m x)*zeroMode L n x) = if m=n then (1:ℂ) else 0 := by
  have hp : (fun x => conj (zeroMode L m x)*zeroMode L n x) =
      (window L).indicator (fun x => conj (mode L m x)*mode L n x) := by
    funext x
    by_cases hx : x ∈ window L <;> simp [zeroMode, hx]
  rw [hp, integral_indicator (show MeasurableSet (window L) from measurableSet_Ioc)]
  exact mode_inner L m n

/-- Original mu bridge for ALL integer indices, including diagonal/zero/opposite.
The complete Fourier integral is literally Zeta23.mu, with its PLUS convention. -/
theorem mu_pairing_bridge (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    Integrable (fun t : ℝ => (Zeta23.mu t:ℂ)*
      conj (Zeta23.paperFT (zeroMode L m) (t:ℂ))*Zeta23.paperFT (zeroMode L n) (t:ℂ)) ∧
    (∫ t : ℝ, (Zeta23.mu t:ℂ)*conj (Zeta23.paperFT (zeroMode L m) (t:ℂ))*
      Zeta23.paperFT (zeroMode L n) (t:ℂ)) =
      (((Complex.digamma (1/4)).re-Real.log Real.pi : ℝ) : ℂ) *
        (if m=n then 1 else 0) +
      ∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s:ℂ)*
        displacementPair L m n s := by
  have h := mu_mixed_of_finite_energy L (mode L m) (mode L n)
    (mode_continuous L m) (mode_continuous L n)
    (mode_actual_energy_integrable L m) (mode_actual_energy_integrable L n)
  simp only [← zeroMode_eq, zeroMode_inner] at h
  simpa only [displacementPair] using h

/-- The original boundaryEntry series, unchanged from the literal matrix target.
This is a formula for the correction; its equality to the actual operator is
proved below by consuming the one-rate image theorem and both complete exchanges. -/
def boundaryEntry (L : ℝ) (m n : ℤ) : ℝ :=
  (2/L)*(-1 : ℝ)^(m+n) * ∑' j : ℕ,
    (1-Real.exp (-rate j*L))*(rate j^2-omega L m*omega L n) /
      ((rate j^2+omega L m^2)*(rate j^2+omega L n^2))

/-- Every zero layer is individually L1 and its integral-norm series is finite.
This is extracted from the existing full absolute owner, not from cancellation. -/
lemma zero_complete_layers (L : ℝ) [Fact (0 < L)] (m n : ℤ) :
    (∀ j : ℕ, IntegrableOn (fun s => (Real.exp (-rate j*s):ℂ)*displacementPair L m n s)
      (Ioi 0)) ∧
    Summable (fun j : ℕ => ∫ s in Ioi 0, ‖(Real.exp (-rate j*s):ℂ)*displacementPair L m n s‖) ∧
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s:ℂ)*
      displacementPair L m n s) =
      ∑' j : ℕ, ∫ s in Ioi 0, (Real.exp (-rate j*s):ℂ)*displacementPair L m n s := by
  have hz := modes_complete_rate_interchange L m n
  refine ⟨?_, hz.1, hz.2⟩
  intro j
  have hj := ((modes_complete_rate_joint_absolute L m n).1 j).integral_prod_left
  simpa only [IntegrableOn, integral_const_mul, displacementPair] using hj

/-- One rate, with both signed moments now evaluated and consumed. -/
theorem rate_entry (L b : ℝ) [hL : Fact (0 < L)] (hb : 0 < b) (m n : ℤ) :
    (∫ s in Ioi 0, (Real.exp (-b*s):ℂ)*displacementPair L m n s) =
      (∫ s in Ioi 0, (Real.exp (-b*s):ℂ)*periodicPair L m n s) +
      (((2/L)*(-1 : ℝ)^(m+n) *
        ((1-Real.exp (-b*L))*(b^2-omega L m*omega L n) /
          ((b^2+omega L m^2)*(b^2+omega L n^2))) : ℝ) : ℂ) := by
  rw [rate_image_pairing L b hb m n, mode_image_form L b hL.out hb m n]

/-- The complete actual jump pairing equals periodic energy plus the entire
absolutely convergent boundary series. No separate divergent 2/b_j sum occurs. -/
theorem full_rate_entry (L : ℝ) [hL : Fact (0 < L)] (m n : ℤ) :
    (∫ s in Ioi 0, (ArchimedeanJumpDecomposition.archimedeanJumpDensity s:ℂ)*
      displacementPair L m n s) =
      (if m=n then (FormCore.LineFourier.actualIncrement (omega L n):ℂ) else 0) +
        (boundaryEntry L m n:ℂ) := by
  have hz := zero_complete_layers L m n
  have hp := periodic_complete_rate_interchange L m n
  have hps : Summable (fun j : ℕ =>
      ∫ s in Ioi 0, (Real.exp (-rate j*s):ℂ)*periodicPair L m n s) := by
    apply Summable.of_norm_bounded hp.2.1
    intro j
    exact norm_integral_le_integral_norm _
  have hbabs := boundary_series_absolutely_summable L hL.out m n
  have hraw : Summable (fun j : ℕ =>
      (1-Real.exp (-rate j*L))*(rate j^2-omega L m*omega L n) /
        ((rate j^2+omega L m^2)*(rate j^2+omega L n^2))) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using hbabs)
  have hscaled := hraw.mul_left ((2/L)*(-1 : ℝ)^(m+n))
  have hbs : Summable (fun j : ℕ =>
      (((2/L)*(-1 : ℝ)^(m+n) *
        ((1-Real.exp (-rate j*L))*(rate j^2-omega L m*omega L n) /
          ((rate j^2+omega L m^2)*(rate j^2+omega L n^2))) : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasSum hscaled.hasSum).summable
  rw [hz.2.2]
  simp_rw [rate_entry L (rate _) (rate_pos _) m n]
  rw [hps.tsum_add hbs, ← hp.2.2, (periodic_mixed_integral L m n).2]
  rw [← Complex.ofReal_tsum]
  congr 2
  rw [tsum_mul_left]
  rfl

end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation
