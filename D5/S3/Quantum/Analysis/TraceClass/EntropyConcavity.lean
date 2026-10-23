/- GID: D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/EntropyConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-weight quantitative concavity of extended spectral entropy in the genuine trace norm. -/

import D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import Mathlib.Analysis.Convex.Strong

noncomputable section
open scoped ComplexOrder ENNReal
set_option backward.isDefEq.respectTransparency false
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem mixture_positive (rho sigma : Reference H) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (((a : ℂ) • rho.1 + (b : ℂ) • sigma.1 : TraceClass H).1) := by
  change 0 ≤ (a : ℂ) • rho.1.1 + (b : ℂ) • sigma.1.1
  rw [Complex.coe_smul, Complex.coe_smul]
  exact add_nonneg (smul_nonneg ha rho.2.1) (smul_nonneg hb sigma.2.1)

private theorem mixture_trace (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    {a b : ℝ} (hab : a + b = 1) :
    (trace (((a : ℂ) • rho.1 + (b : ℂ) • sigma.1 : TraceClass H).1)
      (TraceClass.isTraceClass_coe _)).re = 1 := by
  change (trace ((a : ℂ) • rho.1.1 + (b : ℂ) • sigma.1.1) _).re = 1
  rw [trace_add (isTraceClass_smul _ (TraceClass.isTraceClass_coe rho.1))
    (isTraceClass_smul _ (TraceClass.isTraceClass_coe sigma.1)),
    trace_smul _ (TraceClass.isTraceClass_coe rho.1),
    trace_smul _ (TraceClass.isTraceClass_coe sigma.1), Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hr, hs, mul_one]
  exact hab

/-- The actual convex mixture, normalized through its actual trace. -/
def mixture (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : Reference H :=
  ⟨(a : ℂ) • rho.1 + (b : ℂ) • sigma.1, mixture_positive rho sigma ha hb,
    density_le_one _ (mixture_positive rho sigma ha hb) (mixture_trace rho sigma hr hs hab)⟩

/-- Quantitative entropy concavity for all weights, including zero weights and infinite entropies.
The norm is the trace-class Banach norm and no commutation or faithfulness is required. -/
theorem spectralEntropy_mixture (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * spectralEntropy rho + ENNReal.ofReal b * spectralEntropy sigma +
        ENNReal.ofReal (a * b * ‖rho.1 - sigma.1‖ ^ 2 / 4) ≤
      spectralEntropy (mixture rho sigma hr hs a b ha hb hab) := by
  let tau := mixture rho sigma hr hs a b ha hb hab
  have ht : (trace tau.1.1 (TraceClass.isTraceClass_coe tau.1)).re = 1 :=
    mixture_trace rho sigma hr hs hab
  have hrt := spectralEntropy_add_traceNorm_sq_le_energy rho tau hr ht
  have hst := spectralEntropy_add_traceNorm_sq_le_energy sigma tau hs ht
  have hdist1 : ‖rho.1 - tau.1‖ = b * ‖rho.1 - sigma.1‖ := by
    have h : rho.1 - tau.1 = (b : ℂ) • (rho.1 - sigma.1) := by
      dsimp [tau, mixture]
      have ha' : a = 1 - b := by linarith
      rw [ha', sub_smul, one_smul, smul_sub]
      abel
    rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hdist2 : ‖sigma.1 - tau.1‖ = a * ‖rho.1 - sigma.1‖ := by
    have h : sigma.1 - tau.1 = (a : ℂ) • (sigma.1 - rho.1) := by
      dsimp [tau, mixture]
      have hb' : b = 1 - a := by linarith
      rw [hb', sub_smul, one_smul, smul_sub]
      abel
    rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, norm_sub_rev]
  have hreward : ENNReal.ofReal a * ENNReal.ofReal (‖rho.1 - tau.1‖ ^ 2 / 4) +
      ENNReal.ofReal b * ENNReal.ofReal (‖sigma.1 - tau.1‖ ^ 2 / 4) =
      ENNReal.ofReal (a * b * ‖rho.1 - sigma.1‖ ^ 2 / 4) := by
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_add (by positivity) (by positivity), hdist1, hdist2]
    congr 1
    calc
      _ = a * b * ‖rho.1 - sigma.1‖ ^ 2 / 4 * (a + b) := by ring
      _ = _ := by rw [hab, mul_one]
  calc
    _ = ENNReal.ofReal a * (spectralEntropy rho + ENNReal.ofReal (‖rho.1 - tau.1‖ ^ 2 / 4)) +
        ENNReal.ofReal b * (spectralEntropy sigma + ENNReal.ofReal (‖sigma.1 - tau.1‖ ^ 2 / 4)) := by
      rw [mul_add, mul_add, ← hreward]
      ac_rfl
    _ ≤ ENNReal.ofReal a * spectralEnergy tau rho.1 +
        ENNReal.ofReal b * spectralEnergy tau sigma.1 :=
      add_le_add (mul_le_mul_right hrt _) (mul_le_mul_right hst _)
    _ = spectralEntropy tau := by
      rw [← spectralEnergy_nonneg_linear tau rho.1 sigma.1 rho.2.1 sigma.2.1 a b ha hb]
      exact spectralEnergy_self tau

/-- Real entropy on the positive contraction domain, extended by zero outside it. -/
def realEntropy (rho : TraceClass H) : ℝ := by
  classical
  exact if h : 0 ≤ rho.1 ∧ rho.1 ≤ 1 then (spectralEntropy ⟨rho, h⟩).toReal else 0

theorem realEntropy_reference (rho : Reference H) :
    realEntropy rho.1 = (spectralEntropy rho).toReal := by
  simp only [realEntropy, dif_pos rho.2]

/-- On every convex family of actual normalized positive densities with finite entropy,
the full weighted inequality gives the Mathlib modulus one half. -/
theorem strongConcaveOn_realEntropy {A : Set (TraceClass H)} (hA : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (h : rho ∈ A), spectralEntropy
      (⟨rho, hp rho h, density_le_one rho (hp rho h) (ht rho h)⟩ : Reference H) ≠ ∞) :
    StrongConcaveOn A (1 / 2) realEntropy := by
  refine ⟨hA, ?_⟩
  intro x hx y hy a b ha hb hab
  let rho : Reference H := ⟨x, hp x hx, density_le_one x (hp x hx) (ht x hx)⟩
  let sigma : Reference H := ⟨y, hp y hy, density_le_one y (hp y hy) (ht y hy)⟩
  let tau := mixture rho sigma (ht x hx) (ht y hy) a b ha hb hab
  have hm : a • x + b • y ∈ A := hA hx hy ha hb hab
  have heq : tau.1 = a • x + b • y := by
    change (a : ℂ) • x + (b : ℂ) • y = _
    rw [Complex.coe_smul, Complex.coe_smul]
  have hft : spectralEntropy tau ≠ ∞ := by
    convert hf (a • x + b • y) hm using 1
    congr 1
  have h := ENNReal.toReal_mono hft (spectralEntropy_mixture rho sigma
    (ht x hx) (ht y hy) a b ha hb hab)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hf x hx), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf y hy)⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf x hx))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf y hy)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal (by positivity)] at h
  rw [← realEntropy_reference rho, ← realEntropy_reference sigma, ← realEntropy_reference tau,
    heq] at h
  change a * realEntropy x + b * realEntropy y + a * b * ((1 / 2 : ℝ) / 2 * ‖x - y‖ ^ 2) ≤ _
  convert h using 1 <;> dsimp [rho, sigma] <;> ring

#print axioms spectralEntropy_mixture
#print axioms strongConcaveOn_realEntropy
end QuantumLogEnergy
