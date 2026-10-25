/- GID: D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-bare-quarter-graph-closure)
   anchors: []
   utility: none
   digest: Actual quarter-digamma graph equivalence from finite resolvents and Hankel control. -/

/- Actual same-source L1/L2 bare-quarter spectral closure.
Finite identities and the complete Hankel square series pay both directions
of the graph equivalence; the reflected cross domain is derived from it.
Organizational suppliers are consumed by the full actual Gamma owner.
No standalone admission or successful native verification is inferred here. -/

import D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2
import D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
open scoped Topology ComplexConjugate FourierTransform ENNReal

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

private theorem continuous_unitarySourceFourier {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (unitarySourceFourier f) := by
  unfold unitarySourceFourier
  exact continuous_const.mul
    ((D5.S3.Weil.ZetaGamma.FormCore.LineFourier.continuous_raw_fourier hf).comp
      (by fun_prop))

private theorem unitarySourceFourier_eq_angular (f : ℝ → ℂ) (ξ : ℝ) :
    unitarySourceFourier f ξ =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹ *
        D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angularFourier f (-ξ) := by
  rfl

private theorem unitary_normalizing_enorm_sq :
    ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹‖ₑ ^ 2 =
      ENNReal.ofReal (1 / (2 * Real.pi)) := by
  have hp : 0 ≤ 2 * Real.pi := by positivity
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp]
  simp only [one_div]

/-- Canonical source Plancherel is a consequence of the existing actual
angular theorem. No Fourier-energy equality is supplied as a hypothesis. -/
private theorem unitarySourceFourier_extended_plancherel {f : ℝ → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    (∫⁻ ξ : ℝ, ‖unitarySourceFourier f ξ‖ₑ ^ 2) =
      ∫⁻ t : ℝ, ‖f t‖ₑ ^ 2 := by
  calc
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ ξ : ℝ,
          ‖D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angularFourier f (-ξ)‖ₑ ^ 2 := by
      simp_rw [unitarySourceFourier_eq_angular, enorm_mul, mul_pow,
        unitary_normalizing_enorm_sq]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ ξ : ℝ,
          ‖D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angularFourier f ξ‖ₑ ^ 2 := by
      congr 1
      exact lintegral_neg_eq_self (fun ξ : ℝ =>
        ‖D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angularFourier f ξ‖ₑ ^ 2)
    _ = _ :=
      (D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angular_extended_plancherel hf₁ hf₂).symm


theorem unitarySourceFourier_squared_integrable {f : ℝ → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    Integrable (fun ξ : ℝ => ‖unitarySourceFourier f ξ‖ ^ 2) volume := by
  have hspatial : Integrable (fun t : ℝ => ‖f t‖ ^ 2) volume :=
    hf₂.integrable_norm_pow (p := 2) (by norm_num)
  have hspatialNN : ∀ᵐ t : ℝ ∂volume, 0 ≤ ‖f t‖ ^ 2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hspatialFinite :
      (∫⁻ t : ℝ, ‖f t‖ₑ ^ 2) < ⊤ := by
    calc
      _ = ∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun t => by
          dsimp only
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ < ⊤ := (hasFiniteIntegral_iff_ofReal hspatialNN).1 hspatial.hasFiniteIntegral
  have hfreqFinite :
      (∫⁻ ξ : ℝ, ENNReal.ofReal (‖unitarySourceFourier f ξ‖ ^ 2)) < ⊤ := by
    calc
      _ = ∫⁻ ξ : ℝ, ‖unitarySourceFourier f ξ‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun ξ => by
          dsimp only
          rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ = ∫⁻ t : ℝ, ‖f t‖ₑ ^ 2 :=
        unitarySourceFourier_extended_plancherel hf₁ hf₂
      _ < ⊤ := hspatialFinite
  refine ⟨((continuous_unitarySourceFourier hf₁).norm.pow 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun ξ => sq_nonneg ‖unitarySourceFourier f ξ‖)).2 hfreqFinite

/-- Real mass equality follows from the actual extended Plancherel supplier. -/
private theorem actual_unitary_mass_integral {f : ℝ → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    (∫ ξ : ℝ, ‖unitarySourceFourier f ξ‖ ^ 2) = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  have hF := unitarySourceFourier_squared_integrable hf₁ hf₂
  have hf := hf₂.integrable_norm_pow (p := 2) (by norm_num)
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ξ => sq_nonneg ‖unitarySourceFourier f ξ‖)
      hF.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun t => sq_nonneg ‖f t‖) hf.aestronglyMeasurable]
  congr 1
  calc
    _ = ∫⁻ ξ : ℝ, ‖unitarySourceFourier f ξ‖ₑ ^ 2 := by
      simp_rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    _ = ∫⁻ t : ℝ, ‖f t‖ₑ ^ 2 := unitarySourceFourier_extended_plancherel hf₁ hf₂
    _ = _ := by simp_rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

private theorem source_zero_l1 {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (zeroExtension u) volume :=
  (integrable_indicator_iff measurableSet_Ioi).2 hu

private theorem source_zero_l2 {u : ℝ → ℂ} (hu : MemLp u 2 halfline) :
    MemLp (zeroExtension u) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hu

private theorem source_reflect_l1 {f : ℝ → ℂ} (hf : Integrable f volume) :
    Integrable (fun t : ℝ => f (-t)) volume :=
  (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hf

private theorem source_reflect_l2 {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun t : ℝ => f (-t)) 2 volume :=
  hf.comp_measurePreserving (Measure.measurePreserving_neg volume)

private theorem source_unitary_reflect (f : ℝ → ℂ) (ξ : ℝ) :
    unitarySourceFourier (fun t : ℝ => f (-t)) ξ = unitarySourceFourier f (-ξ) := by
  unfold unitarySourceFourier
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f
    (-ξ / (2 * Real.pi))
  change 𝓕 (fun t : ℝ => f (-t)) (-ξ / (2 * Real.pi)) =
    𝓕 f (-(-ξ / (2 * Real.pi))) at h
  rw [h]
  congr 2
  ring

private theorem source_unitary_add {f g : ℝ → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume) (ξ : ℝ) :
    unitarySourceFourier (fun t => f t + g t) ξ =
      unitarySourceFourier f ξ + unitarySourceFourier g ξ := by
  have hraw :
      𝓕 (fun t => f t + g t) (-ξ / (2 * Real.pi)) =
        𝓕 f (-ξ / (2 * Real.pi)) + 𝓕 g (-ξ / (2 * Real.pi)) := by
    exact congrFun
      (VectorFourier.fourierIntegral_add (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner hf hg)
      (-ξ / (2 * Real.pi))
  simp only [unitarySourceFourier, hraw, mul_add]

private theorem actual_unitary_l2 {f : ℝ → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    MemLp (unitarySourceFourier f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_unitarySourceFourier hf₁).aestronglyMeasurable).2
      (unitarySourceFourier_squared_integrable hf₁ hf₂)

private theorem source_norm_add_sq (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 +
      2 * ((starRingEnd ℂ) z * w).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Actual spectral correlation domain, derived from spatial L1∩L2. -/
theorem actual_unweighted_reflected_cross_integrable {u : ℝ → ℂ}
    (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    Integrable (fun ξ : ℝ =>
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume := by
  have hU₁ := source_zero_l1 hu₁
  have hU₂ := source_zero_l2 hu₂
  have hV₁ := source_reflect_l1 hU₁
  have hV₂ := source_reflect_l2 hU₂
  have hC := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.l2_complex_correlation_integrable
    (actual_unitary_l2 hU₁ hU₂) (actual_unitary_l2 hV₁ hV₂)
  simpa only [source_unitary_reflect] using hC

/-- The constant multiplier has zero real cross, proved by real Plancherel
polarization and the actual disjoint half-line supports. No trace is needed. -/
theorem actual_constant_reflected_cross_re_zero {u : ℝ → ℂ}
    (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    (∫ ξ : ℝ,
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)).re = 0 := by
  let U : ℝ → ℂ := zeroExtension u
  let V : ℝ → ℂ := fun t => U (-t)
  let E : ℝ → ℂ := fun t => U t + V t
  have hU₁ : Integrable U volume := source_zero_l1 hu₁
  have hU₂ : MemLp U 2 volume := source_zero_l2 hu₂
  have hV₁ : Integrable V volume := source_reflect_l1 hU₁
  have hV₂ : MemLp V 2 volume := source_reflect_l2 hU₂
  have hE₁ : Integrable E volume := hU₁.add hV₁
  have hE₂ : MemLp E 2 volume := hU₂.add hV₂
  have hUm := hU₂.integrable_norm_pow (p := 2) (by norm_num)
  have hVm := hV₂.integrable_norm_pow (p := 2) (by norm_num)
  have hSpatial : (∫ t : ℝ, ‖E t‖ ^ 2) =
      (∫ t : ℝ, ‖U t‖ ^ 2) + ∫ t : ℝ, ‖V t‖ ^ 2 := by
    rw [← integral_add hUm hVm]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      by_cases ht : 0 < t
      · have hn : ¬ 0 < -t := by linarith
        simp [E, V, U, zeroExtension, ht, hn]
      · simp [E, V, U, zeroExtension, ht]
  have hC := actual_unweighted_reflected_cross_integrable hu₁ hu₂
  have hUF := unitarySourceFourier_squared_integrable hU₁ hU₂
  have hVF := unitarySourceFourier_squared_integrable hV₁ hV₂
  have hFreq : (∫ ξ : ℝ, ‖unitarySourceFourier E ξ‖ ^ 2) =
      (∫ ξ : ℝ, ‖unitarySourceFourier U ξ‖ ^ 2) +
        (∫ ξ : ℝ, ‖unitarySourceFourier V ξ‖ ^ 2) +
          2 * (∫ ξ : ℝ,
            (starRingEnd ℂ) (unitarySourceFourier U ξ) *
              unitarySourceFourier U (-ξ)).re := by
    calc
      _ = ∫ ξ : ℝ,
          (‖unitarySourceFourier U ξ‖ ^ 2 + ‖unitarySourceFourier V ξ‖ ^ 2) +
            2 * ((starRingEnd ℂ) (unitarySourceFourier U ξ) *
              unitarySourceFourier U (-ξ)).re := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          dsimp only
          rw [show E = fun t => U t + V t from rfl,
            source_unitary_add hU₁ hV₁, source_norm_add_sq]
          simp only [V, source_unitary_reflect]
      _ = _ := by
        have hSum : Integrable (fun ξ => ‖unitarySourceFourier U ξ‖ ^ 2 +
            ‖unitarySourceFourier V ξ‖ ^ 2) volume := hUF.add hVF
        have hTerm : Integrable (fun ξ => 2 * ((starRingEnd ℂ)
            (unitarySourceFourier U ξ) * unitarySourceFourier U (-ξ)).re) volume :=
          hC.re.const_mul 2
        rw [integral_add hSum hTerm, integral_add hUF hVF,
          integral_const_mul]
        have hre : (∫ ξ : ℝ, ((starRingEnd ℂ) (unitarySourceFourier U ξ) *
            unitarySourceFourier U (-ξ)).re) =
            (∫ ξ : ℝ, (starRingEnd ℂ) (unitarySourceFourier U ξ) *
              unitarySourceFourier U (-ξ)).re := integral_re hC
        rw [hre]
  rw [actual_unitary_mass_integral hE₁ hE₂,
    actual_unitary_mass_integral hU₁ hU₂,
    actual_unitary_mass_integral hV₁ hV₂] at hFreq
  change (∫ ξ : ℝ, (starRingEnd ℂ) (unitarySourceFourier U ξ) *
    unitarySourceFourier U (-ξ)).re = 0
  linarith

/-- Literal bare quarter increment, at a positive Laplace rate. -/
private def actualBareQuarterIncrement (c ξ : ℝ) : ℝ :=
  1 / c - c / (ξ ^ 2 + c ^ 2)

/-- Each finite increment's real cross is minus half the literal Laplace
square. Constant cancellation and resolvent inversion are actual suppliers. -/
private theorem actual_bare_quarter_increment_cross {c : ℝ} (hc : 0 < c)
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    Integrable (fun ξ : ℝ => (actualBareQuarterIncrement c ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, (actualBareQuarterIncrement c ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)).re =
      -Complex.normSq (∫ t : ℝ, (Real.exp (-c * t) : ℂ) * u t ∂halfline) / 2 := by
  let C : ℝ → ℂ := fun ξ =>
    (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
      unitarySourceFourier (zeroExtension u) (-ξ)
  have hC : Integrable C volume := actual_unweighted_reflected_cross_integrable hu₁ hu₂
  obtain ⟨_, hR₀, hRi₀⟩ := actual_resolvent_reflected_cross_laplace_square hc hu₁
  have hR : Integrable (fun ξ => actualResolventSymbol c ξ * C ξ) volume := by
    convert hR₀ using 1
    funext ξ
    exact (mul_assoc _ _ _).symm
  have hRi : (∫ ξ : ℝ, actualResolventSymbol c ξ * C ξ) =
      (Complex.normSq (∫ t : ℝ, (Real.exp (-c * t) : ℂ) * u t ∂halfline) : ℂ) /
        ((2 * c : ℝ) : ℂ) := by
    convert hRi₀ using 1
    congr 1
    funext ξ
    exact (mul_assoc _ _ _).symm
  have hPoint (ξ : ℝ) :
      (actualBareQuarterIncrement c ξ : ℂ) * C ξ =
        (1 / c : ℂ) * C ξ - (c : ℂ) * (actualResolventSymbol c ξ * C ξ) := by
    simp only [actualBareQuarterIncrement, actualResolventSymbol]
    push_cast
    ring
  have hInt : Integrable (fun ξ : ℝ =>
      (actualBareQuarterIncrement c ξ : ℂ) * C ξ) volume := by
    simp_rw [hPoint]
    exact (hC.const_mul _).sub (hR.const_mul _)
  refine ⟨by simpa only [C, mul_assoc] using hInt, ?_⟩
  have hZero := actual_constant_reflected_cross_re_zero hu₁ hu₂
  simp only [mul_assoc]
  change (∫ ξ : ℝ, (actualBareQuarterIncrement c ξ : ℂ) * C ξ).re = _
  simp_rw [hPoint]
  rw [integral_sub (hC.const_mul _) (hR.const_mul _),
    integral_const_mul, integral_const_mul, hRi]
  have hZero' : (∫ ξ : ℝ, C ξ).re = 0 := hZero
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.one_re, Complex.one_im, zero_div, zero_mul, mul_zero, sub_zero, hZero']
  field_simp [hc.ne']
  <;> ring

/-- Finite bare digamma approximant; no renormalizing constant is added. -/
private def actualBareQuarterPartial (N : ℕ) (ξ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, actualBareQuarterIncrement ((n : ℝ) + 1 / 4) ξ

private theorem actual_bare_quarter_partial_cross (N : ℕ)
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    Integrable (fun ξ : ℝ => (actualBareQuarterPartial N ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, (actualBareQuarterPartial N ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)).re =
      -(∑ n ∈ Finset.range N, Complex.normSq
        (∫ t : ℝ, (Real.exp (-((n : ℝ) + 1 / 4) * t) : ℂ) * u t ∂halfline)) / 2 := by
  let A : ℕ → ℝ → ℂ := fun n ξ =>
    (actualBareQuarterIncrement ((n : ℝ) + 1 / 4) ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)
  have hA (n : ℕ) : Integrable (A n) volume :=
    (actual_bare_quarter_increment_cross (by positivity) hu₁ hu₂).1
  have hPoint (ξ : ℝ) :
      (actualBareQuarterPartial N ξ : ℂ) *
          (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
            unitarySourceFourier (zeroExtension u) (-ξ) =
        ∑ n ∈ Finset.range N, A n ξ := by
    simp only [actualBareQuarterPartial, Complex.ofReal_sum, Finset.sum_mul, A]
  have hInt : Integrable (fun ξ => ∑ n ∈ Finset.range N, A n ξ) volume :=
    integrable_finsetSum _ fun n _ => hA n
  refine ⟨hInt.congr (Eventually.of_forall fun ξ => (hPoint ξ).symm), ?_⟩
  simp_rw [hPoint]
  rw [integral_finsetSum _ (fun n _ => hA n), Complex.re_sum]
  calc
    _ = ∑ n ∈ Finset.range N, -Complex.normSq
        (∫ t : ℝ, (Real.exp (-((n : ℝ) + 1 / 4) * t) : ℂ) * u t ∂halfline) / 2 := by
      apply Finset.sum_congr rfl
      intro n _
      exact (actual_bare_quarter_increment_cross (by positivity) hu₁ hu₂).2
    _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]

private theorem actual_bare_quarter_increment_nonneg {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    0 ≤ actualBareQuarterIncrement c ξ := by
  unfold actualBareQuarterIncrement
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < ξ ^ 2 + c ^ 2) hc).2
  nlinarith [sq_nonneg ξ]

private theorem actual_bare_quarter_increment_le {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    actualBareQuarterIncrement c ξ ≤ 1 / c := by
  unfold actualBareQuarterIncrement
  have h : 0 ≤ c / (ξ ^ 2 + c ^ 2) := by positivity
  linarith

private theorem actual_bare_quarter_partial_nonneg (N : ℕ) (ξ : ℝ) :
    0 ≤ actualBareQuarterPartial N ξ :=
  Finset.sum_nonneg fun n _ => actual_bare_quarter_increment_nonneg (by positivity) ξ

private theorem actual_bare_quarter_partial_continuous (N : ℕ) :
    Continuous (actualBareQuarterPartial N) := by
  unfold actualBareQuarterPartial actualBareQuarterIncrement
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.sub (continuous_const.div (by fun_prop) (fun ξ => by positivity))

/-- Finite spectral energies have their actual domains from the bounded
approximants and actual Fourier L2 mass; no infinite graph is assumed. -/
private theorem actual_bare_quarter_partial_energy_integrable (N : ℕ)
    {f : ℝ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    Integrable (fun ξ => actualBareQuarterPartial N ξ *
      ‖unitarySourceFourier f ξ‖ ^ 2) volume := by
  let B : ℝ := ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1 / 4)
  have hM := unitarySourceFourier_squared_integrable hf₁ hf₂
  have hCont := (actual_bare_quarter_partial_continuous N).mul
    ((continuous_unitarySourceFourier hf₁).norm.pow 2)
  apply (hM.const_mul B).mono' hCont.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (actual_bare_quarter_partial_nonneg N ξ)
      (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Finset.sum_le_sum fun n _ => actual_bare_quarter_increment_le (by positivity) ξ

/-- Elementary monotone-integrability closure used only after all actual
finite-stage identities have been paid. It does not assume an energy identity. -/
private theorem nonnegative_monotone_integrable_of_uniform_integral_bound
    {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {B : ℝ}
    (hf : ∀ n, Integrable (f n) volume)
    (hpos : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ x, Monotone fun n => f n x)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hB : ∀ n, (∫ x, f n x) ≤ B) : Integrable F volume := by
  have hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (F x))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hf n).aemeasurable.ennreal_ofReal)
    · exact Eventually.of_forall fun x n m hnm =>
        ENNReal.ofReal_le_ofReal (hmono x hnm)
    · exact Eventually.of_forall fun x =>
        (ENNReal.continuous_ofReal.tendsto _).comp (hconv x)
  have hBound : (∫⁻ x, ENNReal.ofReal (F x)) ≤ ENNReal.ofReal B := by
    apply le_of_tendsto' hlim
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n)
      (Eventually.of_forall (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hFpos : ∀ x, 0 ≤ F x := fun x =>
    ge_of_tendsto' (hconv x) (fun n => hpos n x)
  have hFm : AEStronglyMeasurable F volume :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hf n).aestronglyMeasurable)
      (Eventually.of_forall hconv)
  exact ⟨hFm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hFpos)).2
    (lt_of_le_of_lt hBound ENNReal.ofReal_lt_top)⟩

private theorem actual_bare_quarter_partial_even (N : ℕ) (ξ : ℝ) :
    actualBareQuarterPartial N (-ξ) = actualBareQuarterPartial N ξ := by
  simp only [actualBareQuarterPartial, actualBareQuarterIncrement, neg_sq]

private theorem actual_bare_quarter_partial_mono (ξ : ℝ) :
    Monotone fun N => actualBareQuarterPartial N ξ := by
  apply monotone_nat_of_le_succ
  intro N
  simp only [actualBareQuarterPartial, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (actual_bare_quarter_increment_nonneg (by positivity) ξ)

/-- This representative equals the literal even extension almost everywhere. -/
def actualEvenZeroExtension (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  zeroExtension u t + zeroExtension u (-t)

theorem actual_even_zero_fourier {u : ℝ → ℂ}
    (hu : Integrable u halfline) (ξ : ℝ) :
    unitarySourceFourier (actualEvenZeroExtension u) ξ =
      unitarySourceFourier (zeroExtension u) ξ +
        unitarySourceFourier (zeroExtension u) (-ξ) := by
  unfold actualEvenZeroExtension
  rw [source_unitary_add (source_zero_l1 hu) (source_reflect_l1 (source_zero_l1 hu)),
    source_unitary_reflect]

/-- Actual finite spectral energy identity. The right side has precisely
the same u and the bare rates 1/4+n; no graph, energy equality, or jump
Fubini theorem is a premise. -/
private theorem actual_bare_quarter_partial_energy_identity (N : ℕ)
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    (∫ ξ : ℝ, actualBareQuarterPartial N ξ *
      ‖unitarySourceFourier (actualEvenZeroExtension u) ξ‖ ^ 2) =
        2 * (∫ ξ : ℝ, actualBareQuarterPartial N ξ *
          ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) -
        ∑ n ∈ Finset.range N, Complex.normSq
          (∫ t : ℝ, (Real.exp (-((n : ℝ) + 1 / 4) * t) : ℂ) * u t ∂halfline) := by
  let U := zeroExtension u
  let A : ℝ → ℝ := fun ξ => actualBareQuarterPartial N ξ *
    ‖unitarySourceFourier U ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ => actualBareQuarterPartial N ξ *
    ‖unitarySourceFourier U (-ξ)‖ ^ 2
  let R : ℝ → ℂ := fun ξ => (actualBareQuarterPartial N ξ : ℂ) *
    (starRingEnd ℂ) (unitarySourceFourier U ξ) * unitarySourceFourier U (-ξ)
  have hA : Integrable A volume :=
    actual_bare_quarter_partial_energy_integrable N (source_zero_l1 hu₁) (source_zero_l2 hu₂)
  have hB : Integrable B volume := by
    have h := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hA
    simpa only [Function.comp_def, A, B, actual_bare_quarter_partial_even] using h
  obtain ⟨hR, hRi⟩ := actual_bare_quarter_partial_cross N hu₁ hu₂
  have hReflect : (∫ ξ, B ξ) = ∫ ξ, A ξ := by
    have h := integral_neg_eq_self A volume
    simpa only [Function.comp_def, A, B, actual_bare_quarter_partial_even] using h
  calc
    _ = ∫ ξ : ℝ, (A ξ + B ξ) + 2 * (R ξ).re := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        rw [actual_even_zero_fourier hu₁, source_norm_add_sq]
        dsimp [A, B, R, U]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, zero_add, sub_zero]
        ring
    _ = (∫ ξ, A ξ) + (∫ ξ, B ξ) + 2 * (∫ ξ, R ξ).re := by
      have hSum : Integrable (fun ξ => A ξ + B ξ) volume := hA.add hB
      have hTerm : Integrable (fun ξ => 2 * (R ξ).re) volume := hR.re.const_mul 2
      rw [integral_add hSum hTerm, integral_add hA hB, integral_const_mul]
      have hre : (∫ ξ : ℝ, (R ξ).re) = (∫ ξ : ℝ, R ξ).re := integral_re hR
      rw [hre]
    _ = _ := by rw [hReflect, hRi]; ring

/-- The literal bare quarter weight, with its actual digamma input. -/
def actualBareQuarterWeight (ξ : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (ξ : ℂ))).re -
    (Complex.digamma (1 / 4)).re

/- Consumes only the canonical residual supplier's fifth pointwise HasSum
clause. Its total norm identity is retained by the supplier and is not
substituted for the actual bare series needed in this proof. -/
private theorem actual_bare_quarter_hasSum (ξ : ℝ) :
    HasSum (fun n : ℕ => actualBareQuarterIncrement ((n : ℝ) + 1 / 4) ξ)
      (actualBareQuarterWeight ξ) := by
  have h :=
    (D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series
      1 (by norm_num)).2.2.2.2 ξ
  simpa only [actualBareQuarterWeight, actualBareQuarterIncrement] using h

theorem actual_bare_quarter_nonneg (ξ : ℝ) : 0 ≤ actualBareQuarterWeight ξ := by
  rw [← (actual_bare_quarter_hasSum ξ).tsum_eq]
  exact tsum_nonneg fun n => actual_bare_quarter_increment_nonneg (by positivity) ξ

private theorem actual_bare_quarter_partial_le (N : ℕ) (ξ : ℝ) :
    actualBareQuarterPartial N ξ ≤ actualBareQuarterWeight ξ := by
  rw [← (actual_bare_quarter_hasSum ξ).tsum_eq]
  exact (actual_bare_quarter_hasSum ξ).summable.sum_le_tsum (Finset.range N)
    (fun n _ => actual_bare_quarter_increment_nonneg (by positivity) ξ)

private theorem actual_bare_quarter_partial_tendsto (ξ : ℝ) :
    Tendsto (fun N => actualBareQuarterPartial N ξ) atTop (𝓝 (actualBareQuarterWeight ξ)) :=
  (actual_bare_quarter_hasSum ξ).tendsto_sum_nat

theorem actual_bare_quarter_measurable : Measurable actualBareQuarterWeight := by
  have hEq : actualBareQuarterWeight = fun ξ =>
      ∑' n : ℕ, actualBareQuarterIncrement ((n : ℝ) + 1 / 4) ξ :=
    funext fun ξ => (actual_bare_quarter_hasSum ξ).tsum_eq.symm
  rw [hEq]
  apply Measurable.tsum
  intro n
  unfold actualBareQuarterIncrement
  fun_prop (disch := positivity)

theorem actual_bare_quarter_even (ξ : ℝ) :
    actualBareQuarterWeight (-ξ) = actualBareQuarterWeight ξ := by
  rw [← (actual_bare_quarter_hasSum (-ξ)).tsum_eq,
    ← (actual_bare_quarter_hasSum ξ).tsum_eq]
  apply tsum_congr
  intro n
  simp only [actualBareQuarterIncrement, neg_sq]

def InActualBareQuarterGraph (f : ℝ → ℂ) : Prop :=
  Integrable (fun ξ => actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2) volume

def actualBareQuarterEnergy (f : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2

private theorem actual_even_zero_l1 {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (actualEvenZeroExtension u) volume :=
  (source_zero_l1 hu).add (source_reflect_l1 (source_zero_l1 hu))

private theorem actual_even_zero_l2 {u : ℝ → ℂ} (hu : MemLp u 2 halfline) :
    MemLp (actualEvenZeroExtension u) 2 volume :=
  (source_zero_l2 hu).add (source_reflect_l2 (source_zero_l2 hu))

private theorem actual_bare_quarter_partial_integral_tendsto
    {f : ℝ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (hQ : InActualBareQuarterGraph f) :
    Tendsto (fun N => ∫ ξ, actualBareQuarterPartial N ξ *
      ‖unitarySourceFourier f ξ‖ ^ 2) atTop (𝓝 (actualBareQuarterEnergy f)) := by
  apply integral_tendsto_of_tendsto_of_monotone
    (fun N => actual_bare_quarter_partial_energy_integrable N hf₁ hf₂) hQ
  · exact Eventually.of_forall fun ξ N M hNM =>
      mul_le_mul_of_nonneg_right (actual_bare_quarter_partial_mono ξ hNM) (sq_nonneg _)
  · exact Eventually.of_forall fun ξ =>
      (actual_bare_quarter_partial_tendsto ξ).mul tendsto_const_nhds

/-- Bare W domain equivalence and exact finite-to-infinite energy identity,
on the actual same L1∩L2 source. Uniform finite bounds are supplied by the
actual complete PositiveHankel Laplace-square theorem. -/
theorem actual_bare_quarter_even_zero_domain_and_identity
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    (InActualBareQuarterGraph (actualEvenZeroExtension u) ↔
      InActualBareQuarterGraph (zeroExtension u)) ∧
    (InActualBareQuarterGraph (zeroExtension u) →
      actualBareQuarterEnergy (actualEvenZeroExtension u) =
        2 * actualBareQuarterEnergy (zeroExtension u) -
          (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re) := by
  let L : ℕ → ℝ := fun n => Complex.normSq
    (∫ t : ℝ, (Real.exp (-((n : ℝ) + 1 / 4) * t) : ℂ) * u t ∂halfline)
  obtain ⟨_, _, _, _, hS₀, hH₀, _, _, _⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.positive_hankel_actual_l2_domain_quarter_sharp
      (k := (1 / 4 : ℝ)) (by norm_num) u hu₂
  have hS : Summable L := by
    simpa only [L, D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace,
      add_comm (1 / 4 : ℝ)] using hS₀
  have hH : (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re =
      ∑' n : ℕ, L n := by
    rw [hH₀, ← Complex.ofReal_tsum, Complex.ofReal_re]
    apply tsum_congr
    intro n
    simp [L, D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace, add_comm]
  have hLpos (n : ℕ) : 0 ≤ L n := Complex.normSq_nonneg _
  have hLle (N : ℕ) : (∑ n ∈ Finset.range N, L n) ≤ ∑' n, L n :=
    hS.sum_le_tsum (Finset.range N) (fun n _ => hLpos n)
  have hLpartialpos (N : ℕ) : 0 ≤ ∑ n ∈ Finset.range N, L n :=
    Finset.sum_nonneg fun n _ => hLpos n
  have hU₁ := source_zero_l1 hu₁
  have hU₂ := source_zero_l2 hu₂
  have hE₁ := actual_even_zero_l1 hu₁
  have hE₂ := actual_even_zero_l2 hu₂
  have hFinite (N : ℕ) := actual_bare_quarter_partial_energy_identity N hu₁ hu₂
  have hDomain : InActualBareQuarterGraph (actualEvenZeroExtension u) ↔
      InActualBareQuarterGraph (zeroExtension u) := by
    constructor
    · intro hE
      apply nonnegative_monotone_integrable_of_uniform_integral_bound
        (B := (actualBareQuarterEnergy (actualEvenZeroExtension u) + ∑' n, L n) / 2)
        (fun N => actual_bare_quarter_partial_energy_integrable N hU₁ hU₂)
        (fun N ξ => mul_nonneg (actual_bare_quarter_partial_nonneg N ξ) (sq_nonneg _))
        (fun ξ N M hNM => mul_le_mul_of_nonneg_right
          (actual_bare_quarter_partial_mono ξ hNM) (sq_nonneg _))
        (fun ξ => (actual_bare_quarter_partial_tendsto ξ).mul tendsto_const_nhds)
      intro N
      have hEbound : (∫ ξ, actualBareQuarterPartial N ξ *
          ‖unitarySourceFourier (actualEvenZeroExtension u) ξ‖ ^ 2) ≤
            actualBareQuarterEnergy (actualEvenZeroExtension u) := by
        apply integral_mono (actual_bare_quarter_partial_energy_integrable N hE₁ hE₂) hE
        intro ξ
        exact mul_le_mul_of_nonneg_right (actual_bare_quarter_partial_le N ξ) (sq_nonneg _)
      have hId := hFinite N
      change _ = 2 * _ - (∑ n ∈ Finset.range N, L n) at hId
      linarith [hLle N]
    · intro hU
      apply nonnegative_monotone_integrable_of_uniform_integral_bound
        (B := 2 * actualBareQuarterEnergy (zeroExtension u))
        (fun N => actual_bare_quarter_partial_energy_integrable N hE₁ hE₂)
        (fun N ξ => mul_nonneg (actual_bare_quarter_partial_nonneg N ξ) (sq_nonneg _))
        (fun ξ N M hNM => mul_le_mul_of_nonneg_right
          (actual_bare_quarter_partial_mono ξ hNM) (sq_nonneg _))
        (fun ξ => (actual_bare_quarter_partial_tendsto ξ).mul tendsto_const_nhds)
      intro N
      have hUbound : (∫ ξ, actualBareQuarterPartial N ξ *
          ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) ≤
            actualBareQuarterEnergy (zeroExtension u) := by
        apply integral_mono (actual_bare_quarter_partial_energy_integrable N hU₁ hU₂) hU
        intro ξ
        exact mul_le_mul_of_nonneg_right (actual_bare_quarter_partial_le N ξ) (sq_nonneg _)
      have hId := hFinite N
      change _ = 2 * _ - (∑ n ∈ Finset.range N, L n) at hId
      linarith [hLpartialpos N]
  refine ⟨hDomain, ?_⟩
  intro hU
  have hE := hDomain.mpr hU
  have hUlim := actual_bare_quarter_partial_integral_tendsto hU₁ hU₂ hU
  have hElim := actual_bare_quarter_partial_integral_tendsto hE₁ hE₂ hE
  have hLlim := hS.hasSum.tendsto_sum_nat
  rw [hH]
  apply tendsto_nhds_unique hElim
  have hResult := (hUlim.const_mul 2).sub hLlim
  convert hResult using 1
  ext N
  exact hFinite N

private theorem actual_bare_quarter_cross_integrable
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline)
    (hU : InActualBareQuarterGraph (zeroExtension u)) :
    Integrable (fun ξ : ℝ => (actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume := by
  let A : ℝ → ℝ := fun ξ => actualBareQuarterWeight ξ *
    ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ => actualBareQuarterWeight ξ *
    ‖unitarySourceFourier (zeroExtension u) (-ξ)‖ ^ 2
  have hA : Integrable A volume := hU
  have hB : Integrable B volume := by
    simpa only [Function.comp_def, A, B, actual_bare_quarter_even] using
      (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hA
  have hF : AEStronglyMeasurable (unitarySourceFourier (zeroExtension u)) volume :=
    (continuous_unitarySourceFourier (source_zero_l1 hu₁)).aestronglyMeasurable
  have hFm : AEStronglyMeasurable
      (fun ξ => unitarySourceFourier (zeroExtension u) (-ξ)) volume :=
    ((continuous_unitarySourceFourier (source_zero_l1 hu₁)).comp
    (continuous_neg)).aestronglyMeasurable
  have hw : AEStronglyMeasurable (fun ξ => (actualBareQuarterWeight ξ : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      actual_bare_quarter_measurable.aestronglyMeasurable
  apply ((hA.add hB).div_const 2).mono'
    ((hw.mul (Complex.continuous_conj.comp_aestronglyMeasurable hF)).mul hFm)
  exact Eventually.of_forall fun ξ => by
    change ‖(actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)‖ ≤ (A ξ + B ξ) / 2
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (actual_bare_quarter_nonneg ξ)]
    dsimp [A, B]
    have hSq := sq_nonneg
      (‖unitarySourceFourier (zeroExtension u) ξ‖ -
        ‖unitarySourceFourier (zeroExtension u) (-ξ)‖)
    have hW := actual_bare_quarter_nonneg ξ
    nlinarith [mul_nonneg hW hSq]

/-- Actual bare W reflected cross. Both its domain and exact value are
derived from finite actual resolvents and monotone convergence. -/
theorem actual_bare_quarter_reflected_cross
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline)
    (hU : InActualBareQuarterGraph (zeroExtension u)) :
    Integrable (fun ξ : ℝ => (actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, (actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)).re =
      -(D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re / 2 := by
  let A : ℝ → ℝ := fun ξ => actualBareQuarterWeight ξ *
    ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ => actualBareQuarterWeight ξ *
    ‖unitarySourceFourier (zeroExtension u) (-ξ)‖ ^ 2
  let R : ℝ → ℂ := fun ξ => (actualBareQuarterWeight ξ : ℂ) *
    (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
      unitarySourceFourier (zeroExtension u) (-ξ)
  have hA : Integrable A volume := hU
  have hB : Integrable B volume := by
    simpa only [Function.comp_def, A, B, actual_bare_quarter_even] using
      (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hA
  have hR : Integrable R volume := actual_bare_quarter_cross_integrable hu₁ hU
  have hReflect : (∫ ξ, B ξ) = ∫ ξ, A ξ := by
    simpa only [A, B, actual_bare_quarter_even] using integral_neg_eq_self A volume
  have hExpansion : actualBareQuarterEnergy (actualEvenZeroExtension u) =
      2 * actualBareQuarterEnergy (zeroExtension u) + 2 * (∫ ξ, R ξ).re := by
    calc
      _ = ∫ ξ : ℝ, (A ξ + B ξ) + 2 * (R ξ).re := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          dsimp only [actualBareQuarterEnergy]
          rw [actual_even_zero_fourier hu₁, source_norm_add_sq]
          dsimp [A, B, R]
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, zero_add, sub_zero]
          ring
      _ = (∫ ξ, A ξ) + (∫ ξ, B ξ) + 2 * (∫ ξ, R ξ).re := by
        have hSum : Integrable (fun ξ => A ξ + B ξ) volume := hA.add hB
        have hTerm : Integrable (fun ξ => 2 * (R ξ).re) volume := hR.re.const_mul 2
        rw [integral_add hSum hTerm, integral_add hA hB, integral_const_mul]
        have hre : (∫ ξ : ℝ, (R ξ).re) = (∫ ξ : ℝ, R ξ).re := integral_re hR
        rw [hre]
      _ = _ := by
        rw [hReflect]
        dsimp only [A, actualBareQuarterEnergy]
        ring
  refine ⟨hR, ?_⟩
  have hPaid := (actual_bare_quarter_even_zero_domain_and_identity hu₁ hu₂).2 hU
  change (∫ ξ, R ξ).re = _
  linarith

theorem actual_literal_even_fourier (u : ℝ → ℂ) (ξ : ℝ) :
    unitarySourceFourier (fun t : ℝ => u |t|) ξ =
      unitarySourceFourier (actualEvenZeroExtension u) ξ := by
  have hAE : (fun t : ℝ => u |t|) =ᵐ[volume] actualEvenZeroExtension u := by
    have hz : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simp only [ae_iff, not_not]
      exact measure_singleton 0
    filter_upwards [hz] with t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · have hp : 0 < -t := by linarith
      simp [actualEvenZeroExtension, zeroExtension, abs_of_neg ht,
        not_lt_of_ge ht.le, hp]
    · have hn : ¬ 0 < -t := by linarith
      simp [actualEvenZeroExtension, zeroExtension, abs_of_pos ht, ht, hn]
  unfold unitarySourceFourier
  rw [Real.fourier_congr_ae hAE]

end D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
