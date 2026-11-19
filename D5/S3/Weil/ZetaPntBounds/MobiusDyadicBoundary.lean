/- GID: D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted dyadic Möbius energy controls reciprocal zeta on vertical lines. -/

import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
import D5.S3.Analytic.Laplace.CausalExponentialStripTransfer
import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
The unit-weight file supplies the positive-real-part dyadic Mellin identity and its
Fourier conversion. The half-line Mellin file supplies holomorphy for an L² input.
Reweighting that input and shifting the Mellin variable gives holomorphy on
the open half-plane set by the weight. The identity theorem applies after multiplying by
`s * riemannZeta₁ (s + 1)`. Each point on the zero-free boundary admits local
division by this factor. Causal damping, angular Plancherel, and Fatou give the
boundary symbol mass bound, which a pointwise dyadic factor estimate transfers
to the weighted reciprocal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

namespace D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary

open D5.S3.Analytic.Laplace.CausalExponentialStripTransfer (tilt)
open D5.S3.Weil.Mertens.MobiusDyadicEnergy (mobiusDyadicDifference)
open D5.S3.Weil.ZetaGamma.FormCore.LineFourier
  (angularFourier angular_extended_plancherel continuous_raw_fourier)
open D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
  (mobiusDyadicMellinSymbol unitWeightTilt unitWeightSection
    fourier_unitWeightTilt halfLineMellin_dyadic measurable_unitWeightTilt
    measurable_unitWeight_difference)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (halfLineMeasure halfLineMellin halfLineMellin_analyticOnNhd)

local notation "D" => mobiusDyadicDifference

private theorem ofReal_sq_norm (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem integrable_causalTilt {g : ℝ → ℂ}
    (hg₂ : MemLp g 2) (hg₀ : ∀ u < 0, g u = 0) {h : ℝ} (hh : 0 < h) :
    Integrable (tilt h g) := by
  let k : ℝ → ℂ :=
    (Ici (0 : ℝ)).indicator (fun u : ℝ => (Real.exp (-h * u) : ℂ))
  have hk : Measurable k :=
    (show Measurable (fun u : ℝ => (Real.exp (-h * u) : ℂ)) by fun_prop).indicator
      measurableSet_Ici
  have hsqOn : IntegrableOn (fun u : ℝ => Real.exp (-(2 * h) * u)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi (by linarith) 0)
  have hk₂ : MemLp k 2 := by
    apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
    apply (hsqOn.integrable_indicator measurableSet_Ici).congr
    filter_upwards with u
    by_cases hu : u ∈ Ici (0 : ℝ)
    · simp only [k, indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_nat_mul _ 2]
      congr 1
      norm_num <;> ring
    · simp [k, hu]
  have hprod : MemLp (fun u => k u * g u) 1 := hk₂.fun_mul hg₂
  apply (memLp_one_iff_integrable.mp hprod).congr
  filter_upwards with u
  by_cases hu : 0 ≤ u
  · simp [k, tilt, hu]
  · simp [tilt, k, hu, hg₀ u (lt_of_not_ge hu)]

private theorem norm_causalTilt_le {g : ℝ → ℂ}
    (hg₀ : ∀ u < 0, g u = 0) {h : ℝ} (hh : 0 ≤ h) (u : ℝ) :
    ‖tilt h g u‖ ≤ ‖g u‖ := by
  by_cases hu : 0 ≤ u
  · rw [tilt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh) hu))
  · simp [tilt, hg₀ u (lt_of_not_ge hu)]

/-- One-sided angular Fourier limits of damped causal profiles satisfy the boundary L² bound. -/
private theorem causal_angular_boundary_sq_bound {g H : ℝ → ℂ} (hg : Measurable g)
    (hg₂ : MemLp g 2) (hg₀ : ∀ u < 0, g u = 0) (hH : Measurable H)
    {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hlim : ∀ y, Tendsto (fun n => angularFourier (tilt (d n) g) y) atTop (𝓝 (H y))) :
    Integrable (fun y => ‖H y‖ ^ 2) ∧
      (∫ y, ‖H y‖ ^ 2) ≤ 2 * Real.pi * ∫ u, ‖g u‖ ^ 2 := by
  let mass : (ℝ → ℂ) → ℝ → ℝ≥0∞ := fun f u => ENNReal.ofReal (‖f u‖ ^ 2)
  let F : ℕ → ℝ → ℂ := fun n => angularFourier (tilt (d n) g)
  have htime := (memLp_two_iff_integrable_sq_norm hg₂.aestronglyMeasurable).1 hg₂
  have hp : 0 < 2 * Real.pi := by positivity
  have hcancel : ENNReal.ofReal (2 * Real.pi) *
      ENNReal.ofReal (1 / (2 * Real.pi)) = 1 := by
    rw [← ENNReal.ofReal_mul hp.le,
      show 2 * Real.pi * (1 / (2 * Real.pi)) = 1 by field_simp [hp.ne'],
      ENNReal.ofReal_one]
  have hint (n : ℕ) : Integrable (tilt (d n) g) := integrable_causalTilt hg₂ hg₀ (hd n)
  have hline (n : ℕ) : (∫⁻ y, mass (F n) y) ≤
      ENNReal.ofReal (2 * Real.pi * ∫ u, ‖g u‖ ^ 2) := by
    have hmeas : Measurable (tilt (d n) g) :=
      (show Measurable (fun u : ℝ => (Real.exp (-d n * u) : ℂ)) by fun_prop).mul hg
    have h₂ : MemLp (tilt (d n) g) 2 :=
      hg₂.of_le hmeas.aestronglyMeasurable
        (ae_of_all _ (norm_causalTilt_le hg₀ (hd n).le))
    have hP := angular_extended_plancherel (hint n) h₂
    have hPmass : (∫⁻ u, mass (tilt (d n) g) u) =
        ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ y, mass (F n) y := by
      simpa only [mass, F, ofReal_sq_norm] using hP
    calc
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, mass (tilt (d n) g) u := by
        rw [hPmass, ← mul_assoc, hcancel, one_mul]
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, mass g u :=
        mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_causalTilt_le hg₀ (hd n).le u) 2))
      _ = _ := by
        dsimp only [mass]
        rw [← ofReal_integral_eq_lintegral_ofReal htime (ae_of_all _ fun _ => sq_nonneg _),
          ← ENNReal.ofReal_mul hp.le]
  have hF (n : ℕ) : Measurable (mass (F n)) := by
    have hcont : Continuous (F n) :=
      (continuous_raw_fourier (hint n)).comp
        (show Continuous (fun y : ℝ => y / (2 * Real.pi)) by fun_prop)
    exact (hcont.norm.pow 2).measurable.ennreal_ofReal
  have hliminf (y : ℝ) : liminf (fun n => mass (F n) y) atTop = mass H y := by
    have hc : Continuous (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) :=
      ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)
    exact (hc.continuousAt.tendsto.comp (hlim y)).liminf_eq
  have hbound : (∫⁻ y, mass H y) ≤ ENNReal.ofReal (2 * Real.pi * ∫ u, ‖g u‖ ^ 2) := by
    calc
      _ = ∫⁻ y, liminf (fun n => mass (F n) y) atTop := by simp_rw [hliminf]
      _ ≤ liminf (fun n => ∫⁻ y, mass (F n) y) atTop := lintegral_liminf_le hF
      _ ≤ _ := Filter.liminf_le_of_frequently_le (Frequently.of_forall hline)
        ⟨⊥, Eventually.of_forall fun _ => bot_le⟩
  have hfin : Integrable (fun y => ‖H y‖ ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable (hH.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun _ => sq_nonneg _)).1
      (ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hfin, ?_⟩
  dsimp only [mass] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal hfin (ae_of_all _ fun _ => sq_nonneg _)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hp.le (integral_nonneg fun _ => sq_nonneg _))).1 hbound

private theorem mobiusTilt_add (a h : ℝ) :
    tilt h (unitWeightTilt a D) = unitWeightTilt (a + h) D := by
  funext u
  by_cases hu : u ∈ Ici (0 : ℝ)
  · simp only [tilt, unitWeightTilt, indicator_of_mem hu, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -h * u + -a * u = -(a + h) * u by ring]
  · simp [tilt, unitWeightTilt, hu]

private theorem angular_mobiusTilt (a y : ℝ) :
    angularFourier (unitWeightTilt a D) y =
      halfLineMellin (fun x => (D x : ℂ)) ((a : ℂ) + (y : ℂ) * I) := by
  rw [angularFourier, fourier_unitWeightTilt, unitWeightSection]
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ y hπ]

private theorem criticalTilt_energy (θ : ℝ)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    MemLp (unitWeightTilt (θ - 1) D) 2 ∧
    (∫ u, ‖unitWeightTilt (θ - 1) D u‖ ^ 2) =
      ∫ x in Ioi (1 : ℝ), D x ^ 2 * x ^ (-(2 * θ - 1)) := by
  let E : ℝ → ℝ := fun x => D x ^ 2 * x ^ (-(2 * θ - 1))
  let g := unitWeightTilt (θ - 1) D
  let k : ℝ → ℝ := fun u => Real.exp u • E (Real.exp u)
  have hk : IntegrableOn k (Ioi 0) :=
    (integrableOn_comp_exp_Ioi E 0).2 (by simpa only [Real.exp_zero, E] using hE)
  have hk' : IntegrableOn k (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hk
  have hpoint : (fun u => ‖g u‖ ^ 2) = (Ici (0 : ℝ)).indicator k := by
    funext u
    by_cases hu : u ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem hu]
      simp only [g, unitWeightTilt, indicator_of_mem hu, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), mul_pow, sq_abs, k, E, smul_eq_mul]
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, ← Real.exp_nat_mul _ 2]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-(θ - 1) * u) = u + u * -(2 * θ - 1) by ring, Real.exp_add]
      ring
    · simp [g, unitWeightTilt, hu]
  constructor
  · apply (memLp_two_iff_integrable_sq_norm
      (measurable_unitWeightTilt _ measurable_unitWeight_difference).aestronglyMeasurable).2
    change Integrable (fun u => ‖g u‖ ^ 2)
    rw [hpoint]
    exact hk'.integrable_indicator measurableSet_Ici
  · change (∫ u, ‖g u‖ ^ 2) = _
    rw [hpoint, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    simpa only [k, E, Real.exp_zero] using integral_comp_exp_Ioi E 0

private theorem analyticOnNhd_dyadicMellin (θ : ℝ)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    AnalyticOnNhd ℂ (halfLineMellin (fun x => (D x : ℂ))) {s : ℂ | θ - 1 < s.re} := by
  let b : ℝ := 1 / 2 - θ
  let f : ℝ → ℂ := fun x => (D x : ℂ) * ((x ^ b : ℝ) : ℂ)
  have hm : Measurable f :=
    (Complex.continuous_ofReal.measurable.comp measurable_unitWeight_difference).mul
      (Complex.continuous_ofReal.measurable.comp
        (show Measurable (fun x : ℝ => x ^ b) by fun_prop))
  have hf : MemLp f 2 halfLineMeasure := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    refine hE.congr_fun_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    have hx₀ : 0 < x := zero_lt_one.trans hx
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Real.rpow_mul_natCast hx₀.le b 2]
    norm_num only [Nat.cast_ofNat]
    rw [show b * 2 = -(2 * θ - 1) by dsimp [b]; ring]
  have heq (s : ℂ) :
      halfLineMellin (fun x => (D x : ℂ)) s = halfLineMellin f (s + b) := by
    unfold halfLineMellin
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    have hx₀ : 0 < x := zero_lt_one.trans hx
    dsimp only [f]
    rw [Complex.ofReal_cpow hx₀.le, mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx₀.ne')]
    rw [show (b : ℂ) + -(s + b + 1) = -(s + 1) by ring]
  intro s hs
  have hs' : -(1 / 2 : ℝ) < (s + (b : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    change θ - 1 < s.re at hs
    dsimp [b]
    linarith
  have hA : AnalyticAt ℂ (halfLineMellin f) (s + (b : ℂ)) :=
    halfLineMellin_analyticOnNhd hf _ hs'
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + (b : ℂ)) s :=
    analyticAt_id.add analyticAt_const
  rw [show halfLineMellin (fun x => (D x : ℂ)) =
    (fun z : ℂ => halfLineMellin f (z + (b : ℂ))) from funext heq]
  exact hA.comp_of_eq hshift rfl

private theorem shiftedZeta_ne_zero {s : ℂ} (hs : s ≠ 0)
    (hz : riemannZeta (s + 1) ≠ 0) : riemannZeta₁ (s + 1) ≠ 0 := by
  have hs₁ : s + 1 ≠ 1 := by simpa using hs
  intro h
  apply hz
  rw [riemannZeta_eq_inv_sub_mul hs₁, h, mul_zero]

private theorem cleared_dyadic_symbol {s : ℂ} (hs : s ≠ 0)
    (hz : riemannZeta₁ (s + 1) ≠ 0) :
    (s * riemannZeta₁ (s + 1)) * mobiusDyadicMellinSymbol s =
      (1 - (2 : ℂ) ^ s) * (s - riemannZeta₁ (s + 1)) := by
  have hs₁ : s + 1 ≠ 1 := by simpa using hs
  have hzInv : (riemannZeta (s + 1))⁻¹ = s * (riemannZeta₁ (s + 1))⁻¹ := by
    simpa using inv_riemannZeta_eq_sub_mul_of_ne_one hs₁
  rw [mobiusDyadicMellinSymbol, ite_eq_right hs, hzInv]
  field_simp [hs, hz]

/-- Continue the Mellin identity with the pole-removed zeta factor on the entire open
half-plane allowed by critical energy. -/
private theorem cleared_dyadic_mellin {θ : ℝ} (hθ : θ < 2)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    ∀ s : ℂ, θ - 1 < s.re →
      (s * riemannZeta₁ (s + 1)) * halfLineMellin (fun x => (D x : ℂ)) s =
        (1 - (2 : ℂ) ^ s) * (s - riemannZeta₁ (s + 1)) := by
  let U : Set ℂ := {s | θ - 1 < s.re}
  let Z : ℂ → ℂ := fun s => riemannZeta₁ (s + 1)
  let M := halfLineMellin (fun x => (D x : ℂ))
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hZ : Differentiable ℂ Z := differentiable_riemannZeta₁.comp
    (differentiable_id.add_const 1)
  have hpow : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl (by norm_num))
  have hL : AnalyticOnNhd ℂ (fun s => s * Z s * M s) U :=
    ((differentiable_id.mul hZ).differentiableOn.analyticOnNhd hU).mul
      (analyticOnNhd_dyadicMellin θ hE)
  have hR : AnalyticOnNhd ℂ (fun s => (1 - (2 : ℂ) ^ s) * (s - Z s)) U :=
    (((differentiable_const _).sub hpow).mul
      (differentiable_id.sub hZ)).differentiableOn.analyticOnNhd hU
  have h1 : (1 : ℂ) ∈ U := by
    change θ - 1 < (1 : ℂ).re
    simp only [Complex.one_re]
    linarith
  have hseed : (fun s => s * Z s * M s) =ᶠ[𝓝 (1 : ℂ)]
      (fun s => (1 - (2 : ℂ) ^ s) * (s - Z s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with s hs
    change 0 < s.re at hs
    have hs₀ : s ≠ 0 := by
      intro he
      simpa [he] using hs
    have hz : riemannZeta (s + 1) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
    change (s * Z s) * M s = _
    rw [show M s = mobiusDyadicMellinSymbol s from halfLineMellin_dyadic hs]
    exact cleared_dyadic_symbol hs₀ (shiftedZeta_ne_zero hs₀ hz)
  exact fun s hs => hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt (θ - 1)).isPreconnected h1 hseed hs

/-- Critical energy controls the square mass of the canonical symbol on the angular line. -/
private theorem dyadic_symbol_sq_bound {θ : ℝ} (hθ : θ < 2) (hθne : θ ≠ 1)
    (hzero : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    Integrable (fun y : ℝ => ‖mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)‖ ^ 2) ∧
      (∫ y : ℝ, ‖mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
        2 * Real.pi * ∫ x in Ioi (1 : ℝ), D x ^ 2 * x ^ (-(2 * θ - 1)) := by
  let a : ℝ := θ - 1
  let g := unitWeightTilt a D
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let s : ℝ → ℝ → ℂ := fun h y => ((a + h : ℝ) : ℂ) + (y : ℂ) * I
  let A : ℂ → ℂ := fun z => z * riemannZeta₁ (z + 1)
  let B : ℂ → ℂ := fun z => (1 - (2 : ℂ) ^ z) * (z - riemannZeta₁ (z + 1))
  let H : ℝ → ℂ := fun y => mobiusDyadicMellinSymbol (s 0 y)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hd₀ : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsRe (h y : ℝ) : (s h y).re = a + h := by simp [s, Complex.mul_re]
  have hsZ (y : ℝ) : s 0 y + 1 = (θ : ℂ) + (y : ℂ) * I := by
    dsimp [s, a]
    push_cast
    ring
  have hs₀ (y : ℝ) : s 0 y ≠ 0 := by
    intro he
    have hre := hsRe 0 y
    rw [he, Complex.zero_re, add_zero] at hre
    exact hθne (by dsimp [a] at hre; linarith)
  have hZ₀ (y : ℝ) : riemannZeta₁ (s 0 y + 1) ≠ 0 :=
    shiftedZeta_ne_zero (hs₀ y) (by rw [hsZ]; exact hzero y)
  have hA₀ (y : ℝ) : A (s 0 y) ≠ 0 := mul_ne_zero (hs₀ y) (hZ₀ y)
  have hA : Continuous A := continuous_id.mul
    (differentiable_riemannZeta₁.continuous.comp (continuous_id.add continuous_const))
  have hB : Continuous B := by
    have hZ : Continuous (fun z : ℂ => riemannZeta₁ (z + 1)) :=
      differentiable_riemannZeta₁.continuous.comp (continuous_id.add continuous_const)
    have hPow : Differentiable ℂ (fun z : ℂ => (2 : ℂ) ^ z) :=
      differentiable_id.const_cpow (Or.inl (by norm_num))
    exact (continuous_const.sub hPow.continuous).mul (continuous_id.sub hZ)
  have hHdiv (y : ℝ) : H y = B (s 0 y) / A (s 0 y) := by
    apply (eq_div_iff (hA₀ y)).2
    rw [mul_comm]
    exact cleared_dyadic_symbol (hs₀ y) (hZ₀ y)
  have hH : Continuous H := by
    have hS : Continuous (s 0) := by unfold s; fun_prop
    rw [show H = (fun y => B (s 0 y) / A (s 0 y)) from funext hHdiv]
    exact (hB.comp hS).div (hA.comp hS) hA₀
  have hg₀ (u : ℝ) (hu : u < 0) : g u = 0 := by
    simp [g, unitWeightTilt, not_le.mpr hu]
  have hlim (y : ℝ) : Tendsto (fun n => angularFourier (tilt (d n) g) y) atTop (𝓝 (H y)) := by
    have hS : Continuous (fun h => s h y) := by dsimp [s]; fun_prop
    have hs : Tendsto (fun n => s (d n) y) atTop (𝓝 (s 0 y)) :=
      hS.continuousAt.tendsto.comp hd₀
    have ha : Tendsto (fun n => A (s (d n) y)) atTop (𝓝 (A (s 0 y))) :=
      hA.continuousAt.tendsto.comp hs
    have hb : Tendsto (fun n => B (s (d n) y)) atTop (𝓝 (B (s 0 y))) :=
      hB.continuousAt.tendsto.comp hs
    rw [hHdiv]
    refine (hb.div ha (hA₀ y)).congr' ?_
    have hne : ∀ᶠ n in atTop, A (s (d n) y) ≠ 0 :=
      ha.eventually (isOpen_ne.mem_nhds (hA₀ y))
    filter_upwards [hne] with n hn
    change B (s (d n) y) / A (s (d n) y) =
      angularFourier (tilt (d n) (unitWeightTilt a D)) y
    rw [mobiusTilt_add, angular_mobiusTilt]
    symm
    apply (eq_div_iff hn).2
    rw [mul_comm]
    exact cleared_dyadic_mellin hθ hE (s (d n) y) (by
      rw [hsRe]
      exact lt_add_of_pos_right _ (hd n))
  obtain ⟨hg₂, hEnergy⟩ := criticalTilt_energy θ hE
  obtain ⟨hInt, hbound⟩ := causal_angular_boundary_sq_bound
    (measurable_unitWeightTilt _ measurable_unitWeight_difference) hg₂ hg₀ hH.measurable hd hlim
  change (∫ y, ‖H y‖ ^ 2) ≤ 2 * Real.pi * ∫ u, ‖unitWeightTilt (θ - 1) D u‖ ^ 2 at hbound
  rw [hEnergy] at hbound
  simpa only [H, s, add_zero, a] using And.intro hInt hbound

private theorem reciprocal_weight_sq_integral :
    (∫ y : ℝ, ((1 + |y|)⁻¹ : ℝ) ^ 2) = 2 := by
  have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => - (1 + u)⁻¹) ((1 + t)⁻¹ ^ 2) t := by
    have ht₀ : 0 ≤ t := ht
    have hne : (1 + t : ℝ) ≠ 0 := by positivity
    simpa only [id_eq, neg_div, neg_neg, one_div, inv_pow] using
      (((hasDerivAt_id t).const_add 1).fun_inv hne).fun_neg
  have hlim : Tendsto (fun t : ℝ => - (1 + t)⁻¹) atTop (𝓝 0) := by
    have hshift : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
      simpa only [add_comm, id_eq] using
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    simpa only [neg_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hshift).neg
  have hi : (∫ t in Ioi (0 : ℝ), ((1 + t)⁻¹ : ℝ) ^ 2) = 1 := by
    simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t _ => sq_nonneg _) hlim
  rw [integral_comp_abs (f := fun t : ℝ => ((1 + t)⁻¹ : ℝ) ^ 2), hi]
  norm_num

private theorem dyadic_factor_abs_pos {a : ℝ} (ha : a ≠ 0) :
    0 < |1 - (2 : ℝ) ^ a| := by
  apply abs_pos.mpr
  rcases lt_or_gt_of_ne ha with hn | hp
  · exact (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hn)).ne'
  · exact (sub_neg.mpr (Real.one_lt_rpow (by norm_num) hp)).ne

private theorem reciprocal_le_symbol {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ : θ < 2)
    (hθne : θ ≠ 1) (y : ℝ) :
    ‖(riemannZeta ((θ : ℂ) + (y : ℂ) * I))⁻¹‖ / (1 + |y|) ≤
      (1 + |y|)⁻¹ +
      ‖mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)‖ /
        |1 - (2 : ℝ) ^ (θ - 1)| := by
  let a : ℝ := θ - 1
  let s : ℂ := (a : ℂ) + (y : ℂ) * I
  let w : ℝ := 1 + |y|
  let c : ℝ := |1 - (2 : ℝ) ^ a|
  let p : ℂ := 1 - (2 : ℂ) ^ s
  let R : ℂ := (riemannZeta ((θ : ℂ) + (y : ℂ) * I))⁻¹
  let F : ℂ := mobiusDyadicMellinSymbol s
  have ha : a ≠ 0 := sub_ne_zero.mpr hθne
  have hsre : s.re = a := by simp [s, Complex.mul_re]
  have hsim : s.im = y := by simp [s, Complex.mul_im]
  have hs₀ : s ≠ 0 := by
    intro he
    rw [he, Complex.zero_re] at hsre
    exact ha hsre.symm
  have hz : s + 1 = (θ : ℂ) + (y : ℂ) * I := by dsimp [s, a]; push_cast; ring
  have hw : 0 < w := by dsimp [w]; positivity
  have hc : 0 < c := dyadic_factor_abs_pos ha
  have hps : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ a := by
    simpa only [Complex.ofReal_ofNat, hsre] using
      (Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) s)
  have hp : c ≤ ‖p‖ := by
    simpa only [c, p, norm_one, hps] using abs_norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ s)
  have hp₀ : 0 < ‖p‖ := hc.trans_le hp
  have hpne : p ≠ 0 := norm_pos_iff.mp hp₀
  have hsw : ‖s‖ ≤ w := by
    have ht := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre, hsim] at ht
    have ha₁ : |a| ≤ 1 := abs_le.mpr ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
    exact ht.trans (add_le_add ha₁ le_rfl)
  have hR : R = 1 + s * F / p := by
    have hF : F = p * (R - 1) / s := by
      simp only [F, mobiusDyadicMellinSymbol, ite_eq_right hs₀, p, R, hz]
    rw [hF]
    field_simp [hs₀, hpne] <;> ring
  change ‖R‖ / w ≤ w⁻¹ + ‖F‖ / c
  have hnorm : ‖R‖ ≤ 1 + ‖s‖ * ‖F‖ / ‖p‖ := by
    rw [hR]
    simpa only [norm_one, norm_div, norm_mul] using norm_add_le (1 : ℂ) (s * F / p)
  have hratio : ‖s‖ * ‖F‖ / ‖p‖ ≤ w * (‖F‖ / c) := by
    calc
      _ ≤ ‖s‖ * ‖F‖ / c :=
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc hp
      _ ≤ w * ‖F‖ / c :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsw (norm_nonneg _)) hc.le
      _ = _ := by ring
  apply (div_le_iff₀ hw).2
  calc
    ‖R‖ ≤ 1 + w * (‖F‖ / c) := hnorm.trans (add_le_add le_rfl hratio)
    _ = _ := by field_simp [hw.ne', hc.ne'] <;> ring

private theorem weighted_reciprocal_of_symbol {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ : θ < 2)
    (hθne : θ ≠ 1)
    (hzero : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    {K : ℝ}
    (hF : Integrable (fun y : ℝ => ‖mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)‖ ^ 2))
    (hK : (∫ y : ℝ, ‖mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤ K) :
    Integrable (fun y : ℝ => 1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)) ∧
    (∫ y : ℝ, 1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)) ≤
      4 + 2 * K / (1 - (2 : ℝ) ^ (θ - 1)) ^ 2 := by
  let b : ℝ → ℝ := fun y => (1 + |y|)⁻¹
  let c : ℝ := |1 - (2 : ℝ) ^ (θ - 1)|
  let z : ℝ → ℂ := fun y => (θ : ℂ) + (y : ℂ) * I
  let F : ℝ → ℂ := fun y => mobiusDyadicMellinSymbol ((↑(θ - 1) : ℂ) + (y : ℂ) * I)
  let q : ℝ → ℝ := fun y => ‖(riemannZeta (z y))⁻¹‖ / (1 + |y|)
  let W : ℝ → ℝ := fun y => 2 * b y ^ 2 + (2 / c ^ 2) * ‖F y‖ ^ 2
  have hc : 0 < c := dyadic_factor_abs_pos (sub_ne_zero.mpr hθne)
  have hcont : Continuous q := by
    have hz : Continuous z := by unfold z; fun_prop
    have hzeta : Continuous (fun y => riemannZeta (z y)) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      have hy : z y ≠ 1 := by
        intro he
        have hre := congrArg Complex.re he
        exact hθne (by simpa [z, Complex.mul_re] using hre)
      exact (differentiableAt_riemannZeta hy).continuousAt.comp hz.continuousAt
    exact (hzeta.inv₀ hzero).norm.div (by fun_prop) (fun y => by positivity)
  have hb : Integrable (fun y => b y ^ 2) := by
    have hi : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-2 : ℝ)) :=
      integrable_one_add_norm (by simp)
    apply hi.congr
    filter_upwards with y
    dsimp only [b]
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  have hW : Integrable W := (hb.const_mul 2).add (hF.const_mul _)
  have hq₀ (y : ℝ) : 0 ≤ q y := by dsimp [q]; positivity
  have hle (y : ℝ) : q y ^ 2 ≤ W y := by
    have hy : q y ≤ b y + ‖F y‖ / c := reciprocal_le_symbol hθ₀ hθ hθne y
    calc
      _ ≤ (b y + ‖F y‖ / c) ^ 2 := pow_le_pow_left₀ (hq₀ y) hy 2
      _ ≤ 2 * b y ^ 2 + 2 * (‖F y‖ / c) ^ 2 := by nlinarith [sq_nonneg (b y - ‖F y‖ / c)]
      _ = _ := by simp only [W, div_pow]; ring
  have hq : Integrable (fun y => q y ^ 2) := hW.mono' (hcont.pow 2).aestronglyMeasurable
    (ae_of_all _ fun y => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hle y)
  have heq (y : ℝ) :
      1 / ((1 + |y|) ^ 2 * ‖riemannZeta (z y)‖ ^ 2) = q y ^ 2 := by
    simp only [q, norm_inv, mul_pow, inv_pow, div_eq_mul_inv, one_mul, mul_inv]
    ring
  refine ⟨hq.congr (ae_of_all _ fun y => (heq y).symm), ?_⟩
  change (∫ y, 1 / ((1 + |y|) ^ 2 * ‖riemannZeta (z y)‖ ^ 2)) ≤ _
  simp_rw [heq]
  calc
    _ ≤ ∫ y, W y := integral_mono hq hW hle
    _ = 4 + (2 / c ^ 2) * ∫ y, ‖F y‖ ^ 2 := by
      dsimp only [W]
      rw [integral_add (hb.const_mul 2) (hF.const_mul _), integral_const_mul,
        integral_const_mul, show (∫ y, b y ^ 2) = 2 from reciprocal_weight_sq_integral]
      rw [show (2 : ℝ) * 2 = 4 by norm_num]
    _ ≤ 4 + (2 / c ^ 2) * K :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hK (by positivity))
    _ = _ := by dsimp [c]; rw [sq_abs]; ring

/-- Finite weighted energy of the signed dyadic Möbius difference bounds the squared reciprocal
of zeta on a zero-free vertical line. The frequency is angular. The weight becomes critical
at the zero abscissa. -/
theorem weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₂ : θ < 2) (hθne : θ ≠ 1)
    (hzero : ∀ y : ℝ, riemannZeta ((θ : ℂ) + (y : ℂ) * I) ≠ 0)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * θ - 1))) (Ioi 1)) :
    Integrable (fun y : ℝ =>
      1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)) ∧
    (∫ y : ℝ, 1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((θ : ℂ) + (y : ℂ) * I)‖ ^ 2)) ≤
      4 + 4 * Real.pi * (∫ x in Ioi (1 : ℝ), D x ^ 2 * x ^ (-(2 * θ - 1))) /
        (1 - (2 : ℝ) ^ (θ - 1)) ^ 2 := by
  obtain ⟨hF, hmass⟩ := dyadic_symbol_sq_bound hθ₂ hθne hzero hE
  have hout := weighted_reciprocal_of_symbol hθ₀ hθ₂ hθne hzero hF hmass
  exact ⟨hout.1, hout.2.trans_eq (by ring)⟩

section ZeroAbscissa

open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence (exists_nontrivial_zero_re_ge_half)

-- Check the specialization at the actual zero abscissa, including line nonvanishing.
example (hΘ : zeroAbscissa < 1)
    (hunattained : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≠ zeroAbscissa)
    (hE : IntegrableOn (fun x : ℝ => D x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) (Ioi 1)) :
    Integrable (fun y : ℝ =>
      1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((zeroAbscissa : ℂ) + (y : ℂ) * I)‖ ^ 2)) ∧
    (∫ y : ℝ, 1 / ((1 + |y|) ^ 2 * ‖riemannZeta ((zeroAbscissa : ℂ) + (y : ℂ) * I)‖ ^ 2)) ≤
      4 + 4 * Real.pi * (∫ x in Ioi (1 : ℝ), D x ^ 2 * x ^ (-(2 * zeroAbscissa - 1))) /
        (1 - (2 : ℝ) ^ (zeroAbscissa - 1)) ^ 2 := by
  obtain ⟨ρ, hρ, hhalf⟩ := exists_nontrivial_zero_re_ge_half
  have hΘhalf := hhalf.trans (zero_re_le_abscissa hρ)
  have hzero (y : ℝ) : riemannZeta ((zeroAbscissa : ℂ) + (y : ℂ) * I) ≠ 0 := by
    let z : ℂ := (zeroAbscissa : ℂ) + (y : ℂ) * I
    have hre : z.re = zeroAbscissa := by simp [z, Complex.mul_re]
    intro hz
    exact hunattained z ⟨hz, by rw [hre]; linarith, by rwa [hre]⟩ hre
  exact weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy
    (by linarith) (by linarith) hΘ.ne hzero hE

end ZeroAbscissa

end D5.S3.Weil.ZetaPntBounds.MobiusDyadicBoundary
