/- GID: D5/S3/Weil/ZetaTruncationMeanSquare
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaTruncationMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square control of zeta Dirichlet truncation on dyadic height intervals. -/

import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
Squared error for a Dirichlet truncation of the actual zeta function on
padded dyadic height intervals. The Euler–Maclaurin remainder becomes a
Fourier transform after logarithmic substitution.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace D5.S3.Weil.ZetaTruncationMeanSquare

open D5.S3.Weil.ZetaGamma.FormCore.LineFourier (angularFourier
  angularFourier_eq_integral angular_extended_plancherel continuous_raw_fourier)

noncomputable section

def vertical (u t : ℝ) : ℂ := (u : ℂ) + (t : ℂ) * Complex.I

def polynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s

def paddedBand (T : ℝ) : Set ℝ := {t | T - 1 ≤ |t| ∧ |t| ≤ 2 * T + 1}

private def sawtooth (x : ℝ) : ℝ := ⌊x⌋ + 1 / 2 - x

private def logProfile (u v : ℝ) : ℂ :=
  ((sawtooth (Real.exp v) * Real.exp (-u * v) : ℝ) : ℂ)

private def logKernel (N : ℕ) (u : ℝ) : ℝ → ℂ :=
  (Ioi (Real.log (N : ℝ))).indicator (logProfile u)

private theorem substituted_integrand (u t v : ℝ) :
    Real.exp v • ((sawtooth (Real.exp v) : ℂ) *
      (Real.exp v : ℂ) ^ (-(vertical u t + 1))) =
      Complex.exp ((-(t * v) : ℝ) * Complex.I) * logProfile u v := by
  have hphase :
      (Real.exp v : ℂ) * (Real.exp v : ℂ) ^ (-(vertical u t + 1)) =
        Complex.exp ((-(t * v) : ℝ) * Complex.I) * (Real.exp (-u * v) : ℂ) := by
    have hne : (Real.exp v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos v).le,
      Real.log_exp]
    simp only [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold vertical
    push_cast
    ring
  calc
    _ = (sawtooth (Real.exp v) : ℂ) *
        ((Real.exp v : ℂ) * (Real.exp v : ℂ) ^ (-(vertical u t + 1))) := by
      rw [Complex.real_smul]
      ring
    _ = _ := by
      rw [hphase]
      simp only [logProfile, Complex.ofReal_mul]
      ring

private theorem remainder_eq_angular {N : ℕ} (hN : 0 < (N : ℝ)) (u t : ℝ) :
    (∫ x : ℝ in Ioi (N : ℝ), (sawtooth x : ℂ) * (x : ℂ) ^ (-(vertical u t + 1))) =
      angularFourier (logKernel N u) t := by
  let f : ℝ → ℂ := fun x => (sawtooth x : ℂ) * (x : ℂ) ^ (-(vertical u t + 1))
  calc
    _ = ∫ v : ℝ in Ioi (Real.log (N : ℝ)), Real.exp v • f (Real.exp v) := by
      simpa only [f, Real.exp_log hN] using
        (integral_comp_exp_Ioi f (Real.log (N : ℝ))).symm
    _ = ∫ v : ℝ in Ioi (Real.log (N : ℝ)),
          Complex.exp ((-(t * v) : ℝ) * Complex.I) * logProfile u v := by
      exact setIntegral_congr_fun measurableSet_Ioi fun v _ =>
        substituted_integrand u t v
    _ = _ := by
      rw [angularFourier_eq_integral, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : v ∈ Ioi (Real.log (N : ℝ)) <;> simp [logKernel, hv]

private theorem logProfile_measurable (u : ℝ) : Measurable (logProfile u) := by
  have hexp : Continuous (fun v : ℝ => Real.exp (-u * v)) := by fun_prop
  exact Complex.continuous_ofReal.measurable.comp
    ((measurable_floor_add_half_sub.comp Real.continuous_exp.measurable).mul hexp.measurable)

private theorem norm_logProfile_le (u v : ℝ) :
    ‖logProfile u v‖ ≤ (1 / 2 : ℝ) * Real.exp (-u * v) := by
  rw [logProfile, Complex.norm_real, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos (-u * v)).le]
  exact mul_le_mul_of_nonneg_right (ZetaSum_aux1_3 (Real.exp v))
    (Real.exp_pos _).le

private theorem logKernel_norms {N : ℕ} (hN : 0 < (N : ℝ)) {u : ℝ} (hu : 0 < u) :
    Integrable (logKernel N u) ∧
    Integrable (fun v => ‖logKernel N u v‖ ^ 2) ∧
    (∫ v : ℝ, ‖logKernel N u v‖ ^ 2) ≤ (N : ℝ) ^ (-2 * u) / (8 * u) := by
  let c := Real.log (N : ℝ)
  have hL1majorant : IntegrableOn (fun v : ℝ => (1 / 2 : ℝ) * Real.exp (-u * v))
      (Ioi c) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hu) c).const_mul (1 / 2)
  have hL1 : IntegrableOn (logProfile u) (Ioi c) :=
    hL1majorant.mono' (logProfile_measurable u).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_logProfile_le u))
  have hsq (v : ℝ) :
      ‖logProfile u v‖ ^ 2 ≤ (1 / 4 : ℝ) * Real.exp ((-2 * u) * v) := by
    calc
      _ ≤ ((1 / 2 : ℝ) * Real.exp (-u * v)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_logProfile_le u v)
      _ = _ := by
        have hquarter : ((1 / 2 : ℝ) ^ 2) = 1 / 4 := by norm_num
        rw [mul_pow, hquarter, pow_two (Real.exp (-u * v)), ← Real.exp_add,
          show -u * v + -u * v = (-2 * u) * v by ring]
  have hdecay : -2 * u < 0 := by linarith
  have hL2majorant : IntegrableOn (fun v : ℝ => (1 / 4 : ℝ) * Real.exp ((-2 * u) * v))
      (Ioi c) :=
    (integrableOn_exp_mul_Ioi hdecay c).const_mul (1 / 4)
  have hsqMeas : Measurable (fun v => ‖logProfile u v‖ ^ 2) :=
    (logProfile_measurable u).norm.pow_const 2
  have hL2 : IntegrableOn (fun v => ‖logProfile u v‖ ^ 2) (Ioi c) := by
    apply hL2majorant.mono' hsqMeas.aestronglyMeasurable
    filter_upwards with v
    simpa only [Real.norm_of_nonneg (sq_nonneg ‖logProfile u v‖)] using hsq v
  have hsquares :
      (fun v => ‖logKernel N u v‖ ^ 2) =
        (Ioi c).indicator (fun v => ‖logProfile u v‖ ^ 2) := by
    funext v
    change ‖(Ioi c).indicator (logProfile u) v‖ ^ 2 = _
    by_cases hv : v ∈ Ioi c <;> simp [hv]
  refine ⟨hL1.integrable_indicator measurableSet_Ioi, ?_, ?_⟩
  · rw [hsquares]
    exact hL2.integrable_indicator measurableSet_Ioi
  · rw [hsquares, integral_indicator measurableSet_Ioi]
    calc
      _ ≤ ∫ v : ℝ in Ioi c, (1 / 4 : ℝ) * Real.exp ((-2 * u) * v) :=
        setIntegral_mono_on hL2 hL2majorant measurableSet_Ioi fun v _ => hsq v
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi hdecay]
        have hexp : Real.exp ((-2 * u) * c) = (N : ℝ) ^ (-2 * u) := by
          rw [Real.rpow_def_of_pos hN]
          dsimp [c]
          rw [mul_comm]
        rw [hexp]
        field_simp [hu.ne'] <;> ring

/-- The angular transform of the logarithmic remainder has finite squared mass. -/
private theorem angular_mass {N : ℕ} (hN : 0 < (N : ℝ)) {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => ‖angularFourier (logKernel N u) t‖ ^ 2) ∧
    (∫ t : ℝ, ‖angularFourier (logKernel N u) t‖ ^ 2) ≤
      (2 * Real.pi) * ((N : ℝ) ^ (-2 * u) / (8 * u)) := by
  let g := logKernel N u
  let F := angularFourier g
  obtain ⟨hg, hgSq, hgBound⟩ := logKernel_norms hN hu
  have hgLp : MemLp g 2 :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr hgSq
  have hF : Continuous F := by
    unfold F angularFourier
    exact (continuous_raw_fourier hg).comp (by fun_prop)
  have htwoPi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hcancel :
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (1 / (2 * Real.pi)) = 1 := by
    rw [← ENNReal.ofReal_mul htwoPi.le, mul_one_div_cancel htwoPi.ne', ENNReal.ofReal_one]
  have hsquare (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hgSqNN : 0 ≤ᵐ[volume] (fun v : ℝ => ‖g v‖ ^ 2) :=
    Filter.Eventually.of_forall fun v => sq_nonneg ‖g v‖
  have hFSqNN : 0 ≤ᵐ[volume] (fun t : ℝ => ‖F t‖ ^ 2) :=
    Filter.Eventually.of_forall fun t => sq_nonneg ‖F t‖
  have hmass :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖F t‖ ^ 2)) =
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (∫ v : ℝ, ‖g v‖ ^ 2) := by
    calc
      _ = ∫⁻ t : ℝ, ‖F t‖ₑ ^ 2 := by simp only [hsquare]
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ v : ℝ, ‖g v‖ₑ ^ 2 := by
        rw [angular_extended_plancherel hg hgLp, ← mul_assoc, hcancel, one_mul]
      _ = _ := by
        simp only [← hsquare]
        rw [ofReal_integral_eq_lintegral_ofReal hgSq hgSqNN]
  have hFSqMeas : AEStronglyMeasurable (fun t : ℝ => ‖F t‖ ^ 2) volume :=
    (hF.norm.pow 2).aestronglyMeasurable
  refine ⟨⟨hFSqMeas, (hasFiniteIntegral_iff_ofReal hFSqNN).mpr ?_⟩, ?_⟩
  · rw [hmass]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  · change (∫ t : ℝ, ‖F t‖ ^ 2) ≤ _
    rw [integral_eq_lintegral_of_nonneg_ae hFSqNN hFSqMeas, hmass,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal htwoPi.le,
      ENNReal.toReal_ofReal (integral_nonneg fun v : ℝ => sq_nonneg ‖g v‖)]
    exact mul_le_mul_of_nonneg_left hgBound htwoPi.le

private theorem polynomial_eq_sum_range (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    polynomial N s = ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s := by
  unfold polynomial
  apply Finset.sum_subset
  · intro n hn
    have hn' := (Finset.mem_Icc.mp hn).2
    exact Finset.mem_range.mpr (by omega)
  · intro n hn hn'
    have hlt := Finset.mem_range.mp hn
    have hzero : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp [hzero, Complex.zero_cpow hs]

private theorem continuous_polynomial (N : ℕ) : Continuous (polynomial N) := by
  unfold polynomial
  apply continuous_finsetSum
  intro n hn
  have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  exact continuous_const.div (continuous_const_cpow' hnz)
    (fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hnz))

private def explicitCorrection (N : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2

private theorem actual_error_eq {N : ℕ} (hN : 0 < N) {u t : ℝ} (hu : 0 < u)
    (hs : vertical u t ≠ 1) :
    riemannZeta (vertical u t) - polynomial N (vertical u t) =
      explicitCorrection N (vertical u t) +
        vertical u t * angularFourier (logKernel N u) t := by
  let s := vertical u t
  have hRe : s.re = u := by simp [s, vertical, Complex.mul_re]
  have hRePos : 0 < s.re := by simpa only [hRe] using hu
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hRePos
    exact (lt_irrefl _) hRePos
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrem :
      (∫ x : ℝ in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) =
        angularFourier (logKernel N u) t := by
    simpa only [s, sawtooth, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_intCast] using
      remainder_eq_angular hNreal u t
  have hpole : -((N : ℂ) ^ (1 - s)) / (1 - s) = (N : ℂ) ^ (1 - s) / (s - 1) := by
    conv_lhs => arg 2; rw [show 1 - s = -(s - 1) by ring]
    rw [neg_div_neg_eq]
  change riemannZeta s - polynomial N s =
    explicitCorrection N s + s * angularFourier (logKernel N u) t
  rw [← Zeta0EqZeta hN hRePos hs, riemannZeta0_apply,
    ← polynomial_eq_sum_range N hs0, hrem, hpole, explicitCorrection, neg_div]
  ring

/-- Uniform squared truncation error for the actual Riemann zeta function. -/
theorem dyadic_truncation_mean_square {a b u T : ℝ} (ha : 1 / 2 < a)
    (hau : a ≤ u) (hub : u ≤ b) (hT : 2 ≤ T) :
    IntegrableOn (fun t => ‖riemannZeta (vertical u t) -
      polynomial ⌈T⌉₊ (vertical u t)‖ ^ 2) (paddedBand T) ∧
    (∫ t : ℝ in paddedBand T,
      ‖riemannZeta (vertical u t) - polynomial ⌈T⌉₊ (vertical u t)‖ ^ 2) ≤
      (250 + 2 * (b + 3) ^ 2 * (Real.pi / (4 * a))) * T ^ (2 - 2 * a) := by
  let N : ℕ := ⌈T⌉₊
  let D := paddedBand T
  let J := Icc (-(2 * T + 1)) (2 * T + 1)
  let Q := T ^ (-a)
  let K := (b + 3) * T
  let F := angularFourier (logKernel N u)
  let E := fun t => ‖riemannZeta (vertical u t) - polynomial N (vertical u t)‖ ^ 2
  have ha0 : 0 < a := by linarith
  have hu0 : 0 < u := ha0.trans_le hau
  have hb0 : 0 ≤ b := (hu0.trans_le hub).le
  have hT0 : 0 < T := by linarith
  have hTN : T ≤ (N : ℝ) := Nat.le_ceil T
  have hN0 : 0 < (N : ℝ) := hT0.trans_le hTN
  have hNpos : 0 < N := by exact_mod_cast hN0
  have hN1 : 1 ≤ (N : ℝ) := by linarith
  have hNupper : (N : ℝ) ≤ 2 * T := by
    have hceil : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    linarith
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hT0.le _
  have hQn : (N : ℝ) ^ (-u) ≤ Q := by
    exact (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hau)).trans
      (Real.rpow_le_rpow_of_nonpos hT0 hTN (neg_nonpos.mpr ha0.le))
  have hQ2 : Q ^ 2 = T ^ (-2 * a) := by
    dsimp [Q]
    have hexponent : -a * ((2 : ℕ) : ℝ) = -2 * a := by norm_num <;> ring
    rw [← Real.rpow_mul_natCast hT0.le (-a) 2, hexponent]
  have hK0 : 0 ≤ K := mul_nonneg (by linarith) hT0.le
  have hClosed : IsClosed D := by
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hD : MeasurableSet D := hClosed.measurableSet
  have hDJ : D ⊆ J := fun _ ht => abs_le.mp ht.2
  have hCompact : IsCompact D := isCompact_Icc.of_isClosed_subset hClosed hDJ
  have hJfinite : volume J ≠ ∞ := by
    dsimp [J]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hDfinite : volume D ≠ ∞ :=
    ne_of_lt ((measure_mono hDJ).trans_lt (lt_top_iff_ne_top.mpr hJfinite))
  have hDvol : volume.real D ≤ 5 * T := by
    calc
      _ ≤ volume.real J := measureReal_mono hDJ hJfinite
      _ = 2 * T + 1 - (-(2 * T + 1)) := by
        dsimp [J]
        rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      _ ≤ _ := by linarith
  have hsDist (t : ℝ) (ht : t ∈ D) : T / 2 ≤ ‖vertical u t - 1‖ := by
    have habs : T / 2 ≤ |t| := by linarith [ht.1]
    exact habs.trans (by
      simpa [vertical, Complex.sub_im, Complex.mul_im] using
        Complex.abs_im_le_norm (vertical u t - 1))
  have hsNe (t : ℝ) (ht : t ∈ D) : vertical u t ≠ 1 := by
    intro h
    have hd := hsDist t ht
    rw [h, sub_self, norm_zero] at hd
    linarith
  have hsNorm (t : ℝ) (ht : t ∈ D) : ‖vertical u t‖ ≤ K := by
    calc
      _ ≤ u + |t| := by
        simpa [vertical, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hu0.le] using norm_add_le (u : ℂ) ((t : ℂ) * Complex.I)
      _ ≤ b + 3 * T := by linarith [ht.2]
      _ ≤ K := by
        dsimp [K]
        nlinarith [mul_nonneg hb0 (show 0 ≤ T - 1 by linarith)]
  have hsCont : Continuous (vertical u) := by unfold vertical; fun_prop
  have hZeta : ContinuousOn (fun t => riemannZeta (vertical u t)) D := by
    intro t ht
    exact ((differentiableAt_riemannZeta (hsNe t ht)).continuousAt.comp
      hsCont.continuousAt).continuousWithinAt
  have hE : IntegrableOn E D :=
    ((hZeta.sub ((continuous_polynomial N).comp hsCont).continuousOn).norm.pow
      2).integrableOn_compact hCompact
  obtain ⟨hFInt, hFBound⟩ := angular_mass hN0 hu0
  have hFUniform : (∫ t : ℝ, ‖F t‖ ^ 2) ≤ (Real.pi / (4 * a)) * Q ^ 2 := by
    have hnum : (N : ℝ) ^ (-2 * u) ≤ Q ^ 2 := by
      rw [hQ2]
      have hexponent : -2 * u ≤ -2 * a := by linarith
      exact (Real.rpow_le_rpow_of_exponent_le hN1 hexponent).trans
        (Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith))
    have hdiv : (N : ℝ) ^ (-2 * u) / (8 * u) ≤ Q ^ 2 / (8 * a) := by
      calc
        _ ≤ Q ^ 2 / (8 * u) := div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    calc
      _ ≤ (2 * Real.pi) * ((N : ℝ) ^ (-2 * u) / (8 * u)) := hFBound
      _ ≤ (2 * Real.pi) * (Q ^ 2 / (8 * a)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by field_simp [ha0.ne'] <;> ring
  have hFRestricted :
      (∫ t : ℝ in D, ‖F t‖ ^ 2) ≤ (Real.pi / (4 * a)) * Q ^ 2 :=
    (setIntegral_le_integral hFInt
      (Filter.Eventually.of_forall fun t => sq_nonneg ‖F t‖)).trans hFUniform
  have hPoint (t : ℝ) (ht : t ∈ D) : E t ≤ 50 * Q ^ 2 + (2 * K ^ 2) * ‖F t‖ ^ 2 := by
    let s := vertical u t
    have hRe : s.re = u := by simp [s, vertical, Complex.mul_re]
    have hpow (z : ℂ) : ‖(N : ℂ) ^ z‖ = (N : ℝ) ^ z.re := by
      simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hN0 z
    have hPole : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 4 * Q := by
      have hd := hsDist t ht
      have hd0 : 0 < ‖s - 1‖ := (by linarith : 0 < T / 2).trans_le hd
      rw [norm_div, hpow, Complex.sub_re, Complex.one_re, hRe,
        show 1 - u = 1 + (-u) by ring, Real.rpow_add hN0, Real.rpow_one]
      apply (div_le_iff₀ hd0).mpr
      calc
        _ ≤ (2 * T) * Q :=
          mul_le_mul hNupper hQn (Real.rpow_nonneg hN0.le _) (by positivity)
        _ = (4 * Q) * (T / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
    have hHalf : ‖(N : ℂ) ^ (-s) / 2‖ ≤ Q / 2 := by
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [norm_div, hpow, Complex.neg_re, hRe, htwo]
      exact div_le_div_of_nonneg_right hQn (by norm_num)
    have hExplicit : ‖explicitCorrection N s‖ ≤ 5 * Q := by
      unfold explicitCorrection
      calc
        _ ≤ _ := norm_sub_le _ _
        _ ≤ 4 * Q + Q / 2 := add_le_add hPole hHalf
        _ ≤ _ := by linarith
    have hRemainder : ‖s * F t‖ ≤ K * ‖F t‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hsNorm t ht) (norm_nonneg _)
    change ‖riemannZeta s - polynomial N s‖ ^ 2 ≤ _
    rw [actual_error_eq hNpos hu0 (hsNe t ht)]
    calc
      _ ≤ (5 * Q + K * ‖F t‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
          ((norm_add_le _ _).trans (add_le_add hExplicit hRemainder))
      _ ≤ _ := by nlinarith [sq_nonneg (5 * Q - K * ‖F t‖)]
  have hConst : IntegrableOn (fun _ : ℝ => 50 * Q ^ 2) D :=
    integrableOn_const hDfinite
  have hScaled : IntegrableOn (fun t : ℝ => (2 * K ^ 2) * ‖F t‖ ^ 2) D :=
    (hFInt.integrableOn (s := D)).const_mul (2 * K ^ 2)
  have hPower : T ^ (2 : ℕ) * Q ^ 2 = T ^ (2 - 2 * a) := by
    have hexponent : ((2 : ℕ) : ℝ) + (-2 * a) = 2 - 2 * a := by norm_num <;> ring
    rw [hQ2, ← Real.rpow_natCast T 2, ← Real.rpow_add hT0, hexponent]
  change IntegrableOn E D ∧ (∫ t : ℝ in D, E t) ≤ _
  refine ⟨hE, ?_⟩
  calc
    _ ≤ ∫ t : ℝ in D, 50 * Q ^ 2 + (2 * K ^ 2) * ‖F t‖ ^ 2 :=
      setIntegral_mono_on hE (hConst.add hScaled) hD hPoint
    _ = volume.real D * (50 * Q ^ 2) + (2 * K ^ 2) * (∫ t : ℝ in D, ‖F t‖ ^ 2) := by
      rw [integral_add hConst hScaled, setIntegral_const, smul_eq_mul, integral_const_mul]
    _ ≤ (5 * T) * (50 * Q ^ 2) + (2 * K ^ 2) * ((Real.pi / (4 * a)) * Q ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hDvol (by positivity))
        (mul_le_mul_of_nonneg_left hFRestricted (by positivity))
    _ ≤ (5 * T ^ 2) * (50 * Q ^ 2) + (2 * K ^ 2) * ((Real.pi / (4 * a)) * Q ^ 2) := by
      have hTT : T ≤ T ^ 2 := by nlinarith [mul_nonneg hT0.le (show 0 ≤ T - 1 by linarith)]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTT (by norm_num))
          (by positivity)) le_rfl
    _ = _ := by
      rw [← hPower]
      dsimp [K]
      ring

end

end D5.S3.Weil.ZetaTruncationMeanSquare
