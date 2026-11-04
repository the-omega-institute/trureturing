/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-digamma-residual-domain-and-series)
   anchors: []
   utility: none
   digest: Actual quarter-digamma resolvent L1 domain, exact positive rational-layer norm series and bare increment HasSum. -/

/- Selected natural owner: D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1.
Standalone actual digamma residual family, using existing PUBLIC GammaSeries
HasSum at z=-3/4+ix and the existing digamma recurrence. No import, append,
visibility patch or mutation of ArchimedeanJumpDecomposition is needed.
The only public theorem has a>0 and five outputs; its final output is the
literal bare increment HasSum needed by the finite spectral MCT consumer.
All private suppliers have actual consumers in this unit.
No energy-positivity or RH result is claimed.
-/

import D5.S3.Weil.ZetaGamma.GammaMu
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1

open MeasureTheory Set Filter
open scoped ENNReal Topology

/- Private actual-weight notation and direct public-series consumption.
There is no ArchimedeanJumpDecomposition import or private-visibility patch.
The public complex series is used at z=-3/4+ix so that z+n+1=n+1/4+ix.
Taking the difference at x and 0 cancels the common harmonic term.
The existing digamma recurrence supplies psi(z)+1/z=psi(z+1).
All these bridges are used on the actual resolvent proof path. -/
private def gammaResidualQuarterWeight (x : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
    (Complex.digamma (1 / 4)).re

private def gammaResidualIncrement (x : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1 / 4) -
    ((n : ℝ) + 1 / 4) / (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2)

private theorem gamma_residual_quarter_hasSum (x : ℝ) :
    HasSum (gammaResidualIncrement x) (gammaResidualQuarterWeight x) := by
  let z : ℝ → ℂ := fun t => (((-3 / 4 : ℝ) : ℂ)) + Complex.I * (t : ℂ)
  have hmem (t : ℝ) : z t ∈ Complex.integerComplement := by
    have h := Zeta23.MuFields.abscissa_mem
      (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) t
    have hQ : ((1 / 4 : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
      simpa using h
    have heq : z t = ((1 / 4 : ℂ) + Complex.I * (t : ℂ)) + ((-1 : ℤ) : ℂ) := by
      dsimp only [z]
      push_cast
      ring
    rw [heq]
    exact (Complex.add_intCast_mem_integerComplement (-1)).2 hQ
  have hRec (t : ℝ) : Complex.digamma (z t) + 1 / z t =
      Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ)) := by
    have hpole (m : ℕ) : z t ≠ -(m : ℂ) := by
      intro hm
      apply hmem t
      refine ⟨-(m : ℤ), ?_⟩
      simpa only [Int.cast_neg, Int.cast_natCast] using hm.symm
    have h := Complex.digamma_apply_add_one (z t) hpole
    have heq : z t + 1 = (1 / 4 : ℂ) + Complex.I * (t : ℂ) := by
      dsimp only [z]
      push_cast
      ring
    rw [heq] at h
    simpa only [one_div] using h.symm
  have hL (t : ℝ) : Complex.digamma (z t) +
      (Real.eulerMascheroniConstant : ℂ) + 1 / z t =
        Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ)) +
          (Real.eulerMascheroniConstant : ℂ) := by
    linear_combination hRec t
  have hLimit : (Complex.digamma (z x) + (Real.eulerMascheroniConstant : ℂ) +
      1 / z x).re -
      (Complex.digamma (z 0) + (Real.eulerMascheroniConstant : ℂ) + 1 / z 0).re =
        gammaResidualQuarterWeight x := by
    rw [hL x, hL 0]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.add_re, Complex.ofReal_re]
    unfold gammaResidualQuarterWeight
    ring
  have hrow (n : ℕ) :
      ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (z x + n + 1)).re -
        ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (z 0 + n + 1)).re =
          gammaResidualIncrement x n := by
    dsimp only [z]
    rw [Zeta23.MuFields.re_term_eq, Zeta23.MuFields.re_term_eq]
    have heq : (n : ℝ) + 1 + (-3 / 4 : ℝ) = (n : ℝ) + 1 / 4 := by ring
    simp only [heq, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    unfold gammaResidualIncrement
    have hc : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
    have hden : x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2 ≠ 0 := by positivity
    have hden' : ((n : ℝ) + 1 / 4) ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp [hc, hden, hden']
    <;> ring
  have h := (Complex.hasSum_re
    (Zeta23.DigammaSeries.hasSum_digamma_series (hmem x))).sub
      (Complex.hasSum_re (Zeta23.DigammaSeries.hasSum_digamma_series (hmem 0)))
  simpa only [hrow, hLimit] using h

private theorem gamma_residual_quarter_eq_tsum (x : ℝ) :
    gammaResidualQuarterWeight x = ∑' n : ℕ, gammaResidualIncrement x n :=
  (gamma_residual_quarter_hasSum x).tsum_eq.symm

private theorem gamma_residual_quarter_nonnegative (x : ℝ) :
    0 ≤ gammaResidualQuarterWeight x := by
  rw [gamma_residual_quarter_eq_tsum]
  apply tsum_nonneg
  intro n
  unfold gammaResidualIncrement
  have hc : 0 < (n : ℝ) + 1 / 4 := by positivity
  have hd : 0 < x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2 := by positivity
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hd hc).2
  nlinarith [sq_nonneg x]

private theorem gamma_residual_quarter_measurable : Measurable gammaResidualQuarterWeight := by
  have heq : gammaResidualQuarterWeight =
      fun x : ℝ => ∑' n : ℕ, gammaResidualIncrement x n :=
    funext gamma_residual_quarter_eq_tsum
  rw [heq]
  exact Measurable.tsum fun n => by
    unfold gammaResidualIncrement
    fun_prop

private def gammaResidualDensity (a c x : ℝ) : ℝ :=
  x ^ 2 / (c * (x ^ 2 + c ^ 2) * (x ^ 2 + a ^ 2))

/- Direct pinned whole-line Cauchy use, private and consumed below.
The Cauchy integral is not re-proved and is not a public new claim. -/
private theorem gamma_residual_cauchy {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) volume ∧
      (∫ x : ℝ, (x ^ 2 + a ^ 2)⁻¹) = Real.pi / a := by
  have hscale (x : ℝ) : (x ^ 2 + a ^ 2)⁻¹ =
      a⁻¹ ^ 2 * (1 + (a⁻¹ * x) ^ 2)⁻¹ := by
    field_simp [ha.ne', show x ^ 2 + a ^ 2 ≠ 0 by positivity,
      show 1 + (a⁻¹ * x) ^ 2 ≠ 0 by positivity]
    <;> ring
  have hi : Integrable (fun x : ℝ => (x ^ 2 + a ^ 2)⁻¹) volume := by
    apply ((integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne')).const_mul
      (a⁻¹ ^ 2)).congr
    exact Eventually.of_forall fun x => (hscale x).symm
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x : ℝ, a⁻¹ ^ 2 * (1 + (a⁻¹ * x) ^ 2)⁻¹ :=
      integral_congr_ae (Eventually.of_forall hscale)
    _ = a⁻¹ ^ 2 * (Real.pi / |a⁻¹|) := by
      rw [integral_const_mul, integral_univ_inv_one_add_mul_sq]
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr ha)]
      field_simp [ha.ne']
      <;> ring

private theorem gamma_residual_density_nonneg {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (x : ℝ) :
    0 ≤ gammaResidualDensity a c x := by
  unfold gammaResidualDensity
  positivity

private theorem gamma_residual_density_measurable (a c : ℝ) :
    Measurable (gammaResidualDensity a c) := by
  unfold gammaResidualDensity
  fun_prop

private theorem gamma_residual_density_cauchy_bound {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (x : ℝ) :
    gammaResidualDensity a c x ≤ (1 / c) * (x ^ 2 + a ^ 2)⁻¹ := by
  have hden : 0 < x ^ 2 + c ^ 2 := by positivity
  have hratio : x ^ 2 / (x ^ 2 + c ^ 2) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith)
  have heq : gammaResidualDensity a c x =
      (x ^ 2 / (x ^ 2 + c ^ 2)) * ((1 / c) * (x ^ 2 + a ^ 2)⁻¹) := by
    unfold gammaResidualDensity
    field_simp [hc.ne', hden.ne', show x ^ 2 + a ^ 2 ≠ 0 by positivity]
    <;> ring
  rw [heq]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio
    (by positivity : 0 ≤ (1 / c) * (x ^ 2 + a ^ 2)⁻¹)

private theorem gamma_residual_density_integrable {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Integrable (gammaResidualDensity a c) volume := by
  apply ((gamma_residual_cauchy ha).1.const_mul (1 / c)).mono'
    (gamma_residual_density_measurable a c).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (gamma_residual_density_nonneg ha hc x)]
    exact gamma_residual_density_cauchy_bound ha hc x

private theorem gamma_residual_integral_nonresonant {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hne : a ≠ c) :
    (∫ x : ℝ, gammaResidualDensity a c x) = Real.pi / (c * (a + c)) := by
  have hD : a ^ 2 - c ^ 2 ≠ 0 := by
    rw [show a ^ 2 - c ^ 2 = (a - c) * (a + c) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hne) (add_pos ha hc).ne'
  have hdecomp (x : ℝ) : gammaResidualDensity a c x =
      (a ^ 2 / (c * (a ^ 2 - c ^ 2))) * (x ^ 2 + a ^ 2)⁻¹ -
        (c / (a ^ 2 - c ^ 2)) * (x ^ 2 + c ^ 2)⁻¹ := by
    unfold gammaResidualDensity
    field_simp [hc.ne', hD, show x ^ 2 + a ^ 2 ≠ 0 by positivity,
      show x ^ 2 + c ^ 2 ≠ 0 by positivity]
    <;> ring
  have hA := (gamma_residual_cauchy ha).1.const_mul
    (a ^ 2 / (c * (a ^ 2 - c ^ 2)))
  have hC := (gamma_residual_cauchy hc).1.const_mul (c / (a ^ 2 - c ^ 2))
  calc
    _ = ∫ x : ℝ,
        (a ^ 2 / (c * (a ^ 2 - c ^ 2))) * (x ^ 2 + a ^ 2)⁻¹ -
          (c / (a ^ 2 - c ^ 2)) * (x ^ 2 + c ^ 2)⁻¹ :=
      integral_congr_ae (Eventually.of_forall hdecomp)
    _ = (a ^ 2 / (c * (a ^ 2 - c ^ 2))) * (Real.pi / a) -
        (c / (a ^ 2 - c ^ 2)) * (Real.pi / c) := by
      rw [integral_sub hA hC, integral_const_mul, integral_const_mul,
        (gamma_residual_cauchy ha).2, (gamma_residual_cauchy hc).2]
    _ = _ := by
      field_simp [ha.ne', hc.ne', hD, (add_pos ha hc).ne']
      <;> ring

/- When a equals a layer parameter c_n, it must not pass through division by
a^2-c^2. A positive sequence c_j down to a has a single genuine L1
Cauchy majorant, so DCT supplies the resonance value without an assumed
parameter-continuity or repeated-pole integral supplier. -/
private theorem gamma_residual_integral_resonant {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, gammaResidualDensity a a x) = Real.pi / (2 * a ^ 2) := by
  let c : ℕ → ℝ := fun j => a + 1 / ((j : ℝ) + 1)
  have hca (j : ℕ) : a < c j := by
    dsimp only [c]
    exact lt_add_of_pos_right a (by positivity)
  have hc (j : ℕ) : 0 < c j := ha.trans (hca j)
  have hcLimit : Tendsto c atTop (𝓝 a) := by
    simpa only [c, add_zero] using
      (show Tendsto (fun _ : ℕ => a) atTop (𝓝 a) from tendsto_const_nhds).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hMajor : Integrable (fun x : ℝ =>
      (1 / a) * (x ^ 2 + a ^ 2)⁻¹) volume :=
    (gamma_residual_cauchy ha).1.const_mul (1 / a)
  have hBound (j : ℕ) : ∀ᵐ x : ℝ ∂volume,
      ‖gammaResidualDensity a (c j) x‖ ≤
        (1 / a) * (x ^ 2 + a ^ 2)⁻¹ := by
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (gamma_residual_density_nonneg ha (hc j) x)]
      exact (gamma_residual_density_cauchy_bound ha (hc j) x).trans
        (mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le ha (hca j).le) (by positivity))
  have hPoint : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun j => gammaResidualDensity a (c j) x) atTop
        (𝓝 (gammaResidualDensity a a x)) := by
    exact Eventually.of_forall fun x => by
      have hCont : ContinuousAt (fun b : ℝ => gammaResidualDensity a b x) a := by
        unfold gammaResidualDensity
        fun_prop (disch := positivity)
      exact hCont.tendsto.comp hcLimit
  have hInt := tendsto_integral_of_dominated_convergence
    (fun x : ℝ => (1 / a) * (x ^ 2 + a ^ 2)⁻¹)
    (fun j => (gamma_residual_density_measurable a (c j)).aestronglyMeasurable)
    hMajor hBound hPoint
  have hValues (j : ℕ) :
      (∫ x : ℝ, gammaResidualDensity a (c j) x) =
        Real.pi / (c j * (a + c j)) :=
    gamma_residual_integral_nonresonant ha (hc j) (ne_of_lt (hca j))
  simp_rw [hValues] at hInt
  have hValueLimit : Tendsto
      (fun j => Real.pi / (c j * (a + c j))) atTop
        (𝓝 (Real.pi / (a * (a + a)))) := by
    exact tendsto_const_nhds.div (hcLimit.mul (tendsto_const_nhds.add hcLimit))
      (by positivity : a * (a + a) ≠ 0)
  have h := tendsto_nhds_unique hInt hValueLimit
  calc
    _ = Real.pi / (a * (a + a)) := h
    _ = _ := by congr 1; ring

private theorem gamma_residual_density_domain_and_norm {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Integrable (gammaResidualDensity a c) volume ∧
      (∫ x : ℝ, ‖gammaResidualDensity a c x‖) =
        Real.pi / (c * (a + c)) := by
  refine ⟨gamma_residual_density_integrable ha hc, ?_⟩
  have hnorm : (fun x : ℝ => ‖gammaResidualDensity a c x‖) =
      gammaResidualDensity a c := by
    funext x
    exact Real.norm_of_nonneg (gamma_residual_density_nonneg ha hc x)
  rw [hnorm]
  by_cases hac : a = c
  · subst c
    simpa only [show a * (a + a) = 2 * a ^ 2 by ring] using
      gamma_residual_integral_resonant ha
  · exact gamma_residual_integral_nonresonant ha hc hac

private theorem gamma_residual_shifted_pseries (p : ℕ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1 / 4) ^ p)) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 / 4) (p : ℝ)).2
    (by exact_mod_cast hp)
  convert h using 1
  funext n
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 1 / 4), Real.rpow_natCast]

private theorem gamma_residual_layer_norm_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => Real.pi /
      (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4)))) := by
  have hbig := (gamma_residual_shifted_pseries 2 (by norm_num)).mul_left Real.pi
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbig
  have hc : 0 < (n : ℝ) + 1 / 4 := by positivity
  change Real.pi / _ ≤ Real.pi * (1 / (((n : ℝ) + 1 / 4) ^ 2))
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left Real.pi_pos.le (sq_pos_of_pos hc)
    (by nlinarith [mul_nonneg ha.le hc.le])

private theorem gamma_residual_actual_pointwise_series (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasSum (fun n : ℕ => gammaResidualDensity a ((n : ℝ) + 1 / 4) x)
      (gammaResidualQuarterWeight x / (x ^ 2 + a ^ 2)) := by
  have hs := (gamma_residual_quarter_hasSum x).div_const (x ^ 2 + a ^ 2)
  have hrow (n : ℕ) :
      gammaResidualDensity a ((n : ℝ) + 1 / 4) x =
        gammaResidualIncrement x n / (x ^ 2 + a ^ 2) := by
    unfold gammaResidualIncrement
    unfold gammaResidualDensity
    have hc : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
    have hxc : x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2 ≠ 0 := by positivity
    have hcx : ((n : ℝ) + 1 / 4) ^ 2 + x ^ 2 ≠ 0 := by positivity
    have hxa : x ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp [hc, hxc, hcx, hxa]
    <;> ring
  have hfun : (fun n : ℕ => gammaResidualDensity a ((n : ℝ) + 1 / 4) x) =
      fun n : ℕ => gammaResidualIncrement x n / (x ^ 2 + a ^ 2) := funext hrow
  rw [hfun]
  exact hs

/-- Actual L1 Fourier multiplier needed for the rational residual of the
literal quarter digamma family for every a > 0. Every layer is nonnegative;
any resonance c_n=a is paid separately by DCT. The actual quarter digamma series supplies the
pointwise sum, then Tonelli pays L1 before any Gamma cross/Fubini use.
No actual graph premise, Fourier cross identity, proxy energy or RH
conclusion is assumed. All integrals are full real-line Lebesgue ones. -/
theorem actual_digamma_quarter_resolvent_l1_domain_and_series (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
      (Complex.digamma (1 / 4)).re) / (x ^ 2 + a ^ 2)) volume ∧
      Summable (fun n : ℕ => Real.pi /
        (((n : ℝ) + 1 / 4) * (a + ((n : ℝ) + 1 / 4)))) ∧
      (∀ n : ℕ,
        Integrable (fun x : ℝ => x ^ 2 /
          (((n : ℝ) + 1 / 4) * (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2) *
            (x ^ 2 + a ^ 2))) volume ∧
        (∫ x : ℝ, ‖x ^ 2 /
          (((n : ℝ) + 1 / 4) * (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2) *
            (x ^ 2 + a ^ 2))‖) =
          Real.pi / (((n : ℝ) + 1 / 4) *
            (a + ((n : ℝ) + 1 / 4)))) ∧
      ((∫ x : ℝ, ‖((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
      (Complex.digamma (1 / 4)).re) / (x ^ 2 + a ^ 2)‖) =
        ∑' n : ℕ, Real.pi / (((n : ℝ) + 1 / 4) *
          (a + ((n : ℝ) + 1 / 4)))) ∧
      (∀ x : ℝ,
        HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) -
          ((n : ℝ) + 1 / 4) / (x ^ 2 + ((n : ℝ) + 1 / 4) ^ 2))
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x : ℂ))).re -
            (Complex.digamma (1 / 4)).re)) := by
  let P : ℕ → ℝ → ℝ := fun n => gammaResidualDensity a ((n : ℝ) + 1 / 4)
  let q : ℝ → ℝ := fun x => gammaResidualQuarterWeight x / (x ^ 2 + a ^ 2)
  have hPpos (n : ℕ) (x : ℝ) : 0 ≤ P n x :=
    gamma_residual_density_nonneg ha (by positivity) x
  have hPi (n : ℕ) : Integrable (P n) volume :=
    gamma_residual_density_integrable ha (by positivity)
  have hPn (n : ℕ) : (∫ x : ℝ, ‖P n x‖) =
      Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4))) :=
    (gamma_residual_density_domain_and_norm ha (by positivity)).2
  have hInt (n : ℕ) : (∫ x : ℝ, P n x) =
      Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4))) := by
    calc
      _ = ∫ x : ℝ, ‖P n x‖ := integral_congr_ae
        (Eventually.of_forall fun x => (Real.norm_of_nonneg (hPpos n x)).symm)
      _ = _ := hPn n
  have hqpos (x : ℝ) : 0 ≤ q x :=
    div_nonneg (gamma_residual_quarter_nonnegative x) (by positivity)
  have hqm : AEStronglyMeasurable q volume :=
    (gamma_residual_quarter_measurable.div (by fun_prop)).aestronglyMeasurable
  have hPLin (n : ℕ) : (∫⁻ x : ℝ, ENNReal.ofReal (P n x)) =
      ENNReal.ofReal (Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4)))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hPi n)
      (Eventually.of_forall (hPpos n)), hInt n]
  have hLin : (∫⁻ x : ℝ, ENNReal.ofReal (q x)) =
      ENNReal.ofReal (∑' n : ℕ, Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4)))) := by
    calc
      _ = ∫⁻ x : ℝ, ∑' n : ℕ, ENNReal.ofReal (P n x) := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          have hs := gamma_residual_actual_pointwise_series a ha x
          change ENNReal.ofReal
            (gammaResidualQuarterWeight x / (x ^ 2 + a ^ 2)) =
              ∑' n : ℕ, ENNReal.ofReal (P n x)
          rw [← hs.tsum_eq]
          exact ENNReal.ofReal_tsum_of_nonneg (fun n => hPpos n x) hs.summable
      _ = ∑' n : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal (P n x) :=
        lintegral_tsum (fun n =>
          (ENNReal.measurable_ofReal.comp
            (gamma_residual_density_measurable a ((n : ℝ) + 1 / 4))).aemeasurable)
      _ = ∑' n : ℕ, ENNReal.ofReal (Real.pi / (((n : ℝ) + 1 / 4) *
          (a + ((n : ℝ) + 1 / 4)))) := by simp_rw [hPLin]
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (gamma_residual_layer_norm_summable a ha)).symm
  have hqi : Integrable q volume := by
    refine ⟨hqm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hqpos)).2 ?_⟩
    rw [hLin]
    exact ENNReal.ofReal_lt_top
  have hRealInt : (∫ x : ℝ, q x) =
      ∑' n : ℕ, Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4))) := by
    have hSumNonneg : 0 ≤ ∑' n : ℕ, Real.pi / (((n : ℝ) + 1 / 4) *
        (a + ((n : ℝ) + 1 / 4))) :=
      tsum_nonneg fun n => by positivity
    have h := (ofReal_integral_eq_lintegral_ofReal hqi
      (Eventually.of_forall hqpos)).trans hLin
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hqpos),
      ENNReal.toReal_ofReal hSumNonneg] using ht
  refine ⟨hqi, gamma_residual_layer_norm_summable a ha, ?_, ?_, ?_⟩
  · intro n
    exact gamma_residual_density_domain_and_norm ha (by positivity)
  · calc
      _ = ∫ x : ℝ, q x := integral_congr_ae
        (Eventually.of_forall fun x => Real.norm_of_nonneg (hqpos x))
      _ = _ := hRealInt
  · intro x
    change HasSum (gammaResidualIncrement x) (gammaResidualQuarterWeight x)
    exact gamma_residual_quarter_hasSum x

end D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
