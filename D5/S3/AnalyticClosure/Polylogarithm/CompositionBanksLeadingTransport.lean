/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksLeadingTransport
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private leading-block transport for the actual positive-composition branch. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
import D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport

open D5.S3.AnalyticClosure.Polylogarithm
open CompositionDisk CompositionBoundary CompositionContinuation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open private radial_div_bound radial_majorant_integrable radial_div_uniform_bound
  inner_arc_decay from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
open private admissibleRemainder suffixConstant leadingOneRemainder from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction

private def polynomialPrimitive : Polynomial ℝ → Polynomial ℝ := fun P ↦
  P.sum fun n a ↦ Polynomial.C (a / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)
private theorem leading_remainder_ray_limit : ∀ (q : ℕ) (suffix : List ℕ+)
    (P : Polynomial ℝ) (ρ C : ℝ) (M : ℕ),
    0 < ρ → 0 ≤ C →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) →
    ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ∃ rayConstant : ℂ,
        Tendsto
          (fun eps : ℝ ↦
            CompositionContinuation.continued
                (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
                  (1 - (eps : ℂ) * w) -
              Polynomial.aeval (-Complex.log ((eps : ℂ) * w))
                (polynomialPrimitive P))
          (𝓝[>] 0) (𝓝 rayConstant) := by
  intro q suffix P ρ C M hρ hC hbound w hw hw0 hwrho
  let E : ℂ → ℂ := fun u ↦
    CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) -
      Polynomial.aeval (-Complex.log u) P
  let F : ℂ → ℂ := fun u ↦
    CompositionContinuation.continued
        (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - u) -
      Polynomial.aeval (-Complex.log u) (polynomialPrimitive P)
  let integrand : ℝ → ℂ := fun t ↦ w * (-(E ((t : ℂ) * w)) / ((t : ℂ) * w))
  let majorant : ℝ → ℝ := fun t ↦
    C * ‖w‖ * t ^ (1 - 1) *
      (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M
  let Ecut : ℂ → ℂ := fun u ↦
    if u ∈ Complex.slitPlane ∧ ‖u‖ < ρ then -E u else 0
  have radial_mem_slit : ∀ (u : ℂ) (t : ℝ),
      u ∈ Complex.slitPlane → 0 < t → (t : ℂ) * u ∈ Complex.slitPlane := by
    intro u t hu ht
    rw [Complex.mem_slitPlane_iff] at hu ⊢
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact hu.imp (fun h ↦ mul_pos ht h) (mul_ne_zero (ne_of_gt ht))
  have quotient_continuous : ContinuousOn (fun u : ℂ ↦ -(E u) / u)
      Complex.slitPlane := by
    intro u hu
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    have hcontinued : ContinuousAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - v)) u :=
      ContinuousAt.comp (((CompositionSlit.result).2.1 _).1 (1 - u) hω).continuousAt
        (by fun_prop)
    have hlog := (Complex.hasDerivAt_log hu).neg
    have hpoly : ContinuousAt
        (fun v : ℂ ↦ Polynomial.aeval ((-Complex.log) v) P) u :=
      ((P.hasDerivAt_aeval ((-Complex.log) u)).comp u hlog).continuousAt
    exact ((hcontinued.sub hpoly).neg.div continuousAt_id hu0).continuousWithinAt
  have remainder_deriv : ∀ u : ℂ, u ∈ Complex.slitPlane →
      HasDerivAt F (-(E u) / u) u := by
    intro u hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    obtain ⟨_, _, _, leading_deriv, _⟩ := CompositionSlit.result
    have hz := leading_deriv (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) hω
    have hinner : HasDerivAt (fun v : ℂ ↦ 1 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℂ)
    have hactual : HasDerivAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix)) (1 - v))
        (-CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u) u := by
      simpa [Function.comp_def, mul_neg, neg_div] using hz.comp u hinner
    have hprimitiveDerivative : (polynomialPrimitive P).derivative = P := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_derivative]
      simp [polynomialPrimitive, Polynomial.sum_def]
      by_cases hcoeff : P.coeff n = 0 <;> simp [hcoeff] <;> field_simp
    have hpoly := (polynomialPrimitive P).hasDerivAt_aeval (-Complex.log u)
    have hlog := (Complex.hasDerivAt_log hu).neg
    have hcomp := hpoly.comp u hlog
    rw [hprimitiveDerivative] at hcomp
    have hpolyScalar : Polynomial.aeval (-Complex.log u) P * (-u⁻¹) =
        -(Polynomial.aeval (-Complex.log u) P) / u := by
      rw [div_eq_mul_inv]
      ring
    rw [hpolyScalar] at hcomp
    have hsub := hactual.sub hcomp
    have hscalar :
        -CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u -
          (-(Polynomial.aeval (-Complex.log u) P) / u) =
        -(E u) / u := by
      dsimp only [E]
      ring
    rw [hscalar] at hsub
    change HasDerivAt F (-(E u) / u) u at hsub
    simpa only [F, List.replicate_succ, List.cons_append] using hsub
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw0)
  have hEcut : ∀ u : ℂ, u ≠ 0 →
      ‖Ecut u‖ ≤ C * ‖u‖ ^ 1 * (1 + ‖-Complex.log u‖) ^ M := by
    intro u hu
    by_cases hcut : u ∈ Complex.slitPlane ∧ ‖u‖ < ρ
    · rw [show Ecut u = -E u by simp [Ecut, hcut], norm_neg, pow_one]
      exact hbound u hcut.1 (norm_pos_iff.mpr hu) hcut.2
    · rw [show Ecut u = 0 by simp [Ecut, hcut], norm_zero, pow_one]
      exact mul_nonneg (mul_nonneg hC (norm_nonneg u))
        (pow_nonneg (by positivity) M)
  have hline : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖integrand t‖ ≤ majorant t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htwslit := radial_mem_slit w t hw ht0
    have htwnorm : ‖(t : ℂ) * w‖ < ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hwrho
    have hcut : Ecut ((t : ℂ) * w) = -E ((t : ℂ) * w) := by
      apply if_pos
      exact ⟨htwslit, htwnorm⟩
    simpa [integrand, majorant, hcut] using
      (radial_div_bound Ecut C 1 M hC (by omega) w hwne hEcut t ht)
  have hcont : ContinuousOn integrand (Set.Ioc (0 : ℝ) 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.comp quotient_continuous (by fun_prop)
    intro t ht
    exact radial_mem_slit w t hw ht.1
  have hmajor : IntervalIntegrable majorant MeasureTheory.volume 0 1 := by
    have hbase := radial_majorant_integrable ‖-Complex.log w‖ 1 M
      (norm_nonneg _) (by omega)
    have hscaled := hbase.const_mul (C * ‖w‖)
    simpa [majorant, mul_assoc] using hscaled
  have hintegrable : IntervalIntegrable integrand MeasureTheory.volume 0 1 := by
    apply hmajor.mono_fun'
    · simpa [Set.uIoc_of_le zero_le_one] using
        hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hline t (by simpa [Set.uIoc_of_le zero_le_one] using ht)
  let rayConstant : ℂ := F w - ∫ t in (0 : ℝ)..1, integrand t
  refine ⟨rayConstant, ?_⟩
  have hprimitive : ContinuousOn
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (Set.uIcc (0 : ℝ) 1) := by
    apply intervalIntegral.continuousOn_primitive_interval_left
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hintegrable
  have huIcc : Set.uIcc (0 : ℝ) 1 ∈ 𝓝[>] 0 := by
    apply mem_of_superset (Ioo_mem_nhdsGT zero_lt_one)
    intro eps heps
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨heps.1.le, heps.2.le⟩
  have hintegralLimit : Tendsto
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, integrand t)) := by
    exact (hprimitive 0 Set.left_mem_uIcc).mono_of_mem_nhdsWithin huIcc
  have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      F ((eps : ℂ) * w) = F w - ∫ t in eps..1, integrand t := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with eps heps
    have hderiv : ∀ t ∈ Set.uIcc eps 1,
        HasDerivAt (fun x : ℝ ↦ F ((x : ℂ) * w))
          (w * (-(E ((t : ℂ) * w)) / ((t : ℂ) * w))) t := by
      intro t ht
      rw [Set.uIcc_of_le heps.2.le] at ht
      have htw := radial_mem_slit w t hw (heps.1.trans_le ht.1)
      have hline : HasDerivAt (fun u : ℂ ↦ u * w) w (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const w
      simpa only [Function.comp_def, mul_comm] using
        ((remainder_deriv ((t : ℂ) * w) htw).comp (t : ℂ) hline).comp_ofReal
    have hint : IntervalIntegrable integrand MeasureTheory.volume eps 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.comp quotient_continuous (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le heps.2.le] at ht
      exact radial_mem_slit w t hw (heps.1.trans_le ht.1)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hftc' : (∫ t in eps..1, integrand t) = F w - F ((eps : ℂ) * w) := by
      simpa [integrand] using hftc
    calc
      F ((eps : ℂ) * w) = F w - (F w - F ((eps : ℂ) * w)) := by ring
      _ = F w - ∫ t in eps..1, integrand t := by rw [← hftc']
  exact (tendsto_const_nhds.sub hintegralLimit :
    Tendsto (fun eps : ℝ ↦ F w - ∫ t in eps..1, integrand t)
      (𝓝[>] 0) (𝓝 rayConstant)).congr' (Filter.EventuallyEq.symm hformula)
private theorem leading_remainder_positive_ray_limit_real : ∀ (q : ℕ) (suffix : List ℕ+)
    (P : Polynomial ℝ) (ρ C : ℝ) (M : ℕ),
    0 < ρ → 0 ≤ C →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) →
    ∀ r : ℝ, 0 < r → r < ρ →
      ∃ rayConstant : ℝ,
        Tendsto
          (fun eps : ℝ ↦
            CompositionContinuation.continued
                (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
                  (1 - (eps : ℂ) * (r : ℂ)) -
              Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
                (polynomialPrimitive P))
          (𝓝[>] 0) (𝓝 (rayConstant : ℂ)) := by
  intro q suffix P ρ C M hρ hC hbound r hr hrρ
  have hrslit : (r : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hr
  have radial_mem_slit : ∀ (u : ℂ) (t : ℝ),
      u ∈ Complex.slitPlane → 0 < t → (t : ℂ) * u ∈ Complex.slitPlane := by
    intro u t hu ht
    rw [Complex.mem_slitPlane_iff] at hu ⊢
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact hu.imp (fun h ↦ mul_pos ht h) (mul_ne_zero (ne_of_gt ht))
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  obtain ⟨rayConstant, hlimit⟩ :=
    leading_remainder_ray_limit q suffix P ρ C M hρ hC hbound (r : ℂ)
      hrslit (norm_pos_iff.mpr (ofReal_ne_zero.mpr (ne_of_gt hr)))
      (by rw [hrnorm]; exact hrρ)
  have hreal : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      conj
          (CompositionContinuation.continued
              (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
                (1 - (eps : ℂ) * (r : ℂ)) -
            Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
              (polynomialPrimitive P)) =
        CompositionContinuation.continued
            (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
              (1 - (eps : ℂ) * (r : ℂ)) -
          Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
            (polynomialPrimitive P) := by
    filter_upwards [eventually_mem_nhdsWithin] with eps heps
    have heps0 : 0 < eps := heps
    have hprod : 0 < eps * r := mul_pos heps0 hr
    have hwslit : (eps : ℂ) * (r : ℂ) ∈ Complex.slitPlane :=
      radial_mem_slit (r : ℂ) eps hrslit heps0
    have hω : 1 - (eps : ℂ) * (r : ℂ) ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hwslit
    have hcontinued :=
      ((CompositionSlit.result).2.2.1 (1 : ℕ+)
        (List.replicate q (1 : ℕ+) ++ suffix)).2.2.2
          (1 - (eps : ℂ) * (r : ℂ)) hω
    have hcontinuedReal :
        conj (CompositionContinuation.continued
          (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
            (1 - (eps : ℂ) * (r : ℂ))) =
          CompositionContinuation.continued
            (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
              (1 - (eps : ℂ) * (r : ℂ)) := by
      rw [List.replicate_succ, List.cons_append]
      calc
        conj (CompositionContinuation.continued
            ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix))
              (1 - (eps : ℂ) * (r : ℂ))) =
            CompositionContinuation.continued
              ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix))
                (conj (1 - (eps : ℂ) * (r : ℂ))) := hcontinued.symm
        _ = CompositionContinuation.continued
              ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix))
                (1 - (eps : ℂ) * (r : ℂ)) := by simp
    have hlogReal :
        conj (-Complex.log ((eps : ℂ) * (r : ℂ))) =
          -Complex.log ((eps : ℂ) * (r : ℂ)) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_log hprod.le]
      simp
    have hpolyReal :
        conj (Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
            (polynomialPrimitive P)) =
          Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
            (polynomialPrimitive P) := by
      calc
        conj (Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
            (polynomialPrimitive P)) =
            Polynomial.aeval (conj (-Complex.log ((eps : ℂ) * (r : ℂ))))
              (polynomialPrimitive P) :=
          (Polynomial.aeval_conj (polynomialPrimitive P)
            (-Complex.log ((eps : ℂ) * (r : ℂ)))).symm
        _ = Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
              (polynomialPrimitive P) := by rw [hlogReal]
    rw [map_sub, hcontinuedReal, hpolyReal]
  have hconjLimit : Tendsto
      (fun eps : ℝ ↦
        conj
          (CompositionContinuation.continued
              (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
                (1 - (eps : ℂ) * (r : ℂ)) -
            Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
              (polynomialPrimitive P)))
      (𝓝[>] 0) (𝓝 (conj rayConstant)) :=
    (Complex.continuous_conj.tendsto rayConstant).comp hlimit
  have hsecond : Tendsto
      (fun eps : ℝ ↦
        CompositionContinuation.continued
            (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
              (1 - (eps : ℂ) * (r : ℂ)) -
          Polynomial.aeval (-Complex.log ((eps : ℂ) * (r : ℂ)))
            (polynomialPrimitive P))
      (𝓝[>] 0) (𝓝 (conj rayConstant)) := hconjLimit.congr' hreal
  have hrayReal : conj rayConstant = rayConstant := tendsto_nhds_unique hsecond hlimit
  refine ⟨rayConstant.re, ?_⟩
  rw [Complex.conj_eq_iff_re.mp hrayReal]
  exact hlimit
private theorem leading_remainder_subarc_vanishes : ∀ (q : ℕ) (suffix : List ℕ+)
    (P : Polynomial ℝ) (ρ C : ℝ) (M : ℕ),
    0 < ρ → 0 ≤ C →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) →
    ∀ (r a b : ℝ), 0 < r → r < ρ →
      -Real.pi < a → b < Real.pi → a ≤ b →
      Tendsto
        (fun eps : ℝ ↦ ∫ θ in a..b, I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((θ : ℂ) * I))) P))
        (𝓝[>] 0) (𝓝 0) := by
  intro q suffix P ρ C M hρ hC hbound r a b hr hrρ ha hb hab
  let E : ℂ → ℂ := fun w ↦
    CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
      Polynomial.aeval (-Complex.log w) P
  have circle_mem_slit : ∀ (eps θ : ℝ),
      0 < eps → -Real.pi < θ → θ < Real.pi →
        (eps : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
    intro eps θ heps hθneg hθpos
    have hexp : Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
      rw [Complex.exp_mem_slitPlane]
      have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ := by
        apply (toIocMod_eq_self (hp := Real.two_pi_pos) (a := -Real.pi) (b := θ)).2
        exact ⟨hθneg, by linarith [Real.pi_pos]⟩
      simpa [hmod] using ne_of_lt hθpos
    rw [Complex.mem_slitPlane_iff] at hexp ⊢
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact hexp.imp (fun h ↦ mul_pos heps h) (mul_ne_zero (ne_of_gt heps))
  have hdecay := inner_arc_decay (Real.pi + |Real.log r|) 1 M
    (by positivity) (by omega)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun eps : ℝ ↦ (C * r * |b - a|) *
        (eps ^ 1 * (1 + (Real.pi + |Real.log r|) + |Real.log eps|) ^ M))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hdecay.const_mul (C * r * |b - a|)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with eps heps
    have hprod : 0 < eps * r := mul_pos heps.1 hr
    have hprodρ : eps * r < ρ :=
      (mul_lt_of_lt_one_left hr heps.2).trans hrρ
    have hpoint : ∀ θ ∈ Set.uIcc a b,
        ‖E (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ≤
          C * (eps * r) *
            (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ M := by
      intro θ hθ
      rw [Set.uIcc_of_le hab] at hθ
      have hθneg : -Real.pi < θ := ha.trans_le hθ.1
      have hθpos : θ < Real.pi := hθ.2.trans_lt hb
      have hwslit := circle_mem_slit (eps * r) θ hprod hθneg hθpos
      have hwnorm :
          ‖(((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ = eps * r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hprod,
          Complex.norm_exp]
        simp
      have hw0 : 0 <
          ‖(((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ := by
        rw [hwnorm]
        exact hprod
      have hwρ :
          ‖(((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ < ρ := by
        rw [hwnorm]
        exact hprodρ
      have hlogexp :
          Complex.log (Complex.exp ((θ : ℂ) * I)) = (θ : ℂ) * I := by
        apply Complex.log_exp
        · simpa using hθneg
        · simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul,
            add_zero]
          exact hθpos.le
      have hlog :
          Complex.log (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) =
            (Real.log (eps * r) : ℂ) + (θ : ℂ) * I := by
        rw [Complex.log_ofReal_mul hprod (Complex.exp_ne_zero _), hlogexp]
      have hθabs : |θ| ≤ Real.pi :=
        abs_le.mpr ⟨hθneg.le, hθpos.le⟩
      have hlognorm :
          ‖-Complex.log (((eps * r : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ) * I))‖ ≤
              |Real.log eps| + |Real.log r| + Real.pi := by
        rw [hlog, norm_neg]
        calc
          ‖(Real.log (eps * r) : ℂ) + (θ : ℂ) * I‖ ≤
              ‖(Real.log (eps * r) : ℂ)‖ + ‖(θ : ℂ) * I‖ := norm_add_le _ _
          _ = |Real.log (eps * r)| + |θ| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, norm_I, mul_one]
          _ ≤ (|Real.log eps| + |Real.log r|) + Real.pi := by
            gcongr
            rw [Real.log_mul heps.1.ne' hr.ne']
            exact abs_add_le _ _
      have hraw := hbound
        (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))
        hwslit hw0 hwρ
      dsimp [E]
      calc
        ‖CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((θ : ℂ) * I))) P‖ ≤
            C * ‖(((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))‖ *
              (1 + ‖-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((θ : ℂ) * I))‖) ^ M := hraw
        _ ≤ C * (eps * r) *
              (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ M := by
          rw [hwnorm]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hprod.le)
          apply pow_le_pow_left₀ (by positivity) _ M
          linarith [hlognorm]
    calc
      ‖∫ θ in a..b, I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((θ : ℂ) * I))) P)‖ ≤
          (C * (eps * r) *
            (1 + Real.pi + |Real.log r| + |Real.log eps|) ^ M) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro θ hθ
        rw [norm_mul, norm_I, one_mul]
        exact hpoint θ (uIoc_subset_uIcc hθ)
      _ = (C * r * |b - a|) *
          (eps ^ 1 * (1 + (Real.pi + |Real.log r|) + |Real.log eps|) ^ M) := by
        ring
private theorem leading_remainder_common_ray_limit : ∀ (q : ℕ) (suffix : List ℕ+)
    (P : Polynomial ℝ) (ρ C : ℝ) (M : ℕ),
    0 < ρ → 0 ≤ C →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) →
    ∀ r : ℝ, 0 < r → r < ρ →
      ∃ rayConstant : ℝ, ∀ θ : ℝ, -Real.pi < θ → θ < Real.pi →
        Tendsto
          (fun eps : ℝ ↦
            CompositionContinuation.continued
                (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
                  (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) -
              Polynomial.aeval
                (-Complex.log (((eps * r : ℝ) : ℂ) *
                  Complex.exp ((θ : ℂ) * I))) (polynomialPrimitive P))
          (𝓝[>] 0) (𝓝 (rayConstant : ℂ)) := by
  intro q suffix P ρ C M hρ hC hbound r hr hrρ
  obtain ⟨rayConstant, hpositive⟩ :=
    leading_remainder_positive_ray_limit_real q suffix P ρ C M hρ hC hbound r hr hrρ
  let F : ℝ → ℝ → ℂ := fun eps θ ↦
    CompositionContinuation.continued
        (List.replicate (q + 1) (1 : ℕ+) ++ suffix)
          (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) -
      Polynomial.aeval
        (-Complex.log (((eps * r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)))
          (polynomialPrimitive P)
  let E : ℂ → ℂ := fun u ↦ CompositionContinuation.continued
      (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) -
    Polynomial.aeval (-Complex.log u) P
  let G : ℂ → ℂ := fun u ↦ CompositionContinuation.continued
      (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - u) -
    Polynomial.aeval (-Complex.log u) (polynomialPrimitive P)
  have circle_mem_slit : ∀ (eps θ : ℝ),
      0 < eps → -Real.pi < θ → θ < Real.pi →
        (eps : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
    intro eps θ heps hθneg hθpos
    have hexp : Complex.exp ((θ : ℂ) * I) ∈ Complex.slitPlane := by
      rw [Complex.exp_mem_slitPlane]
      have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ := by
        apply (toIocMod_eq_self (hp := Real.two_pi_pos) (a := -Real.pi) (b := θ)).2
        exact ⟨hθneg, by linarith [Real.pi_pos]⟩
      simpa [hmod] using ne_of_lt hθpos
    rw [Complex.mem_slitPlane_iff] at hexp ⊢
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact hexp.imp (fun h ↦ mul_pos heps h) (mul_ne_zero (ne_of_gt heps))
  have quotient_continuous : ContinuousOn (fun u : ℂ ↦ -(E u) / u)
      Complex.slitPlane := by
    intro u hu
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    have hcontinued : ContinuousAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - v)) u :=
      ContinuousAt.comp (((CompositionSlit.result).2.1 _).1 (1 - u) hω).continuousAt
        (by fun_prop)
    have hlog := (Complex.hasDerivAt_log hu).neg
    have hpoly : ContinuousAt
        (fun v : ℂ ↦ Polynomial.aeval ((-Complex.log) v) P) u :=
      ((P.hasDerivAt_aeval ((-Complex.log) u)).comp u hlog).continuousAt
    exact ((hcontinued.sub hpoly).neg.div continuousAt_id hu0).continuousWithinAt
  have remainder_deriv : ∀ u : ℂ, u ∈ Complex.slitPlane →
      HasDerivAt G (-(E u) / u) u := by
    intro u hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    obtain ⟨_, _, _, leading_deriv, _⟩ := CompositionSlit.result
    have hz := leading_deriv (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) hω
    have hinner : HasDerivAt (fun v : ℂ ↦ 1 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℂ)
    have hactual : HasDerivAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix)) (1 - v))
        (-CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u) u := by
      simpa [Function.comp_def, mul_neg, neg_div] using hz.comp u hinner
    have hprimitiveDerivative : (polynomialPrimitive P).derivative = P := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_derivative]
      simp [polynomialPrimitive, Polynomial.sum_def]
      by_cases hcoeff : P.coeff n = 0 <;> simp [hcoeff] <;> field_simp
    have hpoly := (polynomialPrimitive P).hasDerivAt_aeval (-Complex.log u)
    have hcomp := hpoly.comp u (Complex.hasDerivAt_log hu).neg
    rw [hprimitiveDerivative] at hcomp
    have hpolyScalar : Polynomial.aeval (-Complex.log u) P * (-u⁻¹) =
        -(Polynomial.aeval (-Complex.log u) P) / u := by
      rw [div_eq_mul_inv]
      ring
    rw [hpolyScalar] at hcomp
    have hsub := hactual.sub hcomp
    have hscalar :
        -CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u -
          (-(Polynomial.aeval (-Complex.log u) P) / u) = -(E u) / u := by
      dsimp only [E]
      ring
    rw [hscalar] at hsub
    change HasDerivAt G (-(E u) / u) u at hsub
    simpa only [G, List.replicate_succ, List.cons_append] using hsub
  have angular_ftc : ∀ (eps a b : ℝ),
      0 < eps → -Real.pi < a → b < Real.pi → a ≤ b →
        (∫ θ in a..b, I * E ((eps : ℂ) * Complex.exp ((θ : ℂ) * I))) =
          G ((eps : ℂ) * Complex.exp ((a : ℂ) * I)) -
            G ((eps : ℂ) * Complex.exp ((b : ℂ) * I)) := by
    intro eps a b heps ha hb hab
    let circle : ℝ → ℂ := fun θ ↦ (eps : ℂ) * Complex.exp ((θ : ℂ) * I)
    have hcircle : ∀ θ ∈ Set.Icc a b, circle θ ∈ Complex.slitPlane := by
      intro θ hθ
      exact circle_mem_slit eps θ heps (ha.trans_le hθ.1) (hθ.2.trans_lt hb)
    have hderiv : ∀ θ ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ ↦ -G (circle x)) (I * E (circle θ)) θ := by
      intro θ hθ
      rw [Set.uIcc_of_le hab] at hθ
      have hslit := hcircle θ hθ
      have hcomplexCircle : HasDerivAt
          (fun x : ℂ ↦ (eps : ℂ) * Complex.exp (x * I))
          (circle θ * I) (θ : ℂ) := by
        simpa [circle, mul_assoc] using
          (((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.const_mul (eps : ℂ))
      have hneg := ((remainder_deriv (circle θ) hslit).comp
        (θ : ℂ) hcomplexCircle).comp_ofReal.neg
      have hne : circle θ ≠ 0 := Complex.slitPlane_ne_zero hslit
      have hscalar : -(-(E (circle θ)) / circle θ * (circle θ * I)) =
          I * E (circle θ) := by field_simp [hne]
      rw [hscalar] at hneg
      exact hneg
    have hEcont : ContinuousOn E Complex.slitPlane := by
      have hrecover := (quotient_continuous.mul continuousOn_id).neg
      apply hrecover.congr
      intro u hu
      have hne : u ≠ 0 := Complex.slitPlane_ne_zero hu
      change E u = -((-E u / u) * u)
      field_simp
    have hint : IntervalIntegrable (fun θ : ℝ ↦ I * E (circle θ))
        MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.mul
      apply hEcont.comp (by fun_prop)
      intro θ hθ
      exact hcircle θ (by simpa [Set.uIcc_of_le hab] using hθ)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    change (∫ θ in a..b, I * E (circle θ)) = G (circle a) - G (circle b)
    calc
      _ = -G (circle b) - -G (circle a) := hftc
      _ = G (circle a) - G (circle b) := by ring
  have hpositive' : Tendsto (fun eps : ℝ ↦ F eps 0)
      (𝓝[>] 0) (𝓝 (rayConstant : ℂ)) := by
    simpa [F, Complex.exp_zero] using hpositive
  refine ⟨rayConstant, ?_⟩
  intro θ hθneg hθpos
  by_cases hθ : 0 ≤ θ
  · have hvanish := leading_remainder_subarc_vanishes q suffix P ρ C M
      hρ hC hbound r 0 θ hr hrρ (by linarith [Real.pi_pos]) hθpos hθ
    have hcombined : Tendsto
        (fun eps : ℝ ↦ F eps 0 - ∫ x in (0 : ℝ)..θ, I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P))
        (𝓝[>] 0) (𝓝 ((rayConstant : ℂ) - 0)) := hpositive'.sub hvanish
    have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
        F eps θ = F eps 0 - ∫ x in (0 : ℝ)..θ, I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P) := by
      filter_upwards [eventually_mem_nhdsWithin] with eps heps
      have hprod : 0 < eps * r := mul_pos heps hr
      have hftc := angular_ftc (eps * r) 0 θ hprod
        (by linarith [Real.pi_pos]) hθpos hθ
      change (∫ x in (0 : ℝ)..θ, I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P)) = F eps 0 - F eps θ at hftc
      rw [hftc]
      ring
    simpa [F, Complex.ofReal_mul] using
      hcombined.congr' (Filter.EventuallyEq.symm hformula)
  · have hθle : θ ≤ 0 := le_of_not_ge hθ
    have hvanish := leading_remainder_subarc_vanishes q suffix P ρ C M
      hρ hC hbound r θ 0 hr hrρ hθneg (by linarith [Real.pi_pos]) hθle
    have hcombined : Tendsto
        (fun eps : ℝ ↦ (∫ x in θ..(0 : ℝ), I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P)) + F eps 0)
        (𝓝[>] 0) (𝓝 (0 + (rayConstant : ℂ))) := hvanish.add hpositive'
    have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
        F eps θ = (∫ x in θ..(0 : ℝ), I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P)) + F eps 0 := by
      filter_upwards [eventually_mem_nhdsWithin] with eps heps
      have hprod : 0 < eps * r := mul_pos heps hr
      have hftc := angular_ftc (eps * r) θ 0 hprod hθneg
        (by linarith [Real.pi_pos]) hθle
      change (∫ x in θ..(0 : ℝ), I *
          (CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix)
                (1 - ((eps * r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * I)) -
            Polynomial.aeval
              (-Complex.log (((eps * r : ℝ) : ℂ) *
                Complex.exp ((x : ℂ) * I))) P)) = F eps θ - F eps 0 at hftc
      rw [hftc]
      ring
    simpa [F, Complex.ofReal_mul] using
      hcombined.congr' (Filter.EventuallyEq.symm hformula)
private theorem split_leading_ones : ∀ ks : List ℕ+,
    ∃ q suffix, ks = List.replicate q (1 : ℕ+) ++ suffix ∧
      (suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ 1 < (first : ℕ)) := by
  intro ks
  induction ks with
  | nil => exact ⟨0, [], by simp⟩
  | cons first rest ih =>
    by_cases hfirst : (first : ℕ) = 1
    · have hfirst' : first = (1 : ℕ+) := Subtype.ext hfirst
      rcases ih with ⟨q, suffix, hrest, hsuffix⟩
      refine ⟨q + 1, suffix, ?_, hsuffix⟩
      simp [List.replicate_succ, hfirst', hrest]
    · refine ⟨0, first :: rest, by simp, Or.inr ⟨first, rest, rfl, ?_⟩⟩
      have hpositive := first.pos
      omega
private theorem leading_remainder_integral_identity : ∀ (q : ℕ) (suffix : List ℕ+)
    (P : Polynomial ℝ) (ρ C : ℝ) (M : ℕ),
    0 < ρ → 0 ≤ C →
    (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) →
    ∃ rayConstant : ℝ, ∀ w : ℂ, w ∈ Complex.slitPlane →
      0 < ‖w‖ → ‖w‖ < ρ →
        (CompositionContinuation.continued
              (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - w) -
            Polynomial.aeval (-Complex.log w) (polynomialPrimitive P)) - rayConstant =
          ∫ t in (0 : ℝ)..1, w *
            (-(CompositionContinuation.continued
                  (List.replicate q (1 : ℕ+) ++ suffix) (1 - (t : ℂ) * w) -
                Polynomial.aeval (-Complex.log ((t : ℂ) * w)) P) /
              ((t : ℂ) * w)) := by
  intro q suffix P ρ C M hρ hC hbound
  let r : ℝ := ρ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrρ : r < ρ := by dsimp [r]; linarith
  obtain ⟨rayConstant, hcommon⟩ :=
    leading_remainder_common_ray_limit q suffix P ρ C M hρ hC hbound r hr hrρ
  refine ⟨rayConstant, ?_⟩
  intro w hw hw0 hwρ
  let E : ℂ → ℂ := fun u ↦
    CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) -
      Polynomial.aeval (-Complex.log u) P
  let F : ℂ → ℂ := fun u ↦
    CompositionContinuation.continued
        (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - u) -
      Polynomial.aeval (-Complex.log u) (polynomialPrimitive P)
  let integrand : ℝ → ℂ := fun t ↦ w * (-(E ((t : ℂ) * w)) / ((t : ℂ) * w))
  have radial_mem_slit : ∀ (u : ℂ) (t : ℝ),
      u ∈ Complex.slitPlane → 0 < t → (t : ℂ) * u ∈ Complex.slitPlane := by
    intro u t hu ht
    rw [Complex.mem_slitPlane_iff] at hu ⊢
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact hu.imp (fun h ↦ mul_pos ht h) (mul_ne_zero (ne_of_gt ht))
  have quotient_continuous : ContinuousOn (fun u : ℂ ↦ -(E u) / u)
      Complex.slitPlane := by
    intro u hu
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    have hcontinued : ContinuousAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - v)) u :=
      ContinuousAt.comp (((CompositionSlit.result).2.1 _).1 (1 - u) hω).continuousAt
        (by fun_prop)
    have hlog := (Complex.hasDerivAt_log hu).neg
    have hpoly : ContinuousAt
        (fun v : ℂ ↦ Polynomial.aeval ((-Complex.log) v) P) u :=
      ((P.hasDerivAt_aeval ((-Complex.log) u)).comp u hlog).continuousAt
    exact ((hcontinued.sub hpoly).neg.div continuousAt_id hu0).continuousWithinAt
  have remainder_deriv : ∀ u : ℂ, u ∈ Complex.slitPlane →
      HasDerivAt F (-(E u) / u) u := by
    intro u hu
    have hω : 1 - u ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega] using hu
    obtain ⟨_, _, _, leading_deriv, _⟩ := CompositionSlit.result
    have hz := leading_deriv (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) hω
    have hinner : HasDerivAt (fun v : ℂ ↦ 1 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℂ)
    have hactual : HasDerivAt
        (fun v : ℂ ↦ CompositionContinuation.continued
          ((1 : ℕ+) :: (List.replicate q (1 : ℕ+) ++ suffix)) (1 - v))
        (-CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u) u := by
      simpa [Function.comp_def, mul_neg, neg_div] using hz.comp u hinner
    have hprimitiveDerivative : (polynomialPrimitive P).derivative = P := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_derivative]
      simp [polynomialPrimitive, Polynomial.sum_def]
      by_cases hcoeff : P.coeff n = 0 <;> simp [hcoeff] <;> field_simp
    have hpoly := (polynomialPrimitive P).hasDerivAt_aeval (-Complex.log u)
    have hcomp := hpoly.comp u (Complex.hasDerivAt_log hu).neg
    rw [hprimitiveDerivative] at hcomp
    have hpolyScalar : Polynomial.aeval (-Complex.log u) P * (-u⁻¹) =
        -(Polynomial.aeval (-Complex.log u) P) / u := by
      rw [div_eq_mul_inv]
      ring
    rw [hpolyScalar] at hcomp
    have hsub := hactual.sub hcomp
    have hscalar :
        -CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) / u -
          (-(Polynomial.aeval (-Complex.log u) P) / u) = -(E u) / u := by
      dsimp only [E]
      ring
    rw [hscalar] at hsub
    change HasDerivAt F (-(E u) / u) u at hsub
    simpa only [F, List.replicate_succ, List.cons_append] using hsub
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw0)
  have hargneg : -Real.pi < Complex.arg w := Complex.neg_pi_lt_arg w
  have hargpos : Complex.arg w < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases (Complex.mem_slitPlane_iff.mp hw) with hre | him
    · exact Or.inl hre.le
    · exact Or.inr him
  have hscale : Tendsto (fun eps : ℝ ↦ (‖w‖ / r) * eps)
      (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_iff_comap]
    rw [comap_mulLeft_nhdsGT_zero (div_pos hw0 hr)]
  have hFlimit : Tendsto (fun eps : ℝ ↦ F ((eps : ℂ) * w))
      (𝓝[>] 0) (𝓝 (rayConstant : ℂ)) := by
    have h := (hcommon (Complex.arg w) hargneg hargpos).comp hscale
    apply h.congr'
    filter_upwards with eps
    have hpoint :
        (((((‖w‖ / r) * eps) * r : ℝ) : ℂ) *
            Complex.exp ((Complex.arg w : ℂ) * I)) = (eps : ℂ) * w := by
      calc
        (((((‖w‖ / r) * eps) * r : ℝ) : ℂ) *
            Complex.exp ((Complex.arg w : ℂ) * I)) =
            (eps : ℂ) * ((‖w‖ : ℂ) *
              Complex.exp ((Complex.arg w : ℂ) * I)) := by
          push_cast
          field_simp [ne_of_gt hr]
        _ = (eps : ℂ) * w := by rw [Complex.norm_mul_exp_arg_mul_I]
    change F (((((‖w‖ / r) * eps) * r : ℝ) : ℂ) *
      Complex.exp ((Complex.arg w : ℂ) * I)) = F ((eps : ℂ) * w)
    exact congrArg F hpoint
  let Ecut : ℂ → ℂ := fun u ↦
    if u ∈ Complex.slitPlane ∧ ‖u‖ < ρ then -E u else 0
  have hEcut : ∀ u : ℂ, u ≠ 0 →
      ‖Ecut u‖ ≤ C * ‖u‖ ^ 1 * (1 + ‖-Complex.log u‖) ^ M := by
    intro u hu
    by_cases hcut : u ∈ Complex.slitPlane ∧ ‖u‖ < ρ
    · rw [show Ecut u = -E u by simp [Ecut, hcut], norm_neg, pow_one]
      exact hbound u hcut.1 (norm_pos_iff.mpr hu) hcut.2
    · rw [show Ecut u = 0 by simp [Ecut, hcut], norm_zero, pow_one]
      exact mul_nonneg (mul_nonneg hC (norm_nonneg u)) (pow_nonneg (by positivity) M)
  have hline : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Ecut ((t : ℂ) * w) = -E ((t : ℂ) * w) := by
    intro t ht
    apply if_pos
    refine ⟨radial_mem_slit w t hw ht.1, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hwρ
  have hmajor : IntervalIntegrable
      (fun t : ℝ ↦ C * ‖w‖ * t ^ (1 - 1) *
        (1 + ‖-Complex.log w‖ + (-Real.log t)) ^ M)
      MeasureTheory.volume 0 1 := by
    have hbase := radial_majorant_integrable ‖-Complex.log w‖ 1 M
      (norm_nonneg _) (by omega)
    have hscaled := hbase.const_mul (C * ‖w‖)
    simpa [mul_assoc] using hscaled
  have hint : IntervalIntegrable integrand MeasureTheory.volume 0 1 := by
    apply hmajor.mono_fun'
    · have hcont : ContinuousOn integrand (Set.Ioc (0 : ℝ) 1) := by
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.comp quotient_continuous (by fun_prop)
        intro t ht
        exact radial_mem_slit w t hw ht.1
      simpa [Set.uIoc_of_le zero_le_one] using
        hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      simpa [integrand, hline t ht'] using
        radial_div_bound Ecut C 1 M hC (by omega) w hwne hEcut t ht'
  have hprimitive : ContinuousOn
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (Set.uIcc (0 : ℝ) 1) := by
    apply intervalIntegral.continuousOn_primitive_interval_left
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint
  have huIcc : Set.uIcc (0 : ℝ) 1 ∈ 𝓝[>] 0 := by
    apply mem_of_superset (Ioo_mem_nhdsGT zero_lt_one)
    intro eps heps
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨heps.1.le, heps.2.le⟩
  have hintegralLimit : Tendsto
      (fun eps : ℝ ↦ ∫ t in eps..1, integrand t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, integrand t)) :=
    (hprimitive 0 Set.left_mem_uIcc).mono_of_mem_nhdsWithin huIcc
  have hformula : ∀ᶠ eps : ℝ in 𝓝[>] 0,
      (∫ t in eps..1, integrand t) = F w - F ((eps : ℂ) * w) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with eps heps
    have hderiv : ∀ t ∈ Set.uIcc eps 1,
        HasDerivAt (fun x : ℝ ↦ F ((x : ℂ) * w))
          (w * (-(E ((t : ℂ) * w)) / ((t : ℂ) * w))) t := by
      intro t ht
      rw [Set.uIcc_of_le heps.2.le] at ht
      have htw := radial_mem_slit w t hw (heps.1.trans_le ht.1)
      have hline : HasDerivAt (fun u : ℂ ↦ u * w) w (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const w
      simpa only [Function.comp_def, mul_comm] using
        ((remainder_deriv ((t : ℂ) * w) htw).comp (t : ℂ) hline).comp_ofReal
    have hint_eps : IntervalIntegrable integrand MeasureTheory.volume eps 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.comp quotient_continuous (by fun_prop)
      intro t ht
      rw [Set.uIcc_of_le heps.2.le] at ht
      exact radial_mem_slit w t hw (heps.1.trans_le ht.1)
    simpa [integrand] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_eps
  have hright : Tendsto (fun eps : ℝ ↦ F w - F ((eps : ℂ) * w))
      (𝓝[>] 0) (𝓝 (F w - (rayConstant : ℂ))) := tendsto_const_nhds.sub hFlimit
  have heq : (∫ t in (0 : ℝ)..1, integrand t) = F w - (rayConstant : ℂ) :=
    tendsto_nhds_unique hintegralLimit
      (hright.congr' (Filter.EventuallyEq.symm hformula))
  simpa [F, E, integrand] using heq.symm

end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
