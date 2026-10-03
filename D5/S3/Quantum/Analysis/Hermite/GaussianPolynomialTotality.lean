/- GID: D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian-polynomial tests detect complex Lebesgue L2 vectors at any positive width. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license; full license: docs/reports/hermite-suppliers/tauceti-LICENSE.txt.
Authors: The Tau Ceti contributors; Rémy Degenne (complex-MGF strip argument).
Adapted from TauCetiProject/TauCeti at f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd:
Probability/Moments/Determinacy.lean and VanishingMoments.lean,
Probability/Distributions/Gaussian/PolynomialMemLp.lean.
Changes: retain one actual Gaussian-polynomial totality theorem; all intermediate
measure-determinacy, truncation, integrability and normalization proofs are local.
No originality is claimed for the attributed analytic or density constructions.
Retirement: at this repository's future pinned Mathlib revision, replace this port
by an exact direct application proving this full statement at every positive width,
after the actual Hermite and physical-graph consumers pass with the port removed.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Polynomial

open MeasureTheory ProbabilityTheory Complex Filter Polynomial
open scoped Topology ENNReal NNReal

namespace D5.S3.Quantum.Analysis.Hermite.GaussianPolynomialTotality

/-- The Gaussian-polynomial test functions are total in the actual complex Lebesgue L2 space.
No decay or totality assumption on the tested vector is made. -/
theorem gaussian_polynomial_totality (b : ℝ) (hb : 0 < b) (g : ℝ → ℂ)
    (hg : MemLp g 2 (volume : Measure ℝ))
    (horth : ∀ q : Polynomial ℝ,
      ∫ x : ℝ, ((q.eval x : ℝ) : ℂ) * (Real.exp (-(b * x ^ 2) / 2) : ℂ) * g x = 0) :
    (∀ q : Polynomial ℝ, Integrable (fun x : ℝ =>
      ((q.eval x : ℝ) : ℂ) * (Real.exp (-(b * x ^ 2) / 2) : ℂ) * g x) volume) ∧
      g =ᵐ[volume] 0 := by
  have iteratedDeriv_complexMGF_id_zero {μ : Measure ℝ}
      (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ)) (n : ℕ) :
      iteratedDeriv n (complexMGF id μ) 0 = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
    have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by simpa using hμ
    rw [iteratedDeriv_complexMGF (z := 0) hz n]
    have hpow : ∀ x : ℝ, ((x : ℂ)) ^ n * Complex.exp (0 * (x : ℂ)) = (((x ^ n : ℝ)) : ℂ) := by
      intro x
      rw [zero_mul, Complex.exp_zero, mul_one]
      push_cast
      ring
    simp only [id_eq, hpow]
    exact integral_ofReal

  have complexMGF_eventuallyEq_of_forall_integral_pow_eq {μ ν : Measure ℝ}
      (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
      (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
      (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
      complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν := by
    have hAμ : AnalyticAt ℂ (complexMGF id μ) 0 := analyticAt_complexMGF (by simpa using hμ)
    have hAν : AnalyticAt ℂ (complexMGF id ν) 0 := analyticAt_complexMGF (by simpa using hν)
    -- the difference has every iterated derivative zero at `0`, so it vanishes near `0`
    have hiter : ∀ i, iteratedDeriv i (fun z => complexMGF id μ z - complexMGF id ν z) 0 = 0 := by
      intro i
      rw [iteratedDeriv_fun_sub hAμ.contDiffAt hAν.contDiffAt,
        iteratedDeriv_complexMGF_id_zero hμ i, iteratedDeriv_complexMGF_id_zero hν i, hmom i,
        sub_self]
    have hsub : AnalyticAt ℂ (fun z => complexMGF id μ z - complexMGF id ν z) 0 := hAμ.sub hAν
    have hord : analyticOrderAt (fun z => complexMGF id μ z - complexMGF id ν z) 0 = ⊤ :=
      ENat.eq_top_iff_forall_ge.mpr fun m =>
        (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub).mpr fun i _ => hiter i
    filter_upwards [analyticOrderAt_eq_top.mp hord] with z hz using sub_eq_zero.mp hz

  have charFun_eq_of_frequently_complexMGF_eq {μ ν : Measure ℝ}
      (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
      (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
      (heq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ z = complexMGF id ν z) :
      charFun μ = charFun ν := by
    set U : Set ℂ :=
      Complex.reLm ⁻¹' (interior (integrableExpSet id μ) ∩ interior (integrableExpSet id ν))
      with hUdef
    have hUconn : IsPreconnected U :=
      ((convex_integrableExpSet.interior.inter
        convex_integrableExpSet.interior).linear_preimage Complex.reLm).isPreconnected
    have hAμU : AnalyticOnNhd ℂ (complexMGF id μ) U :=
      analyticOnNhd_complexMGF.mono fun _ hz => hz.1
    have hAνU : AnalyticOnNhd ℂ (complexMGF id ν) U :=
      analyticOnNhd_complexMGF.mono fun _ hz => hz.2
    -- The imaginary axis lies in the strip, and there the values are the characteristic functions.
    have hmemU : ∀ z : ℂ, z.re = 0 → z ∈ U := by
      intro z hz
      have hz' : reLm z = 0 := by rw [Complex.reLm_coe]; exact hz
      simp only [hUdef, Set.mem_preimage, Set.mem_inter_iff, hz']
      exact ⟨hμ, hν⟩
    have hEqU : Set.EqOn (complexMGF id μ) (complexMGF id ν) U :=
      hAμU.eqOn_of_preconnected_of_frequently_eq hAνU hUconn (hmemU 0 (by simp)) heq
    ext t
    have h := hEqU (hmemU ((t : ℂ) * I) (by simp))
    rwa [complexMGF_id_mul_I, complexMGF_id_mul_I] at h

  have zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp {μ : Measure ℝ}
      (h : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ) :
      (0 : ℝ) ∈ interior (integrableExpSet id μ) := by
    obtain ⟨a, ha, hint⟩ := h
    refine mem_interior.mpr ⟨Set.Ioo (-a) a, ?_, isOpen_Ioo, Set.mem_Ioo.mpr ⟨neg_lt_zero.mpr ha, ha⟩⟩
    intro t ht
    simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
    refine hint.mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * x ≤ |t * x| := le_abs_self _
      _ = |t| * |x| := abs_mul t x
      _ ≤ a * |x| := mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (abs_nonneg x)

  have determine_measure {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (hμ : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) μ)
      (hν : ∃ a : ℝ, 0 < a ∧ Integrable (fun x => Real.exp (a * |x|)) ν)
      (hmom : ∀ n, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
    have hμ' := zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hμ
    have hν' := zero_mem_interior_integrableExpSet_id_of_exists_integrable_exp hν
    exact Measure.ext_of_charFun (charFun_eq_of_frequently_complexMGF_eq hμ' hν'
      ((complexMGF_eventuallyEq_of_forall_integral_pow_eq hμ' hν' hmom).filter_mono
        nhdsWithin_le_nhds).frequently)

  have integrable_of_integrable_exp_mul_abs_mul {ν : Measure ℝ} {a : ℝ} {g : ℝ → ℝ} (ha : 0 ≤ a)
      (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν) : Integrable g ν := by
    have hgm : AEStronglyMeasurable g ν := by
      have hrw : g = fun x => Real.exp (-(a * |x|)) * (Real.exp (a * |x|) * g x) := by
        funext x
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      rw [hrw]
      exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
        hexp.aestronglyMeasurable
    refine hexp.mono hgm ?_
    filter_upwards with x
    have h1 : (1 : ℝ) ≤ Real.exp (a * |x|) := Real.one_le_exp (mul_nonneg ha (abs_nonneg x))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [abs_nonneg (g x)]

  have integrable_toReal_ofReal_smul_pow {ν : Measure ℝ} {a : ℝ} {g f : ℝ → ℝ} (ha : 0 < a)
      (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
      (hfm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x)) ν)
      (hle : ∀ x, |max (f x) 0| ≤ |g x|) (n : ℕ) :
      Integrable (fun x : ℝ => (ENNReal.ofReal (f x)).toReal • x ^ n) ν := by
    have hc : (0 : ℝ) < ((n : ℝ) / a) ^ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact pow_pos (div_pos (Nat.cast_pos.mpr hn) ha) _
    have hdom : ∀ x : ℝ, |x| ^ n ≤ ((n : ℝ) / a) ^ n * Real.exp (a * |x|) := by
      intro x
      have h := rpow_abs_le_mul_exp_abs x (p := (n : ℝ)) (t := a) (Nat.cast_nonneg n) (ne_of_gt ha)
      rwa [abs_of_pos ha, Real.rpow_natCast, Real.rpow_natCast] at h
    refine (hexp.const_mul (((n : ℝ) / a) ^ n)).mono ?_ ?_
    · exact hfm.ennreal_toReal.aestronglyMeasurable.smul (continuous_pow n).aestronglyMeasurable
    · filter_upwards with x
      have hE : (0 : ℝ) < Real.exp (a * |x|) := Real.exp_pos _
      simp only [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos hE, abs_of_pos hc]
      nlinarith [hle x, hdom x, abs_nonneg (g x),
        abs_nonneg (max (f x) 0), pow_nonneg (abs_nonneg x) n, hE.le, hc.le]

  have integrable_exp_withDensity_ofReal {ν : Measure ℝ} {a : ℝ} {g f : ℝ → ℝ}
      (hexp : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
      (hfm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (f x)) ν)
      (hlt : ∀ᵐ x ∂ν, ENNReal.ofReal (f x) < ⊤) (hle : ∀ x, |max (f x) 0| ≤ |g x|) :
      Integrable (fun x : ℝ => Real.exp (a * |x|))
        (ν.withDensity fun x => ENNReal.ofReal (f x)) := by
    rw [integrable_withDensity_iff_integrable_smul₀' hfm hlt]
    refine hexp.mono ?_ ?_
    · exact hfm.ennreal_toReal.aestronglyMeasurable.smul (by fun_prop)
    · filter_upwards with x
      have hE : (0 : ℝ) < Real.exp (a * |x|) := Real.exp_pos _
      simp only [smul_eq_mul, ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_mul,
        abs_of_pos hE]
      nlinarith [hle x, abs_nonneg (g x), hE.le]

  have integral_pow_withDensity_ofReal_eq {ν : Measure ℝ} {g : ℝ → ℝ} {n : ℕ}
      (hmeasp : AEMeasurable (fun x : ℝ => ENNReal.ofReal (g x)) ν)
      (hmeasn : AEMeasurable (fun x : ℝ => ENNReal.ofReal (-g x)) ν)
      (hintp : Integrable (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n) ν)
      (hintn : Integrable (fun x : ℝ => (ENNReal.ofReal (-g x)).toReal • x ^ n) ν)
      (hmom : ∫ x : ℝ, x ^ n * g x ∂ν = 0) :
      ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (g x))
        = ∫ x, x ^ n ∂(ν.withDensity fun x => ENNReal.ofReal (-g x)) := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeasp (ae_of_all _ fun _ =>
        ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hmeasn (ae_of_all _ fun _ =>
        ENNReal.ofReal_lt_top)]
    have hsplit : (fun x : ℝ => (ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) = fun x : ℝ => x ^ n * g x := by
      funext x
      rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal',
        ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      ring
    have hz : ∫ x : ℝ, ((ENNReal.ofReal (g x)).toReal • x ^ n
        - (ENNReal.ofReal (-g x)).toReal • x ^ n) ∂ν = 0 := by
      rw [hsplit]; exact hmom
    rw [integral_sub hintp hintn] at hz
    linarith

  have withDensity_ofReal_eq_withDensity_ofReal_neg {ν : Measure ℝ} {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
      (hexpa : Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
      (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n * g x ∂ν = 0) :
      (ν.withDensity fun x => ENNReal.ofReal (g x))
        = ν.withDensity fun x => ENNReal.ofReal (-g x) := by
    have hg : Integrable g ν := integrable_of_integrable_exp_mul_abs_mul ha.le hexpa
    have hgm : AEMeasurable g ν := hg.aestronglyMeasurable.aemeasurable
    have hmeasp : AEMeasurable (fun x => ENNReal.ofReal (g x)) ν :=
      ENNReal.measurable_ofReal.comp_aemeasurable hgm
    have hmeasn : AEMeasurable (fun x => ENNReal.ofReal (-g x)) ν :=
      ENNReal.measurable_ofReal.comp_aemeasurable hgm.neg
    -- `ENNReal.ofReal` already truncates at zero, so these densities are exactly `g⁺` and `g⁻`.
    -- `|max t 0| ≤ |t|` is Mathlib's `abs_max_sub_max_le_abs` at `b = c = 0`.
    have hlep : ∀ x, |max (g x) 0| ≤ |g x| := fun x => by
      simpa using abs_max_sub_max_le_abs (g x) 0 0
    have hlen : ∀ x, |max (-g x) 0| ≤ |g x| := fun x => by
      simpa using abs_max_sub_max_le_abs (-g x) 0 0
    have : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (g x)) :=
      isFiniteMeasure_withDensity_ofReal hg.2
    have : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (-g x)) :=
      isFiniteMeasure_withDensity_ofReal hg.neg.2
    -- `g⁺ - g⁻ = g` pointwise, so the two moment sequences differ by `∫ xⁿ g = 0`.
    exact determine_measure
      ⟨a, ha, integrable_exp_withDensity_ofReal hexpa hmeasp
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) hlep⟩
      ⟨a, ha, integrable_exp_withDensity_ofReal hexpa hmeasn
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) hlen⟩
      fun n => integral_pow_withDensity_ofReal_eq hmeasp hmeasn
        (integrable_toReal_ofReal_smul_pow ha hexpa hmeasp hlep n)
        (integrable_toReal_ofReal_smul_pow ha hexpa hmeasn hlen n) (hmom n)

  have ae_eq_zero_of_forall_moment_eq_zero {ν : Measure ℝ} (g : ℝ → ℝ)
      (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|) * g x) ν)
      (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n * g x ∂ν = 0) :
      g =ᵐ[ν] 0 := by
    obtain ⟨a, ha, hexpa⟩ := hexp
    have hg : Integrable g ν := integrable_of_integrable_exp_mul_abs_mul ha.le hexpa
    -- `g` and `0` have the same vector measure, because the two parts of `g` cancel.
    refine hg.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _) ?_
    rw [withDensityᵥ_zero, withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hg,
      sub_eq_zero]
    congr 1
    exact withDensity_ofReal_eq_withDensity_ofReal_neg ha hexpa hmom

  have integrable_exp_mul_abs_gaussianWeight {b : ℝ} (hb : 0 < b) (a : ℝ) :
      Integrable (fun x : ℝ => Real.exp (a * |x|))
        (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-(b * x ^ 2)))) := by
    have hgauss :
        Integrable (fun x : ℝ => Real.exp (a ^ 2 / (2 * b)) * Real.exp (-(b / 2) * x ^ 2)) :=
      (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < b / 2)).const_mul _
    have hcore : Integrable (fun x : ℝ => Real.exp (a * |x|) * Real.exp (-(b * x ^ 2))) := by
      refine hgauss.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
      rw [← Real.exp_add, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      -- Cleared of the denominator `2b`, the bound is exactly `0 ≤ (a - b|x|)²`.
      have hsq : 0 ≤ a ^ 2 - 2 * (a * b) * |x| + b ^ 2 * x ^ 2 := by
        have h : (a - b * |x|) ^ 2 = a ^ 2 - 2 * (a * b) * |x| + b ^ 2 * x ^ 2 := by
          rw [← sq_abs x]; ring
        exact h ▸ sq_nonneg _
      have hkey : a * |x| - b / 2 * x ^ 2 ≤ a ^ 2 / (2 * b) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
        nlinarith [hsq]
      linarith
    rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hfun :
        (fun x : ℝ => (ENNReal.ofReal (Real.exp (-(b * x ^ 2)))).toReal • Real.exp (a * |x|))
          = fun x : ℝ => Real.exp (a * |x|) * Real.exp (-(b * x ^ 2)) := by
      funext x
      rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
    rw [hfun]
    exact hcore

  have hweight : MemLp (fun x : ℝ => Real.exp (|x| - b * x ^ 2 / 2)) 2
      (volume : Measure ℝ) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    have hi := integrable_exp_mul_abs_gaussianWeight hb 2
    rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
    refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [pow_two (Real.exp (|x| - b * x ^ 2 / 2))]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  let h : ℝ → ℂ := fun x => (Real.exp (-(b * x ^ 2) / 2) : ℂ) * g x
  have hexp : Integrable (fun x : ℝ => (Real.exp |x| : ℂ) * h x) volume := by
    have hi := hweight.ofReal.integrable_mul hg
    refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
    change (Real.exp (|x| - b * x ^ 2 / 2) : ℂ) * g x =
      (Real.exp |x| : ℂ) * ((Real.exp (-(b * x ^ 2) / 2) : ℂ) * g x)
    have he : Real.exp (|x| - b * x ^ 2 / 2) =
        Real.exp |x| * Real.exp (-(b * x ^ 2) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, Complex.ofReal_mul, mul_assoc]
  have hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * h x = 0 := by
    intro n
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_pow, mul_assoc, h]
      using horth (Polynomial.X ^ n)
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (x : ℂ) ^ n * h x) volume := by
    intro n
    have hm : AEStronglyMeasurable h volume :=
      (show AEStronglyMeasurable (fun x : ℝ => (Real.exp (-(b * x ^ 2) / 2) : ℂ)) volume
        from by fun_prop).mul hg.aestronglyMeasurable
    refine (hexp.const_mul ((n : ℝ) ^ n : ℂ)).mono
      ((show AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ n) volume
        from by fun_prop).mul hm) ?_
    filter_upwards with x
    have hd := rpow_abs_le_mul_exp_abs x (p := (n : ℝ)) (t := 1)
      (Nat.cast_nonneg n) (by norm_num : (1 : ℝ) ≠ 0)
    simp only [abs_one, div_one, Real.rpow_natCast, one_mul] at hd
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (norm_nonneg (h x))
  have transfer (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
      ∫ x : ℝ, x ^ n * L (h x) = 0 := by
    have hfun : (fun x : ℝ => x ^ n * L (h x)) =
        fun x : ℝ => L ((x : ℂ) ^ n * h x) := by
      funext x
      rw [← Complex.ofReal_pow, ← Complex.real_smul, L.map_smul, smul_eq_mul]
    rw [hfun, L.integral_comp_comm (hint n), hmom n, map_zero]
  have hreexp : Integrable (fun x : ℝ => Real.exp |x| * (h x).re) volume := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using (Complex.reCLM.integrable_comp hexp)
  have himexp : Integrable (fun x : ℝ => Real.exp |x| * (h x).im) volume := by
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using (Complex.imCLM.integrable_comp hexp)
  have hzre := ae_eq_zero_of_forall_moment_eq_zero (ν := volume)
    (fun x => (h x).re) ⟨1, one_pos, by simpa only [one_mul] using hreexp⟩
    (fun n => transfer Complex.reCLM n)
  have hzim := ae_eq_zero_of_forall_moment_eq_zero (ν := volume)
    (fun x => (h x).im) ⟨1, one_pos, by simpa only [one_mul] using himexp⟩
    (fun n => transfer Complex.imCLM n)
  refine ⟨?_, ?_⟩
  · intro q
    have hpoly : Integrable (fun x : ℝ => ((q.eval x : ℝ) : ℂ) * h x) volume := by
      simp_rw [Polynomial.eval_eq_sum_range, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul]
      exact integrable_finsetSum _ fun n _ => by
        simpa only [Complex.ofReal_pow, mul_assoc] using (hint n).const_mul (q.coeff n : ℂ)
    simpa only [h, mul_assoc] using hpoly
  · filter_upwards [hzre, hzim] with x hr hi
    have hz : h x = 0 := Complex.ext hr hi
    have hn : (Real.exp (-(b * x ^ 2) / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp hz).resolve_left hn

end D5.S3.Quantum.Analysis.Hermite.GaussianPolynomialTotality
