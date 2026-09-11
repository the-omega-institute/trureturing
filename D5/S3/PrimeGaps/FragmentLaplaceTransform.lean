/- GID: D5/S3/PrimeGaps/FragmentLaplaceTransform
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/FragmentLaplaceTransform
   mirror-E: none(waiver:analytic-source-port)
   anchors: []
   utility: none
   digest: Derive the Laplace functional and scalar mass transform of the actual dyadic Poisson fragment law. -/

/-
Adapted from openai/PrimeGaps186, commit
61340d0b74163003b32756bb16e91d9209a5e330, PrimeGaps186.lean.
Verified full source Git blob: a8d0b8a138c7309f85e3967b24c3b502be5a3917.
SPDX-License-Identifier: Apache-2.0
Upstream attribution notices and license are retained in
research/fragment_mesh/UPSTREAM_NOTICE.md. Modified 2026-09-08:
dependency-isolated port onto the repository's pinned Mathlib. The original
probability construction is imported, never copied or replaced. No upstream
main module, Challenge module or project input axiom is imported.
-/

import D5.S3.PrimeGaps.FragmentLaw
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Laplace transform of the actual fragment law

The four proofs adapt upstream declarations at original lines 3442-3611 and
3709-3795. Finite Poisson conditioning gives the band transform; independence
and dominated convergence over finite band sets give the full transform.
The zero fallback is removed using the existing almost-sure finiteness owner.

These are source-reviewed candidate ports, not an executed kernel receipt.
No density, perpetuity or Laplace identity is postulated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace PrimeGap186

theorem exp_neg_ennreal_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    EReal.exp (-((∑ i ∈ s, f i : ℝ≥0∞) : EReal)) =
      ∏ i ∈ s, EReal.exp (-((f i : ℝ≥0∞) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.coe_ennreal_add,
      EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
        (.inr (EReal.coe_ennreal_ne_bot _)),
      sub_eq_add_neg, EReal.exp_add, ih, Finset.prod_insert hi]

theorem lintegral_exp_neg_finitePoissonLaw
    (μ : FiniteMeasure ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ c, EReal.exp (-((∫⁻ u, h u ∂(c : Measure ℝ)) : EReal))
      ∂(finitePoissonLaw μ)) =
      EReal.exp (-((∫⁻ u,
        1 - EReal.exp (-((ENNReal.ofReal u * h u : ℝ≥0∞) : EReal))
        ∂(μ : Measure ℝ)) : EReal)) := by
  let g : ℝ → ℝ≥0∞ := fun u =>
    EReal.exp (-((ENNReal.ofReal u * h u : ℝ≥0∞) : EReal))
  have hg : Measurable g :=
    (measurable_id.ennreal_ofReal.mul hh).coe_ereal_ennreal.neg.ereal_exp
  have hg_one (u : ℝ) : g u ≤ 1 :=
    EReal.exp_le_one_iff.2
      (EReal.neg_le_zero.2 (EReal.coe_ennreal_nonneg _))
  let q : ℝ≥0∞ := ∫⁻ u, g u ∂(μ.normalize : Measure ℝ)
  have hq_one : q ≤ 1 :=
    lintegral_le_const (Filter.Eventually.of_forall hg_one)
  have hq : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_one
  have hF : Measurable (fun c : FiniteMeasure ℝ =>
      EReal.exp (-((∫⁻ u, h u ∂(c : Measure ℝ)) : EReal))) :=
    ((Measure.measurable_lintegral hh).comp
      measurable_subtype_coe).coe_ereal_ennreal.neg.ereal_exp
  have hpoint (n : ℕ) (x : Fin n → ℝ) :
      EReal.exp (-((∫⁻ u, h u ∂(weightedEmpirical n x : Measure ℝ)) : EReal)) =
        ∏ i : Fin n, g (x i) := by
    simp_rw [coe_weightedEmpirical, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul]
    exact exp_neg_ennreal_sum Finset.univ _
  have htuple (n : ℕ) :
      (∫⁻ x : Fin n → ℝ,
        EReal.exp (-((∫⁻ u, h u ∂(weightedEmpirical n x : Measure ℝ)) : EReal))
        ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ)))) = q ^ n := by
    simp_rw [hpoint]
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun
      Finset.univ (fun i (x : Fin n → ℝ) => g (x i))
      (ProbabilityTheory.iIndepFun_pi (fun _ => hg.aemeasurable))
      (fun i => hg.comp (measurable_pi_apply i))]
    simpa using Finset.prod_eq_pow_card (s := Finset.univ) (fun i _ =>
      (measurePreserving_eval
        (fun _ : Fin n => (μ.normalize : Measure ℝ)) i).lintegral_comp hg)
  have hseries :
      HasSum (fun n : ℕ =>
        Real.exp (-(μ.mass : ℝ)) * ((μ.mass : ℝ) * q.toReal) ^ n / n.factorial)
        (Real.exp (-(μ.mass : ℝ)) * Real.exp ((μ.mass : ℝ) * q.toReal)) := by
    simpa only [← Real.exp_eq_exp_ℝ, mul_div_assoc] using
      (NormedSpace.expSeries_div_hasSum_exp
        ((μ.mass : ℝ) * q.toReal)).mul_left (Real.exp (-(μ.mass : ℝ)))
  have hpoisson :
      (∫⁻ n : ℕ, q ^ n ∂(ProbabilityTheory.poissonMeasure μ.mass)) =
        ENNReal.ofReal
          (Real.exp (-(μ.mass : ℝ)) * Real.exp ((μ.mass : ℝ) * q.toReal)) := by
    calc
      _ = ∑' n : ℕ, ENNReal.ofReal
          (Real.exp (-(μ.mass : ℝ)) * ((μ.mass : ℝ) * q.toReal) ^ n / n.factorial) := by
        rw [lintegral_countable']
        apply tsum_congr
        intro n
        have hpow : q ^ n = ENNReal.ofReal (q.toReal ^ n) := by
          rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hq]
        rw [ProbabilityTheory.poissonMeasure_singleton, hpow,
          ← ENNReal.ofReal_mul (pow_nonneg ENNReal.toReal_nonneg n)]
        congr 1
        rw [mul_pow]
        ring
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          hseries.summable, hseries.tsum_eq]
  have hI : (∫⁻ u, 1 - g u ∂(μ : Measure ℝ)) =
      (μ.mass : ℝ≥0∞) * (1 - q) := by
    rw [coe_eq_mass_smul_normalize μ, lintegral_smul_measure,
      lintegral_sub hg hq (Filter.Eventually.of_forall hg_one)]
    simp [q, smul_eq_mul]
  have hfinite : (μ.mass : ℝ≥0∞) * (1 - q) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [lintegral_finitePoissonLaw_normalized μ _ hF]
  simp_rw [htuple]
  rw [hpoisson]
  change ENNReal.ofReal
      (Real.exp (-(μ.mass : ℝ)) * Real.exp ((μ.mass : ℝ) * q.toReal)) =
    EReal.exp (-((∫⁻ u, 1 - g u ∂(μ : Measure ℝ)) : EReal))
  rw [hI, ← EReal.coe_ennreal_toReal hfinite, ← EReal.coe_neg, EReal.exp_coe,
    ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sub_of_le hq_one ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [← Real.exp_add]
  congr 2
  ring

theorem lintegral_exp_neg_fragmentLaw
    (ζ : ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ c, EReal.exp (-((∫⁻ u, h u ∂(c : Measure ℝ)) : EReal))
      ∂(fragmentLaw ζ)) =
      EReal.exp (-((∫⁻ u,
        1 - EReal.exp (-((ENNReal.ofReal u * h u : ℝ≥0∞) : EReal))
        ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
          (fun u : ℝ => ENNReal.ofReal (1 / u)))) : EReal)) := by
  classical
  let : ∀ k : ℤ, IsProbabilityMeasure (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  let P : Measure (ℤ → FiniteMeasure ℝ) :=
    Measure.infinitePi (fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k))
  have hm : Measurable (fun c : FiniteMeasure ℝ => ∫⁻ u, h u ∂(c : Measure ℝ)) :=
    (Measure.measurable_lintegral hh).comp measurable_subtype_coe
  have hF : Measurable (fun c : FiniteMeasure ℝ =>
      EReal.exp (-((∫⁻ u, h u ∂(c : Measure ℝ)) : EReal))) :=
    hm.coe_ereal_ennreal.neg.ereal_exp
  have hc : Continuous (fun a : ℝ≥0∞ => EReal.exp (-(a : EReal))) :=
    ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg
  have he (s : Finset ℤ) :
      (∫⁻ ω : ℤ → FiniteMeasure ℝ,
        EReal.exp (-((∑ k ∈ s, ∫⁻ u, h u ∂(ω k : Measure ℝ) : ℝ≥0∞) : EReal))
        ∂P) =
      EReal.exp (-((∑ k ∈ s, ∫⁻ u,
        1 - EReal.exp (-((ENNReal.ofReal u * h u : ℝ≥0∞) : EReal))
        ∂(cappedDyadicIntensity ζ k : Measure ℝ) : ℝ≥0∞) : EReal)) := by
    simp_rw [exp_neg_ennreal_sum]
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun s _
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k)) (fun _ => hF))
      (fun k => hF.comp (measurable_pi_apply k))]
    apply Finset.prod_congr rfl
    intro k _
    rw [(measurePreserving_eval_infinitePi
      (fun j : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ j)) k).lintegral_comp hF,
      lintegral_exp_neg_finitePoissonLaw _ h hh]
  have hlim : Filter.Tendsto
      (fun s : Finset ℤ => ∫⁻ ω : ℤ → FiniteMeasure ℝ,
        EReal.exp (-((∑ k ∈ s, ∫⁻ u, h u ∂(ω k : Measure ℝ) : ℝ≥0∞) : EReal))
        ∂P)
      Filter.atTop
      (nhds (∫⁻ ω : ℤ → FiniteMeasure ℝ,
        EReal.exp (-((∫⁻ u, h u ∂(Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))) : EReal))
        ∂P)) := by
    apply tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    · exact Filter.Eventually.of_forall fun s =>
        (s.measurable_fun_sum fun k _ =>
          hm.comp (measurable_pi_apply k)).coe_ereal_ennreal.neg.ereal_exp
    · simp [EReal.coe_ennreal_nonneg]
    · simp
    · exact Filter.Eventually.of_forall fun ω =>
        (hc.tendsto _).comp
          (hasSum_lintegral_measure h (fun k : ℤ => (ω k : Measure ℝ)))
  have hi := (hc.tendsto _).comp (hasSum_lintegral_measure
    (fun u : ℝ => 1 - EReal.exp (-((ENNReal.ofReal u * h u : ℝ≥0∞) : EReal)))
    (fun k : ℤ => (cappedDyadicIntensity ζ k : Measure ℝ)))
  rw [sum_cappedDyadicIntensity] at hi
  simp only [Function.comp_def, SummationFilter.unconditional_filter] at hi
  unfold fragmentLaw
  rw [lintegral_map hF measurable_finiteFragments]
  calc
    _ = (∫⁻ ω : ℤ → FiniteMeasure ℝ,
        EReal.exp (-((∫⁻ u, h u ∂(Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))) : EReal))
        ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [ae_isFiniteMeasure_fragment_sum ζ] with ω hω
      simp [finiteFragments, hω]
    _ = _ := tendsto_nhds_unique (by simpa only [he] using hlim) hi

theorem integral_exp_neg_mass_fragmentLaw
    (ζ s : ℝ) (hζ : 0 < ζ) (hs : 0 ≤ s) :
    (∫ c, Real.exp (-s * (c.mass : ℝ)) ∂(fragmentLaw ζ)) =
      Real.exp (∫ u in (0 : ℝ)..ζ, (Real.exp (-s * u) - 1) / u) := by
  let : IsProbabilityMeasure (fragmentLaw ζ) := fragmentLaw_isProbabilityMeasure ζ
  have hmassm : Measurable (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) := by
    have hm : Measurable (fun c : FiniteMeasure ℝ => (c : Measure ℝ) Set.univ) :=
      (Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe
    simpa only [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using hm.ennreal_toReal
  have hleftInt : Integrable
      (fun c : FiniteMeasure ℝ => Real.exp (-s * (c.mass : ℝ)))
      (fragmentLaw ζ) := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_const.mul hmassm).exp.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) c.mass.coe_nonneg)
  have hbound : ∀ u ∈ Set.Ioc (0 : ℝ) ζ,
      0 ≤ (1 - Real.exp (-s * u)) / u ∧
      (1 - Real.exp (-s * u)) / u ≤ s := by
    intro u hu
    constructor
    · exact div_nonneg
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hu.1.le))) hu.1.le
    · apply (div_le_iff₀ hu.1).2
      linarith [Real.add_one_le_exp (-s * u)]
  have hkernelInt : Integrable
      (fun u : ℝ => (1 - Real.exp (-s * u)) / u)
      (volume.restrict (Set.Ioc (0 : ℝ) ζ)) := by
    refine (integrable_const s).mono'
      ((measurable_const.sub (measurable_const.mul measurable_id).exp).div
        measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound u hu).1]
    exact (hbound u hu).2
  have hkernelNonneg : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) ζ),
      0 ≤ (1 - Real.exp (-s * u)) / u :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => (hbound u hu).1
  have hinner (u : ℝ) (hu : 0 ≤ u) :
      EReal.exp (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal)) =
        ENNReal.ofReal (Real.exp (-s * u)) := by
    rw [mul_comm (ENNReal.ofReal u) (ENNReal.ofReal s),
      ← ENNReal.ofReal_mul hs, EReal.coe_ennreal_ofReal,
      max_eq_left (mul_nonneg hs hu),
      ← EReal.coe_neg, EReal.exp_coe]
    simp only [neg_mul]
  have hintensity :
      (∫⁻ u, 1 - EReal.exp
        (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))
        ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
          (fun u : ℝ => ENNReal.ofReal (1 / u)))) =
      ENNReal.ofReal (∫ u in Set.Ioc (0 : ℝ) ζ,
        (1 - Real.exp (-s * u)) / u) := by
    rw [ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change ENNReal.ofReal (1 / u) *
        (1 - EReal.exp
          (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal ((1 - Real.exp (-s * u)) / u)
    rw [hinner u hu.1.le, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (div_nonneg zero_le_one hu.1.le)]
    congr 1
    ring
  have hpoint (c : FiniteMeasure ℝ) :
      EReal.exp (-((∫⁻ _u, ENNReal.ofReal s ∂(c : Measure ℝ)) : EReal)) =
        ENNReal.ofReal (Real.exp (-s * (c.mass : ℝ))) := by
    simpa only [lintegral_const, ← FiniteMeasure.ennreal_mass,
      ENNReal.ofReal_coe_nnreal, mul_comm] using hinner (c.mass : ℝ) c.mass.coe_nonneg
  have horientation :
      (∫ u in (0 : ℝ)..ζ, (Real.exp (-s * u) - 1) / u) =
        -(∫ u in Set.Ioc (0 : ℝ) ζ, (1 - Real.exp (-s * u)) / u) := by
    rw [intervalIntegral.integral_of_le hζ.le, ← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring
  have hmain := lintegral_exp_neg_fragmentLaw ζ
    (fun _ => ENNReal.ofReal s) measurable_const
  simp_rw [hpoint] at hmain
  rw [← ofReal_integral_eq_lintegral_ofReal hleftInt
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _),
    hintensity, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg_of_ae hkernelNonneg),
    ← EReal.coe_neg, EReal.exp_coe] at hmain
  rw [horientation]
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun _ => Real.exp_nonneg _) (Real.exp_nonneg _)).1 hmain

#print axioms exp_neg_ennreal_sum
#print axioms lintegral_exp_neg_finitePoissonLaw
#print axioms lintegral_exp_neg_fragmentLaw
#print axioms integral_exp_neg_mass_fragmentLaw

end PrimeGap186
