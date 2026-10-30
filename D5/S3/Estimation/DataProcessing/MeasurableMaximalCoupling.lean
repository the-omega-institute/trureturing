/- GID: D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling
   generality: I
   mirror-B: D5/B/S3/Estimation/DataProcessing/MeasurableMaximalCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Kernel.RadonNikodym]
   utility: none
   digest: Standard Borel state spaces admit measurable maximal coupling kernels. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Measurable maximal couplings

The individual-law substrate below is selectively transplanted from Jiyuan Tan's
Causalean source at a7085d88d2e4b30003db7097ca374f4718da0f01:
`Causalean/Stat/Minimax/TotalVariation.lean`, `Scheffe.lean`, and
`OverlapCoupling.lean`. Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under the Apache License, Version 2.0. Full license and NOTICE:
`docs/reports/licenses/causalsmith-maximal-coupling/`.

The transplanted declarations have private visibility, local namespace resolution,
and imports adapted to the receiver. Their individual-law mathematics is upstream
work. Retirement uses equivalent suppliers and checked consumer replacements at the
receiver's actually pinned Mathlib revision, as specified in the source notice.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables

section PortedIndividualLaws
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private noncomputable def tvDist (μ ν : Measure Ω) : ℝ :=
  ⨆ A : {A : Set Ω // MeasurableSet A}, |μ.real A.1 - ν.real A.1|

private theorem abs_measureReal_sub_le_one (A : Set Ω) : |μ.real A - ν.real A| ≤ 1 := by
  have hμ : μ.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := μ) (Set.subset_univ A) (measure_ne_top μ _)
      simpa [probReal_univ] using this⟩
  have hν : ν.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := ν) (Set.subset_univ A) (measure_ne_top ν _)
      simpa [probReal_univ] using this⟩
  rw [abs_le]
  constructor <;> [nlinarith [hμ.1, hμ.2, hν.1, hν.2]; nlinarith [hμ.1, hμ.2, hν.1, hν.2]]

private theorem bddAbove_tvDist_range :
    BddAbove (Set.range fun A : {A : Set Ω // MeasurableSet A} => |μ.real A.1 - ν.real A.1|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact abs_measureReal_sub_le_one A.1

private theorem abs_measureReal_sub_le_tvDist {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ tvDist μ ν :=
  le_ciSup bddAbove_tvDist_range (⟨A, hA⟩ : {A : Set Ω // MeasurableSet A})

private theorem tvDist_nonneg : 0 ≤ tvDist μ ν := by
  have := abs_measureReal_sub_le_tvDist (μ := μ) (ν := ν) MeasurableSet.empty
  simpa using (abs_nonneg _).trans this

private theorem tvDist_le_one : tvDist μ ν ≤ 1 :=
  ciSup_le fun A => abs_measureReal_sub_le_one A.1

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    {f : Ω → ℝ} (hf : Integrable f ν) (hf0 : ∫ x, f x ∂ν = 0)
    {A : Set Ω} (hA : MeasurableSet A) :
    |∫ x in A, f x ∂ν| ≤ (1/2) * ∫ x, |f x| ∂ν := by
  have hfA : IntegrableOn f A ν := hf.integrableOn
  have hfAc : IntegrableOn f Aᶜ ν := hf.integrableOn
  -- `∫_A f + ∫_{Aᶜ} f = 0`
  have hsplit : ∫ x in A, f x ∂ν + ∫ x in Aᶜ, f x ∂ν = 0 := by
    rw [MeasureTheory.integral_add_compl hA hf, hf0]
  have hcompl : ∫ x in Aᶜ, f x ∂ν = -(∫ x in A, f x ∂ν) := by linarith
  -- `∫|f| = ∫_A |f| + ∫_{Aᶜ} |f|`
  have habs : Integrable (fun x => |f x|) ν := hf.abs
  have hsplitabs :
      ∫ x, |f x| ∂ν = (∫ x in A, |f x| ∂ν) + ∫ x in Aᶜ, |f x| ∂ν :=
    (MeasureTheory.integral_add_compl hA habs).symm
  -- bound each piece of `f` by `|f|`
  have hbA : ∫ x in A, f x ∂ν ≤ ∫ x in A, |f x| ∂ν :=
    integral_mono_ae hfA habs.integrableOn (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAc : ∫ x in Aᶜ, f x ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
    integral_mono_ae hfAc habs.integrableOn (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAneg : -(∫ x in A, f x ∂ν) ≤ ∫ x in A, |f x| ∂ν := by
    have : ∫ x in A, (-f x) ∂ν ≤ ∫ x in A, |f x| ∂ν :=
      integral_mono_ae hfA.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => (neg_le_abs _))
    rwa [integral_neg] at this
  have hbAcneg : -(∫ x in Aᶜ, f x ∂ν) ≤ ∫ x in Aᶜ, |f x| ∂ν := by
    have : ∫ x in Aᶜ, (-f x) ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
      integral_mono_ae hfAc.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => (neg_le_abs _))
    rwa [integral_neg] at this
  rw [abs_le, hsplitabs]
  constructor
  · -- `-(½(∫_A|f| + ∫_{Aᶜ}|f|)) ≤ ∫_A f`
    nlinarith [hbAneg, hbAc, hcompl]
  · -- `∫_A f ≤ ½(∫_A|f| + ∫_{Aᶜ}|f|)`
    nlinarith [hbA, hbAcneg, hcompl]

private lemma tvDist_eq_half_integral_abs_rnDeriv_sub
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsFiniteMeasure xi] (hmu : mu ≪ xi) (hnu : nu ≪ xi) :
    tvDist mu nu =
      (1 / 2 : ℝ) * ∫ x,
        |(mu.rnDeriv xi x).toReal - (nu.rnDeriv xi x).toReal| ∂xi := by
  let p : X → ℝ := fun x => (mu.rnDeriv xi x).toReal
  let q : X → ℝ := fun x => (nu.rnDeriv xi x).toReal
  let d : X → ℝ := fun x => p x - q x
  have hp : Integrable p xi := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q xi := Measure.integrable_toReal_rnDeriv
  have hd : Integrable d xi := hp.sub hq
  have hd0 : ∫ x, d x ∂xi = 0 := by
    rw [show d = fun x => p x - q x from rfl, integral_sub hp hq]
    rw [show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
      show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hmu,
      Measure.integral_toReal_rnDeriv hnu]
    simp
  apply le_antisymm
  · unfold tvDist
    apply ciSup_le
    rintro ⟨A, hA⟩
    have hgap : mu.real A - nu.real A = ∫ x in A, d x ∂xi := by
      rw [show d = fun x => p x - q x from rfl,
        integral_sub hp.integrableOn hq.integrableOn,
        show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
        show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
        Measure.setIntegral_toReal_rnDeriv hmu,
        Measure.setIntegral_toReal_rnDeriv hnu]
    rw [hgap]
    exact abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
      hd hd0 hA
  · let A : Set X := {x | 0 ≤ d x}
    have hA : MeasurableSet A := by
      dsimp [A, d, p, q]
      exact measurableSet_le measurable_const
        ((Measure.measurable_rnDeriv mu xi).ennreal_toReal.sub
          (Measure.measurable_rnDeriv nu xi).ennreal_toReal)
    have hsplit : ∫ x in A, d x ∂xi + ∫ x in Aᶜ, d x ∂xi = 0 := by
      rw [MeasureTheory.integral_add_compl hA hd, hd0]
    have hpos : 0 ≤ ∫ x in A, d x ∂xi := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hx
    have habs : ∫ x, |d x| ∂xi = 2 * ∫ x in A, d x ∂xi := by
      rw [← MeasureTheory.integral_add_compl hA hd.abs]
      have h1 : ∫ x in A, |d x| ∂xi = ∫ x in A, d x ∂xi := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        exact abs_of_nonneg hx
      have h2 : ∫ x in Aᶜ, |d x| ∂xi = -(∫ x in Aᶜ, d x ∂xi) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA.compl] with x hx
        exact abs_of_nonpos (le_of_not_ge hx)
      rw [h1, h2]
      linarith
    have hgap : mu.real A - nu.real A = ∫ x in A, d x ∂xi := by
      rw [show d = fun x => p x - q x from rfl,
        integral_sub hp.integrableOn hq.integrableOn,
        show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
        show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
        Measure.setIntegral_toReal_rnDeriv hmu,
        Measure.setIntegral_toReal_rnDeriv hnu]
    have htv := abs_measureReal_sub_le_tvDist
      (μ := mu) (ν := nu) hA
    change (1 / 2 : ℝ) * ∫ x, |d x| ∂xi ≤ _
    rw [habs]
    rw [hgap, abs_of_nonneg hpos] at htv
    linarith

private noncomputable def rnCommonPart
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) : Measure X :=
  xi.withDensity fun x => min (mu.rnDeriv xi x) (nu.rnDeriv xi x)

private lemma rnCommonPart_le_left
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure xi] (hmu : mu ≪ xi) :
    rnCommonPart mu nu xi ≤ mu := by
  calc
    rnCommonPart mu nu xi ≤ xi.withDensity (mu.rnDeriv xi) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall fun x => min_le_left _ _
    _ = mu := Measure.withDensity_rnDeriv_eq mu xi hmu

private lemma rnCommonPart_le_right
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsFiniteMeasure nu] [IsFiniteMeasure xi] (hnu : nu ≪ xi) :
    rnCommonPart mu nu xi ≤ nu := by
  calc
    rnCommonPart mu nu xi ≤ xi.withDensity (nu.rnDeriv xi) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall fun x => min_le_right _ _
    _ = nu := Measure.withDensity_rnDeriv_eq nu xi hnu

private lemma rnCommonPart_mass_eq_one_sub_tvDist
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsFiniteMeasure xi] (hmu : mu ≪ xi) (hnu : nu ≪ xi) :
    rnCommonPart mu nu xi Set.univ =
      ENNReal.ofReal (1 - tvDist mu nu) := by
  let p : X → ℝ := fun x => (mu.rnDeriv xi x).toReal
  let q : X → ℝ := fun x => (nu.rnDeriv xi x).toReal
  have hp : Integrable p xi := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q xi := Measure.integrable_toReal_rnDeriv
  have hformula : ∀ x, min (p x) (q x) =
      (p x + q x - |p x - q x|) / 2 := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hmin : Integrable (fun x => min (p x) (q x)) xi := by
    refine ((hp.add hq).sub (hp.sub hq).abs |>.div_const 2).congr ?_
    exact Filter.Eventually.of_forall fun x => (hformula x).symm
  have hmin_nonneg : 0 ≤ᵐ[xi] fun x => min (p x) (q x) := by
    filter_upwards [] with x
    exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hp_one : ∫ x, p x ∂xi = 1 := by
    rw [show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hmu]
    simp
  have hq_one : ∫ x, q x ∂xi = 1 := by
    rw [show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hnu]
    simp
  have hreal : ∫ x, min (p x) (q x) ∂xi =
      1 - tvDist mu nu := by
    have hid : (fun x => min (p x) (q x)) =
        fun x => (p x + q x - |p x - q x|) / 2 := by
      funext x; exact hformula x
    rw [hid, integral_div]
    rw [integral_sub (f := fun x => p x + q x)
      (g := fun x => |p x - q x|) (hp.add hq) (hp.sub hq).abs]
    rw [integral_add hp hq, hp_one, hq_one,
      tvDist_eq_half_integral_abs_rnDeriv_sub mu nu xi hmu hnu]
    ring
  rw [rnCommonPart, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    ∫⁻ x, min (mu.rnDeriv xi x) (nu.rnDeriv xi x) ∂xi =
        ∫⁻ x, ENNReal.ofReal (min (p x) (q x)) ∂xi := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top mu xi,
        Measure.rnDeriv_lt_top nu xi] with x hpx hqx
      simp only [ENNReal.ofReal_min]
      rw [ENNReal.ofReal_toReal hpx.ne, ENNReal.ofReal_toReal hqx.ne]
    _ = ENNReal.ofReal (∫ x, min (p x) (q x) ∂xi) := by
      exact (ofReal_integral_eq_lintegral_ofReal hmin hmin_nonneg).symm
    _ = _ := by rw [hreal]

private lemma measure_eq_of_tvDist_eq_zero
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : tvDist mu nu = 0) : mu = nu := by
  ext A hA
  have hgap := abs_measureReal_sub_le_tvDist
    (μ := mu) (ν := nu) hA
  rw [h] at hgap
  have hre : mu.real A = nu.real A := by
    have := abs_nonneg (mu.real A - nu.real A)
    rw [abs_nonpos_iff] at hgap
    linarith
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu A) (measure_ne_top nu A)]
  exact hre

private noncomputable def overlapCoupling
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    Measure (X × X) :=
  if hzero : tvDist mu nu = 0 then
    mu.map fun x => (x, x)
  else
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    c.map (fun x => (x, x)) +
      (ENNReal.ofReal (tvDist mu nu))⁻¹ • (rmu.prod rnu)

private lemma residual_mass
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    (mu - c) Set.univ = ENNReal.ofReal (tvDist mu nu) := by
  dsimp
  have hmu : mu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right _
  have hnu : nu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hc : rnCommonPart mu nu (mu + nu) ≤ mu :=
    rnCommonPart_le_left mu nu (mu + nu) hmu
  letI : IsFiniteMeasure (rnCommonPart mu nu (mu + nu)) :=
    isFiniteMeasure_of_le mu hc
  rw [Measure.sub_apply MeasurableSet.univ hc,
    rnCommonPart_mass_eq_one_sub_tvDist mu nu (mu + nu) hmu hnu]
  have htv0 := tvDist_nonneg (μ := mu) (ν := nu)
  have htv1 := tvDist_le_one (μ := mu) (ν := nu)
  rw [measure_univ, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - tvDist mu nu)]
  congr 1
  ring

private lemma residual_mass_right
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    (nu - c) Set.univ = ENNReal.ofReal (tvDist mu nu) := by
  dsimp
  have hmu : mu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right _
  have hnu : nu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hc : rnCommonPart mu nu (mu + nu) ≤ nu :=
    rnCommonPart_le_right mu nu (mu + nu) hnu
  letI : IsFiniteMeasure (rnCommonPart mu nu (mu + nu)) :=
    isFiniteMeasure_of_le nu hc
  rw [Measure.sub_apply MeasurableSet.univ hc,
    rnCommonPart_mass_eq_one_sub_tvDist mu nu (mu + nu) hmu hnu]
  have htv0 := tvDist_nonneg (μ := mu) (ν := nu)
  have htv1 := tvDist_le_one (μ := mu) (ν := nu)
  rw [measure_univ, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - tvDist mu nu)]
  congr 1
  ring

private lemma overlapCoupling_map_fst
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (overlapCoupling mu nu).map Prod.fst = mu := by
  by_cases hzero : tvDist mu nu = 0
  · rw [overlapCoupling, dif_pos hzero,
      Measure.map_map (μ := mu) (f := fun x : X => (x, x))
        (g := Prod.fst) measurable_fst (measurable_id.prodMk measurable_id)]
    change mu.map id = mu
    exact Measure.map_id
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    have hmu : mu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right _
    have hc : c ≤ mu := rnCommonPart_le_left mu nu xi hmu
    letI : IsFiniteMeasure c := isFiniteMeasure_of_le mu hc
    have hrnu : rnu Set.univ =
        ENNReal.ofReal (tvDist mu nu) := residual_mass_right mu nu
    rw [overlapCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.map_add, Measure.map_smul, Measure.map_map, Measure.map_fst_prod,
      hrnu]
    rw [← mul_smul, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne
        (tvDist_nonneg (μ := mu) (ν := nu)) (Ne.symm hzero)))
      ENNReal.ofReal_ne_top, one_smul]
    rw [show (Prod.fst ∘ fun x : X => (x, x)) = id by rfl, Measure.map_id,
      add_comm, Measure.sub_add_cancel_of_le hc]
    all_goals fun_prop

private lemma overlapCoupling_map_snd
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (overlapCoupling mu nu).map Prod.snd = nu := by
  by_cases hzero : tvDist mu nu = 0
  · have heq : mu = nu := measure_eq_of_tvDist_eq_zero mu nu hzero
    rw [overlapCoupling, dif_pos hzero,
      Measure.map_map (μ := mu) (f := fun x : X => (x, x))
        (g := Prod.snd) measurable_snd (measurable_id.prodMk measurable_id)]
    change mu.map id = nu
    rw [Measure.map_id, heq]
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    have hnu : nu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right' _
    have hc : c ≤ nu := rnCommonPart_le_right mu nu xi hnu
    letI : IsFiniteMeasure c := isFiniteMeasure_of_le nu hc
    have hrmu : rmu Set.univ =
        ENNReal.ofReal (tvDist mu nu) := residual_mass mu nu
    rw [overlapCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.map_add, Measure.map_smul, Measure.map_map, Measure.map_snd_prod,
      hrmu]
    rw [← mul_smul, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne
        (tvDist_nonneg (μ := mu) (ν := nu)) (Ne.symm hzero)))
      ENNReal.ofReal_ne_top, one_smul]
    rw [show (Prod.snd ∘ fun x : X => (x, x)) = id by rfl, Measure.map_id,
      add_comm, Measure.sub_add_cancel_of_le hc]
    all_goals fun_prop

private noncomputable instance overlapCoupling.instIsProbabilityMeasure
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (overlapCoupling mu nu) := by
  constructor
  have h := congrArg (fun m : Measure X => m Set.univ)
    (overlapCoupling_map_fst mu nu)
  change ((overlapCoupling mu nu).map Prod.fst) Set.univ = mu Set.univ at h
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa using h

private lemma overlapCoupling_eq_mass_ge
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ENNReal.ofReal (1 - tvDist mu nu) ≤
      overlapCoupling mu nu {p | p.1 = p.2} := by
  let D : Set (X × X) := {p | p.1 = p.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  change ENNReal.ofReal (1 - tvDist mu nu) ≤
    overlapCoupling mu nu D
  by_cases hzero : tvDist mu nu = 0
  · rw [overlapCoupling, dif_pos hzero, Measure.map_apply
      (μ := mu) (f := fun x : X => (x, x))
      (measurable_id.prodMk measurable_id) hD]
    simp [D, hzero]
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    have hmu : mu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right _
    have hnu : nu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right' _
    have hcmass : c Set.univ =
        ENNReal.ofReal (1 - tvDist mu nu) :=
      rnCommonPart_mass_eq_one_sub_tvDist mu nu xi hmu hnu
    rw [overlapCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.add_apply]
    calc
      ENNReal.ofReal (1 - tvDist mu nu) = c Set.univ := hcmass.symm
      _ = c.map (fun x => (x, x)) D := by
        rw [Measure.map_apply (μ := c) (f := fun x : X => (x, x))
          (measurable_id.prodMk measurable_id) hD]
        congr 1
        ext x
        simp [D]
      _ ≤ c.map (fun x => (x, x)) D +
          ((ENNReal.ofReal (tvDist mu nu))⁻¹ •
            ((mu - c).prod (nu - c))) D := le_add_right le_rfl

end PortedIndividualLaws

section KernelFamily
variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X] [StandardBorelSpace X]
  (P Q : Kernel Z X) [IsMarkovKernel P] [IsMarkovKernel Q]

private def commonKernel : Kernel Z X :=
  (P + Q).withDensity (fun z x => min (P.rnDeriv (P + Q) z x) (Q.rnDeriv (P + Q) z x))

private theorem commonKernel_apply (z : Z) :
    commonKernel P Q z = rnCommonPart (P z) (Q z) (P z + Q z) := by
  rw [commonKernel, Kernel.withDensity_apply _
    ((Kernel.measurable_rnDeriv P (P + Q)).min (Kernel.measurable_rnDeriv Q (P + Q)))]
  simp only [rnCommonPart, Kernel.add_apply]
  apply withDensity_congr_ae
  have hp := Kernel.rnDeriv_eq_rnDeriv_measure (κ := P) (η := P + Q) (a := z)
  have hq := Kernel.rnDeriv_eq_rnDeriv_measure (κ := Q) (η := P + Q) (a := z)
  simp only [Kernel.add_apply] at hp hq
  filter_upwards [hp, hq] with x hx hy
  rw [hx, hy]

private theorem commonKernel_le_left : commonKernel P Q ≤ P := by
  intro z
  rw [commonKernel_apply]
  exact rnCommonPart_le_left _ _ _ (Measure.AbsolutelyContinuous.rfl.add_right _)

private theorem commonKernel_le_right : commonKernel P Q ≤ Q := by
  intro z
  rw [commonKernel_apply]
  exact rnCommonPart_le_right _ _ _ (Measure.AbsolutelyContinuous.rfl.add_right' _)

private instance commonKernel_finite : IsFiniteKernel (commonKernel P Q) :=
  isFiniteKernel_of_le (commonKernel_le_left P Q)

private def dominatedDifference (K L : Kernel Z X) [IsFiniteKernel L] (h : L ≤ K) :
    Kernel Z X where
  toFun z := K z - L z
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun E hE => ?_
    simp only [Measure.sub_apply hE (h _)]
    exact (K.measurable_coe hE).sub (L.measurable_coe hE)

private theorem dominatedDifference_apply (K L : Kernel Z X) [IsFiniteKernel L]
    (h : L ≤ K) (z : Z) : dominatedDifference K L h z = K z - L z := rfl

private instance dominatedDifference_finite (K L : Kernel Z X)
    [IsFiniteKernel K] [IsFiniteKernel L] (h : L ≤ K) :
    IsFiniteKernel (dominatedDifference K L h) :=
  isFiniteKernel_of_le (fun _ => Measure.sub_le)

private def leftResidual : Kernel Z X :=
  dominatedDifference P (commonKernel P Q) (commonKernel_le_left P Q)

private def rightResidual : Kernel Z X :=
  dominatedDifference Q (commonKernel P Q) (commonKernel_le_right P Q)

private instance leftResidual_finite : IsFiniteKernel (leftResidual P Q) :=
  inferInstanceAs (IsFiniteKernel (dominatedDifference P (commonKernel P Q) _))

private instance rightResidual_finite : IsFiniteKernel (rightResidual P Q) :=
  inferInstanceAs (IsFiniteKernel (dominatedDifference Q (commonKernel P Q) _))

private theorem leftResidual_mass (z : Z) :
    leftResidual P Q z Set.univ = ENNReal.ofReal (tvDist (P z) (Q z)) := by
  change (P z - commonKernel P Q z) Set.univ = _
  rw [commonKernel_apply]
  exact residual_mass (P z) (Q z)

private theorem zeroSet_measurable : MeasurableSet {z | tvDist (P z) (Q z) = 0} := by
  have heq : {z | tvDist (P z) (Q z) = 0} = {z | leftResidual P Q z Set.univ = 0} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, leftResidual_mass, ENNReal.ofReal_eq_zero]
    exact ⟨fun h => h.le, fun h => le_antisymm h tvDist_nonneg⟩
  rw [heq]
  exact (leftResidual P Q).measurable_coe MeasurableSet.univ (measurableSet_singleton 0)

private theorem residualWeight_measurable :
    Measurable (Function.uncurry (fun z (_ : X × X) =>
      (leftResidual P Q z Set.univ)⁻¹)) :=
  ((leftResidual P Q).measurable_coe MeasurableSet.univ).inv.comp measurable_fst

/-- One measurable coupling family, with a diagonal branch on equal rows and a
common-part plus normalized residual-product branch on all other rows. -/
def maximalCoupling : Kernel Z (X × X) := by
  classical
  exact Kernel.piecewise (zeroSet_measurable P Q)
    (P.map (fun x => (x, x)))
    ((commonKernel P Q).map (fun x => (x, x)) +
      (leftResidual P Q ×ₖ rightResidual P Q).withDensity
        (fun z _ => (leftResidual P Q z Set.univ)⁻¹))

private theorem maximalCoupling_apply (z : Z) :
    maximalCoupling P Q z = overlapCoupling (P z) (Q z) := by
  classical
  rw [maximalCoupling, Kernel.piecewise_apply]
  by_cases h : tvDist (P z) (Q z) = 0
  · simp only [Set.mem_setOf_eq, if_pos h, overlapCoupling, dif_pos h]
    exact Kernel.map_apply _ (measurable_id.prodMk measurable_id) _
  · simp only [Set.mem_setOf_eq, if_neg h, overlapCoupling, dif_neg h]
    rw [Kernel.add_apply, Kernel.map_apply (commonKernel P Q)
        (f := fun x : X => (x, x)) (measurable_id.prodMk measurable_id),
      Kernel.withDensity_apply _ (residualWeight_measurable P Q),
      withDensity_const, Kernel.prod_apply, leftResidual_mass]
    simp only [leftResidual, rightResidual, dominatedDifference_apply, commonKernel_apply]

end KernelFamily

private theorem event_tv_ofReal {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    measurableTotalVariation μ ν = ENNReal.ofReal (tvDist μ ν) := by
  have hbound : measurableTotalVariation μ ν ≤ 1 :=
    iSup_le fun _ => max_le (tsub_le_self.trans prob_le_one)
      (tsub_le_self.trans prob_le_one)
  have hfin : measurableTotalVariation μ ν ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) hbound
  have h := (event_tv_normalization (⟨μ, inferInstance⟩ : ProbabilityMeasure X)
      (⟨ν, inferInstance⟩ : ProbabilityMeasure X)).1
  change (measurableTotalVariation μ ν).toReal = tvDist μ ν at h
  rw [← h]
  exact (ENNReal.ofReal_toReal hfin).symm

private theorem event_tv_maps_le {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (π : Measure A) (f g : A → X) (hf : Measurable f) (hg : Measurable g) :
    measurableTotalVariation (π.map f) (π.map g) ≤ π {a | f a ≠ g a} := by
  exact gate_tv π {a | f a = g a} f g hf hg (fun _ ha => ha)

private theorem overlapCoupling_offDiagonal {X : Type*} [MeasurableSpace X]
    [MeasurableEq X] (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    overlapCoupling μ ν {p | p.1 ≠ p.2} = measurableTotalVariation μ ν := by
  apply le_antisymm
  · rw [event_tv_ofReal]
    have hD : MeasurableSet {p : X × X | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have htv := tvDist_le_one (μ := μ) (ν := ν)
    calc
      overlapCoupling μ ν {p | p.1 ≠ p.2} =
          1 - overlapCoupling μ ν {p | p.1 = p.2} := by
        rw [show {p : X × X | p.1 ≠ p.2} = {p | p.1 = p.2}ᶜ from rfl,
          measure_compl hD (measure_ne_top _ _), measure_univ]
      _ ≤ 1 - ENNReal.ofReal (1 - tvDist μ ν) :=
        tsub_le_tsub_left (overlapCoupling_eq_mass_ge μ ν) _
      _ = ENNReal.ofReal (tvDist μ ν) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr htv)]
        congr 1
        ring
  · have h := event_tv_maps_le (overlapCoupling μ ν) Prod.fst Prod.snd
      measurable_fst measurable_snd
    rwa [overlapCoupling_map_fst, overlapCoupling_map_snd] at h

/-- Every row is maximally coupled by the same measurable kernel. The parameter
space is arbitrary; only the common state space needs to be standard Borel. -/
theorem maximal_coupling {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [StandardBorelSpace X] (P Q : Kernel Z X) [IsMarkovKernel P] [IsMarkovKernel Q] :
    IsMarkovKernel (maximalCoupling P Q) ∧
      (maximalCoupling P Q).map Prod.fst = P ∧
      (maximalCoupling P Q).map Prod.snd = Q ∧
      ∀ z, maximalCoupling P Q z {p | p.1 ≠ p.2} =
        measurableTotalVariation (P z) (Q z) := by
  have hmarkov : IsMarkovKernel (maximalCoupling P Q) := by
    constructor
    intro z
    rw [maximalCoupling_apply]
    infer_instance
  refine ⟨hmarkov, ?_, ?_, ?_⟩
  · ext z : 1
    rw [Kernel.map_apply _ measurable_fst, maximalCoupling_apply, overlapCoupling_map_fst]
  · ext z : 1
    rw [Kernel.map_apply _ measurable_snd, maximalCoupling_apply, overlapCoupling_map_snd]
  · intro z
    rw [maximalCoupling_apply]
    exact overlapCoupling_offDiagonal (P z) (Q z)

#print axioms maximal_coupling

end D5.S3.Estimation.DataProcessing.MeasurableMaximalCoupling
