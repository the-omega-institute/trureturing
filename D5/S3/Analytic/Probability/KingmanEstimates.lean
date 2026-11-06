/- GID: D5/S3/Analytic/Probability/KingmanEstimates
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/KingmanEstimates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Greedy subadditive blocks and stationary maximal estimates. -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
complete license retained at docs/reports/lovasz-suppliers/atlas-LICENSE.txt.

Proof source: facebookresearch/atlas-lean, revision
a60759060b5616df0d5775b42da4d337719feb32,
MathlibExt/Dynamics/Ergodic/Kingman.lean,
SHA-256 d7363bfb4d33d73517b93b75e361de0a8e0363f32350e25dd5ce1f6a21b2782c.
Adaptation: native Birkhoff reuse, finite-measure normalization and
almost-everywhere measurable representatives with an internal zeroth reset.
An equivalent declaration in the host-pinned Mathlib replaces this port.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import D5.S3.Analytic.Probability.BirkhoffPointwise

/-! Greedy block and stationary-tail estimates for nonnegative subadditive cocycles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Probability.KingmanEstimates

open MeasureTheory Filter Topology

/-- N6: integrable stationary sequences are o(n) along orbits. -/
theorem ae_tendsto_comp_iterate_div_nat
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφmeas : Measurable φ) (hφint : Integrable φ μ) (hφnn : ∀ x, 0 ≤ φ x) :
    ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => φ ((T^[m]) x) / (m : ℝ)) atTop (nhds 0) := by
  have hbound : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ m in atTop,
      φ ((T^[m]) x) / (m : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hXint : Integrable (fun y => ((k : ℝ) + 1) * φ y) μ := hφint.const_mul _
    have hXnn : ∀ y, 0 ≤ ((k : ℝ) + 1) * φ y := fun y =>
      mul_nonneg (by positivity) (hφnn y)
    have htsum : ∑' (m : ℕ), μ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} < ⊤ := by
      let : MeasureSpace α := ⟨μ⟩
      exact ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hXint hXnn
    have hmeas_set : ∀ m : ℕ,
        MeasurableSet {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} := by
      intro m
      have h : MeasurableSet {y | ((m : ℝ)) < ((k : ℝ) + 1) * φ y} :=
        measurableSet_lt measurable_const (measurable_const.mul hφmeas)
      simpa only [Set.mem_Ioi] using h
    have htsum2 : ∑' (m : ℕ),
        μ ((T^[m]) ⁻¹' {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}) ≠ ⊤ := by
      have hpre : ∀ m : ℕ, μ ((T^[m]) ⁻¹' {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}) =
          μ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} :=
        fun m => (hT.iterate m).measure_preimage ((hmeas_set m).nullMeasurableSet)
      exact ne_of_lt (by simpa only [hpre] using htsum)
    have hbc := MeasureTheory.ae_eventually_notMem htsum2
    filter_upwards [hbc] with x hx
    filter_upwards [hx, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hK : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
    have hle : ((k : ℝ) + 1) * φ ((T^[m]) x) ≤ (m : ℝ) := by
      rw [← not_lt]
      intro hcon
      apply hm
      change (T^[m]) x ∈ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}
      change ((m : ℝ)) < ((k : ℝ) + 1) * φ ((T^[m]) x)
      exact hcon
    have h1 : φ ((T^[m]) x) ≤ (m : ℝ) / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hK, mul_comm]
      exact hle
    have h2 : (1 / ((k : ℝ) + 1)) * (m : ℝ) = (m : ℝ) / ((k : ℝ) + 1) := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [div_le_iff₀ hm0, h2]
    exact h1
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ᶠ m in atTop,
      φ ((T^[m]) x) / (m : ℝ) ≤ 1 / ((k : ℝ) + 1) :=
    (MeasureTheory.ae_all_iff).mpr hbound
  filter_upwards [hall] with x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hx k)
  refine ⟨N1, fun m hm => ?_⟩
  have hmb := hN1 m hm
  have hnn : 0 ≤ φ ((T^[m]) x) / (m : ℝ) := div_nonneg (hφnn _) (Nat.cast_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact lt_of_le_of_lt hmb hk


/-- N9: Steele's greedy block decomposition bound (pure combinatorics). -/
theorem greedy_block_bound
    (F : ℕ → ℕ → ℝ) (hFnonneg : ∀ k n, 0 ≤ F k n) (hF0 : ∀ k, F k 0 = 0)
    (hFsub : ∀ k m n, F k (m + n) ≤ F k m + F (k + m) n)
    (B : ℕ → Prop) [DecidablePred B]
    (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hgood : ∀ k, ¬ B k → ∃ n, 1 ≤ n ∧ n ≤ N ∧ F k n ≤ n * c) :
    ∀ M : ℕ, F 0 M ≤ M * c + (∑ k ∈ Finset.range M, if B k then F k 1 else 0) +
      (∑ k ∈ Finset.range M, if M ≤ k + N then F k 1 else 0) := by
  intro M
  have hifnn : ∀ k, 0 ≤ (if B k then F k 1 else 0) := by
    intro k
    split_ifs with h
    · exact hFnonneg k 1
    · exact le_rfl
  have hifnn2 : ∀ k, 0 ≤ (if M ≤ k + N then F k 1 else 0) := by
    intro k
    split_ifs with h
    · exact hFnonneg k 1
    · exact le_rfl
  -- split off the first term of a sum over Ico
  have hsplit : ∀ (g : ℕ → ℝ) (a b : ℕ), a < b →
      (∑ k ∈ Finset.Ico a b, g k) = g a + ∑ k ∈ Finset.Ico (a + 1) b, g k := by
    intro g a b hab
    have hIco : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hIco, Finset.sum_insert (by rw [Finset.mem_Ico]; omega)]
  have key : ∀ r, r ≤ M → ∀ j, M - r = j → F j r ≤ r * c +
      (∑ k ∈ Finset.Ico j M, if B k then F k 1 else 0) +
      (∑ k ∈ Finset.Ico j M, if M ≤ k + N then F k 1 else 0) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrM j hrj
      by_cases r0 : r = 0
      · subst r0
        simp only [Nat.sub_zero] at hrj
        subst hrj
        rw [hF0 M]
        have s1 : 0 ≤ (∑ k ∈ Finset.Ico M M, if B k then F k 1 else 0) :=
          Finset.sum_nonneg (fun k _ => hifnn k)
        have s2 : 0 ≤ (∑ k ∈ Finset.Ico M M, if M ≤ k + N then F k 1 else 0) :=
          Finset.sum_nonneg (fun k _ => hifnn2 k)
        simp only [Nat.cast_zero, zero_mul, zero_add]
        exact add_nonneg s1 s2
      · have hpos : 0 < r := Nat.pos_of_ne_zero r0
        have hjM : j < M := by omega
        have hjr : j + r = M := by omega
        by_cases hBj : B j
        · -- bad position: peel off one step, charge to first sum
          have hr1 : r = 1 + (r - 1) := by omega
          have step1 : F j r ≤ F j 1 + F (j + 1) (r - 1) := by
            conv_lhs => rw [hr1]
            exact hFsub j 1 (r - 1)
          have ihr := ih (r - 1) (by omega) (by omega) (j + 1) (by omega)
          have e1 := hsplit (fun k => if B k then F k 1 else 0) j M hjM
          have e2 := hsplit (fun k => if M ≤ k + N then F k 1 else 0) j M hjM
          rw [ite_eq_left hBj] at e1
          have ht : 0 ≤ (if M ≤ j + N then F j 1 else 0) := hifnn2 j
          have hcast : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast Nat.sub_le r 1
          have hmul : ((r - 1 : ℕ) : ℝ) * c ≤ (r : ℝ) * c :=
            mul_le_mul_of_nonneg_right hcast hc
          linarith
        · -- good position: take the whole block given by hgood
          obtain ⟨n, h1n, hnN, hFn⟩ := hgood j hBj
          by_cases hleM : j + n ≤ M
          · have hnr : n ≤ r := by omega
            have hr2 : r = n + (r - n) := by omega
            have step : F j r ≤ F j n + F (j + n) (r - n) := by
              conv_lhs => rw [hr2]
              exact hFsub j n (r - n)
            have ihr := ih (r - n) (by omega) (by omega) (j + n) (by omega)
            have hsub12 : Finset.Ico (j + n) M ⊆ Finset.Ico j M :=
              Finset.Ico_subset_Ico (by omega) le_rfl
            have s1le : (∑ k ∈ Finset.Ico (j + n) M, if B k then F k 1 else 0) ≤
                (∑ k ∈ Finset.Ico j M, if B k then F k 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub12 (fun i _ _ => hifnn i)
            have s2le : (∑ k ∈ Finset.Ico (j + n) M, if M ≤ k + N then F k 1 else 0) ≤
                (∑ k ∈ Finset.Ico j M, if M ≤ k + N then F k 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub12 (fun i _ _ => hifnn2 i)
            have hcast2 : ((r - n : ℕ) : ℝ) + (n : ℝ) = (r : ℝ) := by
              exact_mod_cast Nat.sub_add_cancel hnr
            have hmul2 : ((r - n : ℕ) : ℝ) * c + (n : ℝ) * c = (r : ℝ) * c := by
              rw [← add_mul, hcast2]
            linarith
          · -- block overruns M: peel off one step, charge to tail sum
            have htail : M ≤ j + N := by omega
            have hr3 : r = 1 + (r - 1) := by omega
            have step : F j r ≤ F j 1 + F (j + 1) (r - 1) := by
              conv_lhs => rw [hr3]
              exact hFsub j 1 (r - 1)
            have ihr := ih (r - 1) (by omega) (by omega) (j + 1) (by omega)
            have e1 := hsplit (fun k => if B k then F k 1 else 0) j M hjM
            have e2 := hsplit (fun k => if M ≤ k + N then F k 1 else 0) j M hjM
            rw [ite_eq_right hBj] at e1
            rw [ite_eq_left htail] at e2
            have hcast : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
              exact_mod_cast Nat.sub_le r 1
            have hmul : ((r - 1 : ℕ) : ℝ) * c ≤ (r : ℝ) * c :=
              mul_le_mul_of_nonneg_right hcast hc
            linarith
  have hfin := key M le_rfl 0 (Nat.sub_self M)
  rw [← Finset.range_eq_Ico] at hfin
  simpa using hfin

-- The maximal integral inequality and invariant divergence sets are shared with Birkhoff.

/-- N3a: integral of `φ - c` over the shared `DickSet` is nonnegative. -/
private theorem setIntegral_kingmanDick_sub_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hφi : Integrable φ μ) (c : ℝ) :
    0 ≤ ∫ x in BirkhoffPointwise.DickSet T φ c, (φ x - c) ∂μ := by
  have hDmeas : MeasurableSet (BirkhoffPointwise.DickSet T φ c) :=
    BirkhoffPointwise.dick_measurable hT hφ c
  have hiter : ∀ (k : ℕ) (x : α),
      (T^[k] x ∈ BirkhoffPointwise.DickSet T φ c) ↔ (x ∈ BirkhoffPointwise.DickSet T φ c) :=
    fun k x => Set.ext_iff.mp
      (Function.IsFixedPt.preimage_iterate BirkhoffPointwise.dick_inv k) x
  set hfun : α → ℝ := (BirkhoffPointwise.DickSet T φ c).indicator (fun y => φ y - c) with hfundef
  have hm_h : Measurable hfun := Measurable.indicator (hφ.sub measurable_const) hDmeas
  have hi_h : Integrable hfun μ :=
    Integrable.indicator (hφi.sub (integrable_const c)) hDmeas
  have hfundef' : ∀ y : α,
      hfun y = (BirkhoffPointwise.DickSet T φ c).indicator (fun y => φ y - c) y :=
    fun y => rfl
  have hsum_in : ∀ x : α, x ∈ BirkhoffPointwise.DickSet T φ c → ∀ n : ℕ,
      birkhoffSum T hfun n x = birkhoffSum T φ n x - n * c :=
    fun x hx n => BirkhoffPointwise.dick_sum_in _ hiter hfun hfundef' x hx n
  have hsum_out : ∀ x : α, x ∉ BirkhoffPointwise.DickSet T φ c → ∀ n : ℕ,
      birkhoffSum T hfun n x = 0 :=
    fun x hx n => BirkhoffPointwise.dick_sum_out _ hiter hfun hfundef' x hx n
  have hE : {x | ∃ n, 0 < birkhoffSum T hfun n x} = BirkhoffPointwise.DickSet T φ c := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := hx
      by_contra hxD
      rw [hsum_out x hxD n] at hn
      exact lt_irrefl 0 hn
    · intro hx
      have hxD : x ∈ BirkhoffPointwise.DickSet T φ c := hx
      rw [BirkhoffPointwise.dick_mem] at hx
      obtain ⟨q, hcq, hfreq⟩ := hx
      obtain ⟨n, hn1, hnq⟩ := hfreq 1
      refine ⟨n, ?_⟩
      rw [hsum_in x hxD n]
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have h0n : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
        exact_mod_cast h0n
      have hqc : (0 : ℝ) < (q : ℝ) - c := sub_pos.mpr hcq
      have hmul : (0 : ℝ) < (n : ℝ) * ((q : ℝ) - c) := mul_pos hnpos hqc
      have heq : (n : ℝ) * (q : ℝ) - (n : ℝ) * c = (n : ℝ) * ((q : ℝ) - c) := by ring
      linarith
  have hmax := BirkhoffPointwise.maximal_ergodic hT hm_h hi_h
  rw [hE] at hmax
  have hcongr : ∫ x in BirkhoffPointwise.DickSet T φ c, hfun x ∂μ
      = ∫ x in BirkhoffPointwise.DickSet T φ c, (φ x - c) ∂μ := by
    apply setIntegral_congr_ae hDmeas
    filter_upwards with x
    intro hx
    exact Set.indicator_of_mem hx _
  rw [hcongr] at hmax
  exact hmax

/-- N3b: weak maximal inequality for nonnegative `φ`. -/
theorem measure_kingmanDick_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hφi : Integrable φ μ) (hφnn : ∀ x, 0 ≤ φ x)
    {c : ℝ} (hc : 0 < c) :
    μ (BirkhoffPointwise.DickSet T φ c) ≤ ENNReal.ofReal ((∫ x, φ x ∂μ) / c) := by
  have h3a := setIntegral_kingmanDick_sub_nonneg hT hφ hφi c
  have hconst : (∫ x in BirkhoffPointwise.DickSet T φ c, c ∂μ)
      = c * (μ (BirkhoffPointwise.DickSet T φ c)).toReal := by
    rw [setIntegral_const, Measure.real_def, smul_eq_mul]
    exact mul_comm _ _
  have hsub : (∫ x in BirkhoffPointwise.DickSet T φ c, (φ x - c) ∂μ)
      = (∫ x in BirkhoffPointwise.DickSet T φ c, φ x ∂μ)
        - c * (μ (BirkhoffPointwise.DickSet T φ c)).toReal := by
    have h1 : (∫ x in BirkhoffPointwise.DickSet T φ c, (φ x - c) ∂μ)
        = (∫ x in BirkhoffPointwise.DickSet T φ c, φ x ∂μ)
          - ∫ x in BirkhoffPointwise.DickSet T φ c, c ∂μ :=
      integral_sub (μ := μ.restrict (BirkhoffPointwise.DickSet T φ c))
        hφi.integrableOn (integrable_const c).integrableOn
    rw [hconst] at h1
    exact h1
  have hle1 : c * (μ (BirkhoffPointwise.DickSet T φ c)).toReal
      ≤ ∫ x in BirkhoffPointwise.DickSet T φ c, φ x ∂μ := by
    linarith [h3a, hsub]
  have hle2 : (∫ x in BirkhoffPointwise.DickSet T φ c, φ x ∂μ) ≤ ∫ x, φ x ∂μ :=
    setIntegral_le_integral hφi (Filter.Eventually.of_forall hφnn)
  have hle : c * (μ (BirkhoffPointwise.DickSet T φ c)).toReal ≤ ∫ x, φ x ∂μ :=
    le_trans hle1 hle2
  have hdiv : (μ (BirkhoffPointwise.DickSet T φ c)).toReal ≤ (∫ x, φ x ∂μ) / c := by
    rw [le_div_iff₀ hc]
    linarith [hle]
  calc μ (BirkhoffPointwise.DickSet T φ c)
      = ENNReal.ofReal ((μ (BirkhoffPointwise.DickSet T φ c)).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal ((∫ x, φ x ∂μ) / c) := ENNReal.ofReal_le_ofReal hdiv


end D5.S3.Analytic.Probability.KingmanEstimates
