/- GID: D5/S3/Analytic/Probability/KingmanPointwise
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/KingmanPointwise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative subadditive cocycles converge to an integrable invariant limit. -/

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

import D5.S3.Analytic.Probability.KingmanEstimates

/-! Kingman convergence with an integrable invariant limit on finite measure spaces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Probability.KingmanPointwise

open MeasureTheory Filter Topology

open KingmanEstimates

/-- N5a: subadditive cocycle bounded by Birkhoff sums of `f 1` (everywhere version). -/
private theorem le_birkhoffSum_one
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∀ n x, f n x ≤ birkhoffSum T (f 1) n x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [hf_zero x]
    have h0 := congrFun (birkhoffSum_zero T (f 1)) x
    simp only [Pi.zero_apply] at h0
    rw [h0]
  | succ n ih =>
    intro x
    have hsub := hf_subadd 1 n x
    rw [Function.iterate_one] at hsub
    have hshift : f (n + 1) x = f (1 + n) x := by rw [Nat.add_comm]
    rw [hshift]
    have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
    simp only [Pi.add_apply, Function.comp_apply] at hbs
    rw [hbs]
    exact le_trans hsub (add_le_add_right (ih (T x)) _)

/-- N5b: integral bound via Birkhoff sums (everywhere version). -/
private theorem integral_le_mul_integral_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_int : ∀ n, Integrable (f n) μ)
    (hle : ∀ n x, f n x ≤ birkhoffSum T (f 1) n x) :
    ∀ n, ∫ x, f n x ∂μ ≤ n * ∫ x, f 1 x ∂μ := by
  have hint : ∀ n, Integrable (fun x => birkhoffSum T (f 1) n x) μ := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
      have hcomp : Integrable (fun x => birkhoffSum T (f 1) n (T x)) μ :=
        hT.integrable_comp_of_integrable ih
      have ef : (fun x => birkhoffSum T (f 1) (n + 1) x) =
          fun x => (f 1 x + birkhoffSum T (f 1) n (T x)) := by
        funext x
        have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
        simp only [Pi.add_apply, Function.comp_apply] at hbs
        exact hbs
      rw [ef]
      exact (hf_int 1).add hcomp
  have hident : ∀ n, ∫ x, birkhoffSum T (f 1) n x ∂μ = n * ∫ x, f 1 x ∂μ := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
      have hcomp : Integrable (fun x => birkhoffSum T (f 1) n (T x)) μ :=
        hT.integrable_comp_of_integrable (hint n)
      have eadd : ∫ x, (f 1 x + birkhoffSum T (f 1) n (T x)) ∂μ =
          (∫ x, f 1 x ∂μ) + ∫ x, birkhoffSum T (f 1) n (T x) ∂μ :=
        integral_add (hf_int 1) hcomp
      have emap : (∫ x, birkhoffSum T (f 1) n (T x) ∂μ) =
          (∫ x, birkhoffSum T (f 1) n x ∂μ) := by
        have haes : AEStronglyMeasurable (fun x => birkhoffSum T (f 1) n x)
            (Measure.map T μ) := by
          rw [hT.map_eq]
          exact (hint n).1
        have h1 : (∫ y, birkhoffSum T (f 1) n y ∂(Measure.map T μ)) =
            (∫ x, birkhoffSum T (f 1) n (T x) ∂μ) :=
          integral_map hT.measurable.aemeasurable haes
        rw [← h1, hT.map_eq]
      have ef : (fun x => birkhoffSum T (f 1) (n + 1) x) =
          fun x => (f 1 x + birkhoffSum T (f 1) n (T x)) := by
        funext x
        have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
        simp only [Pi.add_apply, Function.comp_apply] at hbs
        exact hbs
      rw [← ef] at eadd
      rw [eadd, emap, ih]
      push_cast
      ring
  intro n
  calc ∫ x, f n x ∂μ ≤ ∫ x, birkhoffSum T (f 1) n x ∂μ :=
        integral_mono (hf_int n) (hint n) (hle n)
    _ = ↑n * ∫ x, f 1 x ∂μ := hident n


/-- N4: reduce a.e. hypotheses to everywhere hypotheses via an invariant full-measure set. -/
private theorem kingman_reduce_everywhere
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hf_zero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hf_subadd : ∀ m n, ∀ᵐ x ∂μ, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∃ f' : ℕ → α → ℝ, (∀ n, Measurable (f' n)) ∧ (∀ n, f' n =ᵐ[μ] f n) ∧
      (∀ n x, 0 ≤ f' n x) ∧ (∀ x, f' 0 x = 0) ∧
      (∀ m n x, f' (m + n) x ≤ f' m x + f' n ((T^[m]) x)) := by
  have hTm : ∀ k, Measurable (T^[k]) := fun k => (hT.measurable.iterate k)
  set G1 : Set α :=
    (⋂ n, (f n) ⁻¹' (Set.Ici 0)) ∩ ((f 0) ⁻¹' {0}) ∩
      (⋂ m, ⋂ n, {x | f (m + n) x ≤ f m x + f n ((T^[m]) x)}) with hG1
  have hG1meas : MeasurableSet G1 := by
    rw [hG1]
    refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact MeasurableSet.iInter (fun n => (hf_meas n) measurableSet_Ici)
    · exact (hf_meas 0) (measurableSet_singleton 0)
    · exact MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun n =>
        measurableSet_le (hf_meas (m + n)) ((hf_meas m).add ((hf_meas n).comp (hTm m)))))
  have hA : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x := (MeasureTheory.ae_all_iff).mpr hf_nonneg
  have hC1 : ∀ m, ∀ᵐ x ∂μ, ∀ n, f (m + n) x ≤ f m x + f n ((T^[m]) x) := by
    intro m
    exact (MeasureTheory.ae_all_iff).mpr (hf_subadd m)
  have hC : ∀ᵐ x ∂μ, ∀ m n, f (m + n) x ≤ f m x + f n ((T^[m]) x) :=
    (MeasureTheory.ae_all_iff).mpr hC1
  have hG1ae : ∀ᵐ x ∂μ, x ∈ G1 := by
    filter_upwards [hA, hf_zero, hC] with x hxA hx0 hxC
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Set.mem_iInter]
      intro n
      exact hxA n
    · exact hx0
    · rw [Set.mem_iInter]
      intro m
      rw [Set.mem_iInter]
      intro n
      exact hxC m n
  set G0 : Set α := ⋂ k, (T^[k]) ⁻¹' G1 with hG0
  have hG0meas : MeasurableSet G0 := by
    rw [hG0]
    exact MeasurableSet.iInter (fun k => (hTm k) hG1meas)
  have hG1null : μ G1ᶜ = 0 := MeasureTheory.ae_iff.mp hG1ae
  have hpre : ∀ k, μ ((T^[k]) ⁻¹' G1)ᶜ = 0 := by
    intro k
    have h1 : ((T^[k]) ⁻¹' G1)ᶜ = (T^[k]) ⁻¹' (G1ᶜ) := (Set.preimage_compl).symm
    rw [h1, (hT.iterate k).measure_preimage (hG1meas.compl.nullMeasurableSet), hG1null]
  have hG0ae : ∀ᵐ x ∂μ, x ∈ G0 := by
    have h2 : ∀ k, ∀ᵐ x ∂μ, x ∈ (T^[k]) ⁻¹' G1 := by
      intro k
      exact MeasureTheory.ae_iff.mpr (hpre k)
    have h3 : ∀ᵐ x ∂μ, ∀ k, x ∈ (T^[k]) ⁻¹' G1 := (MeasureTheory.ae_all_iff).mpr h2
    filter_upwards [h3] with x hx
    rw [hG0, Set.mem_iInter]
    exact hx
  have hfwd : ∀ m x, x ∈ G0 → (T^[m]) x ∈ G0 := by
    intro m x hx
    rw [hG0, Set.mem_iInter] at hx ⊢
    intro k
    have hk := hx (k + m)
    rw [Set.mem_preimage] at hk ⊢
    have heq : (T^[k + m]) x = (T^[k]) ((T^[m]) x) := Function.iterate_add_apply T k m x
    rw [← heq]
    exact hk
  have hmemG1 : ∀ x, x ∈ G0 → x ∈ G1 := by
    intro x hx
    rw [hG0, Set.mem_iInter] at hx
    have h0 := hx 0
    rw [Set.mem_preimage, Function.iterate_zero, id_eq] at h0
    exact h0
  have hG1A : ∀ x, x ∈ G1 → ∀ n, 0 ≤ f n x := by
    intro x hx n
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨⟨hA', -⟩, -⟩ := hx
    exact Set.mem_iInter.mp hA' n
  have hG1B : ∀ x, x ∈ G1 → f 0 x = 0 := by
    intro x hx
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨⟨-, hB⟩, -⟩ := hx
    exact hB
  have hG1C : ∀ x, x ∈ G1 → ∀ m n, f (m + n) x ≤ f m x + f n ((T^[m]) x) := by
    intro x hx m n
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨-, hC'⟩ := hx
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hC' m) n
  refine ⟨fun n => G0.indicator (f n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hf_meas n).indicator hG0meas
  · intro n
    filter_upwards [hG0ae] with x hx
    exact Set.indicator_of_mem hx (f n)
  · intro n x
    change 0 ≤ G0.indicator (f n) x
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx]
      exact hG1A x (hmemG1 x hx) n
    · rw [Set.indicator_of_notMem hx]
  · intro x
    change G0.indicator (f 0) x = 0
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx]
      exact hG1B x (hmemG1 x hx)
    · rw [Set.indicator_of_notMem hx]
  · intro m n x
    change G0.indicator (f (m + n)) x ≤ G0.indicator (f m) x + G0.indicator (f n) ((T^[m]) x)
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_mem (hfwd m x hx)]
      exact hG1C x (hmemG1 x hx) m n
    · rw [Set.indicator_of_notMem hx]
      have h1 : 0 ≤ G0.indicator (f m) x := by
        rw [Set.indicator_of_notMem hx]
      have h2 : 0 ≤ G0.indicator (f n) ((T^[m]) x) := by
        by_cases hTx : (T^[m]) x ∈ G0
        · rw [Set.indicator_of_mem hTx]
          exact hG1A _ (hmemG1 _ hTx) n
        · rw [Set.indicator_of_notMem hTx]
      exact add_nonneg h1 h2

/-- N8: liminf rate function (ENNReal to avoid boundedness side conditions). -/
private noncomputable def kingmanLiminf {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (x : α) : ENNReal :=
  Filter.liminf (fun n : ℕ => ENNReal.ofReal (f n x / (n : ℝ))) atTop

/-- N8a: measurability of the liminf rate. -/
private theorem kingmanLiminf_measurable
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (hf_meas : ∀ n, Measurable (f n)) :
    Measurable (kingmanLiminf f) := by
  unfold kingmanLiminf
  apply Measurable.liminf
  intro n
  exact ((hf_meas n).div measurable_const).ennreal_ofReal

/-- N8bc: Fatou bound and a.e. finiteness of the liminf rate. -/
private theorem kingmanLiminf_lintegral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hN5 : ∀ n, ∫ x, f n x ∂μ ≤ (n : ℝ) * ∫ x, f 1 x ∂μ) :
    ∫⁻ x, kingmanLiminf f x ∂μ ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) ∧
      ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤ := by
  have hmeas_seq : ∀ n, Measurable (fun x => ENNReal.ofReal (f n x / (n : ℝ))) :=
    fun n => ((hf_meas n).div measurable_const).ennreal_ofReal
  have hfat : ∫⁻ x, kingmanLiminf f x ∂μ
      ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ) atTop := by
    have := lintegral_liminf_le hmeas_seq (μ := μ) (u := (atTop : Filter ℕ))
    simpa only [kingmanLiminf] using this
  have hper : ∀ n, (∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ)
      ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hz : (fun x => ENNReal.ofReal (f 0 x / ((0 : ℕ) : ℝ))) = fun _ => 0 := by
        funext x
        rw [hf_zero x]
        simp
      rw [hz]
      simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
      have hint : Integrable (fun x => f n x / (n : ℝ)) μ := (hf_int n).div_const _
      have hnnm : 0 ≤ᵐ[μ] (fun x => f n x / (n : ℝ)) :=
        Filter.Eventually.of_forall
          (fun x => div_nonneg (hf_nn n x) (Nat.cast_nonneg _))
      have hof : (∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ)
          = ENNReal.ofReal (∫ x, (f n x / (n : ℝ)) ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint hnnm]
      have hval : (∫ x, (f n x / (n : ℝ)) ∂μ) = ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ := by
        have heq : (fun x => f n x / (n : ℝ)) = (fun x => ((n : ℝ))⁻¹ * f n x) := by
          funext x
          rw [div_eq_mul_inv, mul_comm]
        rw [heq, integral_const_mul]
      have hle : ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ ≤ ∫ x, f 1 x ∂μ := by
        have h1 := hN5 n
        have h2 : ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ ≤ ((n : ℝ))⁻¹ * ((n : ℝ) * ∫ x, f 1 x ∂μ) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hnn)
        have h3 : ((n : ℝ))⁻¹ * ((n : ℝ) * ∫ x, f 1 x ∂μ) = ∫ x, f 1 x ∂μ := by
          field_simp
        rw [h3] at h2
        exact h2
      rw [hof, hval]
      exact ENNReal.ofReal_le_ofReal hle
  have hlim : Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ) atTop
      ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) :=
    Filter.liminf_le_of_frequently_le (Frequently.of_forall hper)
      ⟨⊥, Filter.Eventually.of_forall fun _ => bot_le⟩
  refine ⟨le_trans hfat hlim, ?_⟩
  apply ae_lt_top (kingmanLiminf_measurable f hf_meas)
  exact ne_of_lt (lt_of_le_of_lt (le_trans hfat hlim) ENNReal.ofReal_lt_top)

/-- N8d: the liminf rate is sub-invariant. -/
private theorem kingmanLiminf_le_comp
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∀ x, kingmanLiminf f x ≤ kingmanLiminf f (T x) := by
  intro x
  have hpt : ∀ n : ℕ, ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))
      ≤ ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
        + ENNReal.ofReal (f n (T x) / (n : ℝ)) := by
    intro n
    have hreal : f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
        ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ) := by
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hf_zero (T x)]
        simp
      · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hN1 : (0 : ℝ) < (((n + 1 : ℕ)) : ℝ) := by
          exact_mod_cast Nat.succ_pos n
        have hsub := hf_subadd 1 n x
        rw [Function.iterate_one, Nat.add_comm (1 : ℕ) n] at hsub
        have hleN : (n : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hdiv : f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
            ≤ (f 1 x + f n (T x)) / (((n + 1 : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_right hsub (le_of_lt hN1)
        have h2 : f n (T x) / (((n + 1 : ℕ)) : ℝ) ≤ f n (T x) / (n : ℝ) :=
          div_le_div_of_nonneg_left (hf_nn n (T x)) hN hleN
        calc f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
            ≤ (f 1 x + f n (T x)) / (((n + 1 : ℕ)) : ℝ) := hdiv
          _ = f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (((n + 1 : ℕ)) : ℝ) :=
              add_div _ _ _
          _ ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ) :=
              add_le_add_right h2 _
    have hb : 0 ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) :=
      div_nonneg (hf_nn 1 x) (Nat.cast_nonneg _)
    have hd : 0 ≤ f n (T x) / (n : ℝ) :=
      div_nonneg (hf_nn n (T x)) (Nat.cast_nonneg _)
    calc ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))
        ≤ ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
          + ENNReal.ofReal (f n (T x) / (n : ℝ)) := ENNReal.ofReal_add hb hd
  have hzero : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))) atTop (nhds 0) := by
    have hreal0 : Filter.Tendsto (fun n : ℕ => f 1 x / (((n + 1 : ℕ)) : ℝ)) atTop
        (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Filter.Tendsto (fun n : ℕ => f 1 x * ((1 : ℝ) / ((n : ℝ) + 1))) atTop
          (nhds 0) := by
        have h := Filter.Tendsto.const_mul (f 1 x) h1
        rw [mul_zero] at h
        exact h
      have heq : (fun n : ℕ => f 1 x / (((n + 1 : ℕ)) : ℝ))
          = fun n : ℕ => f 1 x * ((1 : ℝ) / ((n : ℝ) + 1)) := by
        funext n
        have hc : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [hc, mul_one_div]
      rw [heq]
      exact h2
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hreal0
    rw [ENNReal.ofReal_zero] at hcont
    exact hcont
  have hLHS : kingmanLiminf f x
      = Filter.liminf
        (fun n : ℕ => ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))) atTop := by
    have h := (Filter.liminf_nat_add
      (fun n : ℕ => ENNReal.ofReal (f n x / (n : ℝ))) 1).symm
    unfold kingmanLiminf
    exact h
  have hRHS : Filter.liminf (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
        + ENNReal.ofReal (f n (T x) / (n : ℝ))) atTop
      = kingmanLiminf f (T x) := by
    have hz := ENNReal.liminf_add_of_left_tendsto_zero hzero
      (fun n : ℕ => ENNReal.ofReal (f n (T x) / (n : ℝ)))
    unfold kingmanLiminf
    exact hz
  calc kingmanLiminf f x
      = Filter.liminf
        (fun n : ℕ => ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))) atTop := hLHS
    _ ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
          + ENNReal.ofReal (f n (T x) / (n : ℝ))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hpt)
    _ = kingmanLiminf f (T x) := hRHS


/-- N8f: the liminf rate is constant along orbits a.e. -/
private theorem kingmanLiminf_ae_iterate_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (he : ∀ᵐ x ∂μ, kingmanLiminf f (T x) = kingmanLiminf f x) :
    ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x := by
  have hq : ∀ k, QuasiMeasurePreserving (T^[k]) μ μ :=
    fun k => (hT.iterate k).quasiMeasurePreserving
  have hall : ∀ᵐ x ∂μ, ∀ k,
      kingmanLiminf f (T ((T^[k]) x)) = kingmanLiminf f ((T^[k]) x) :=
    MeasureTheory.ae_all_iff.mpr (fun k => MeasureTheory.QuasiMeasurePreserving.ae (hq k) he)
  filter_upwards [hall] with x hx
  intro k
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih =>
    have h1 := hx k
    change kingmanLiminf f ((T^[k.succ]) x) = kingmanLiminf f x
    rw [Function.iterate_succ_apply', h1, ih]

/-- N10/N11: bad set where averages exceed `ℓ + ε` on all of `Icc 1 N`. -/
private def kingmanBadSet {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) : Set α :=
  {y | ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y}

/-- Measurability of the bad sets. -/
private theorem kingmanBadSet_measurable
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (hf_meas : ∀ n, Measurable (f n)) (ε : ℝ) (N : ℕ) :
    MeasurableSet (kingmanBadSet f ε N) := by
  have hℓ : Measurable (fun y => (kingmanLiminf f y).toReal) :=
    (kingmanLiminf_measurable f hf_meas).ennreal_toReal
  unfold kingmanBadSet
  have heq : {y | ∀ n : ℕ, 1 ≤ n → n ≤ N →
        (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y}
      = ⋂ (n : ℕ) (_ : 1 ≤ n) (_ : n ≤ N),
        {y | (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_const.mul (hℓ.add measurable_const)) (hf_meas n)

/-- N10: Steele's pointwise bound from the greedy decomposition. -/
private theorem kingman_pointwise_bound
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x))
    (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (x : α)
    (hinv : ∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal) :
    ∀ M : ℕ, f M x ≤ (M : ℝ) * ((kingmanLiminf f x).toReal + ε)
      + birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) M x
      + ∑ k ∈ Finset.range M, (if M ≤ k + N then f 1 ((T^[k]) x) else 0) := by
  have hc : 0 ≤ (kingmanLiminf f x).toReal + ε :=
    add_nonneg ENNReal.toReal_nonneg hε
  classical
  have hFsub : ∀ k m n, (fun k n => f n ((T^[k]) x)) k (m + n)
      ≤ (fun k n => f n ((T^[k]) x)) k m
        + (fun k n => f n ((T^[k]) x)) (k + m) n := by
    intro k m n
    have h := hf_subadd m n ((T^[k]) x)
    have e : (T^[m]) ((T^[k]) x) = (T^[k + m]) x := by
      rw [← Function.iterate_add_apply T m k x, Nat.add_comm m k]
    rw [e] at h
    exact h
  have hgood : ∀ k, ¬ (fun k => (T^[k]) x ∈ kingmanBadSet f ε N) k →
      ∃ n, 1 ≤ n ∧ n ≤ N ∧ (fun k n => f n ((T^[k]) x)) k n
        ≤ (n : ℝ) * ((kingmanLiminf f x).toReal + ε) := by
    intro k hk
    simp only [kingmanBadSet, Set.mem_ofPred_eq] at hk
    rw [not_forall] at hk
    obtain ⟨n, hn⟩ := hk
    rw [not_imp, not_imp] at hn
    obtain ⟨h1n, hnN, hcon⟩ := hn
    refine ⟨n, h1n, hnN, ?_⟩
    have hle : f n ((T^[k]) x)
        ≤ (n : ℝ) * ((kingmanLiminf f ((T^[k]) x)).toReal + ε) :=
      not_lt.mp hcon
    rw [hinv k] at hle
    exact hle
  have hmain := greedy_block_bound (fun k n => f n ((T^[k]) x))
    (fun k n => hf_nn n _) (fun k => hf_zero _) hFsub
    (fun k => (T^[k]) x ∈ kingmanBadSet f ε N)
    ((kingmanLiminf f x).toReal + ε) hc N hgood
  intro M
  have hM := hmain M
  have e0 : f M ((T^[0]) x) = f M x := by rw [Function.iterate_zero_apply]
  have hsum1 : (∑ k ∈ Finset.range M,
        (if (T^[k]) x ∈ kingmanBadSet f ε N then f 1 ((T^[k]) x) else 0))
      = birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) M x := by
    unfold birkhoffSum
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (T^[k]) x ∈ kingmanBadSet f ε N
    · rw [ite_eq_left hk, Set.indicator_of_mem hk]
    · rw [ite_eq_right hk, Set.indicator_of_notMem hk]
  rw [← e0, ← hsum1]
  exact hM

/-- N11: the bad sets shrink and their `f 1`-integrals tend to zero. -/
private theorem tendsto_setIntegral_kingmanBad
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (ε : ℝ) (hε : 0 < ε)
    (hfin : ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤) :
    Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop (nhds 0) := by
  have hAmeas : ∀ N, MeasurableSet (kingmanBadSet f ε N) :=
    fun N => kingmanBadSet_measurable f hf_meas ε N
  have hanti : Antitone (kingmanBadSet f ε) := by
    intro a b hab y hy
    simp only [kingmanBadSet, Set.mem_ofPred_eq] at hy ⊢
    intro n h1n hnN
    exact hy n h1n (le_trans hnN hab)
  have hsub : (⋂ N, kingmanBadSet f ε N) ⊆ {x | kingmanLiminf f x = ⊤} := by
    intro y hy
    simp only [Set.mem_iInter, kingmanBadSet, Set.mem_ofPred_eq] at hy
    by_contra hcon
    simp only [Set.mem_ofPred_eq] at hcon
    have hlt : kingmanLiminf f y < ⊤ := lt_of_le_of_ne le_top hcon
    have hLy : kingmanLiminf f y = ENNReal.ofReal ((kingmanLiminf f y).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hlt)).symm
    have hpos : (0 : ℝ) < (kingmanLiminf f y).toReal + ε :=
      add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε
    have hlt2 : kingmanLiminf f y
        < ENNReal.ofReal ((kingmanLiminf f y).toReal + ε) := by
      conv_lhs => rw [hLy]
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith [hε])
    unfold kingmanLiminf at hlt2
    have hfreq : ∃ᶠ n in atTop,
        ENNReal.ofReal (f n y / (n : ℝ))
          < ENNReal.ofReal ((kingmanLiminf f y).toReal + ε) :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt2
    obtain ⟨n, hn_lt, hn1⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    have hreal : f n y / (n : ℝ) < (kingmanLiminf f y).toReal + ε :=
      (ENNReal.ofReal_lt_ofReal_iff'.mp hn_lt).1
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfin' : f n y < (n : ℝ) * ((kingmanLiminf f y).toReal + ε) := by
      have h := (div_lt_iff₀ hnR).mp hreal
      rwa [mul_comm] at h
    have hmem := hy n n hn1 (le_refl n)
    exact lt_irrefl _ (lt_trans hfin' hmem)
  have htop0 : μ {x | kingmanLiminf f x = ⊤} = 0 := by
    have hcompl : {x | kingmanLiminf f x = ⊤} = {x | kingmanLiminf f x < ⊤}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt, top_le_iff]
    have hae : ∀ᵐ x ∂μ, x ∈ {x | kingmanLiminf f x < ⊤} := hfin
    have h0 : μ ({x | kingmanLiminf f x < ⊤}ᶜ) = 0 := MeasureTheory.ae_iff.mp hae
    rwa [← hcompl] at h0
  have hinter0 : μ (⋂ N, kingmanBadSet f ε N) = 0 :=
    le_antisymm (le_trans (measure_mono hsub) (le_of_eq htop0)) zero_le
  have hlim : Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop
      (nhds (∫ y in ⋂ N, kingmanBadSet f ε N, f 1 y ∂μ)) :=
    tendsto_setIntegral_of_antitone hAmeas hanti ⟨0, (hf_int 1).integrableOn⟩
  rw [setIntegral_measure_zero _ hinter0] at hlim
  exact hlim

/-- N12: upper bound `f M x / M ≤ ℓ x + 4ε` eventually a.e. -/
private theorem kingman_upper
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x))
    (hLinv : ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x)
    (hfin : ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ x ∂μ, ∀ᶠ M in atTop,
      f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε := by
  intro ε hε
  have hN6 := ae_tendsto_comp_iterate_div_nat hT (hf_meas 1) (hf_int 1) (hf_nn 1)
  have hOmega : ∀ᵐ x ∂μ, (∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal)
      ∧ Tendsto (fun m : ℕ => f 1 ((T^[m]) x) / (m : ℝ)) atTop (nhds 0) := by
    filter_upwards [hLinv, hN6] with x hx1 hx2
    exact ⟨fun k => by rw [hx1 k], hx2⟩
  set Bad : Set α := {x | (∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal)
    ∧ Tendsto (fun m : ℕ => f 1 ((T^[m]) x) / (m : ℝ)) atTop (nhds 0)
    ∧ ¬ ∀ᶠ M in atTop, f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε}
    with hBad
  have hBadsub : ∀ N : ℕ, 1 ≤ N →
      Bad ⊆ BirkhoffPointwise.DickSet T ((kingmanBadSet f ε N).indicator (f 1)) ε := by
    intro N hN x hx
    simp only [hBad, Set.mem_ofPred_eq] at hx
    obtain ⟨hinv, hlim0, hbad⟩ := hx
    by_contra hxD
    rw [BirkhoffPointwise.dick_mem] at hxD
    obtain ⟨q, hεq, hq2⟩ := exists_rat_btwn (show ε < 2 * ε by linarith)
    have hnotfreq : ¬ ∀ N' : ℕ, ∃ n : ℕ, N' ≤ n ∧ (n : ℝ) * (q : ℝ)
        < birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x := by
      intro hall
      exact hxD ⟨q, hεq, hall⟩
    rw [not_forall] at hnotfreq
    obtain ⟨N', hN'⟩ := hnotfreq
    have hSbound : ∀ n : ℕ, N' ≤ n →
        birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (2 * ε) := by
      intro n hn
      have hle : birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (q : ℝ) := by
        by_contra hcon
        rw [not_le] at hcon
        exact hN' ⟨n, hn, hcon⟩
      calc birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (q : ℝ) := hle
        _ ≤ (n : ℝ) * (2 * ε) :=
            mul_le_mul_of_nonneg_left (le_of_lt hq2) (Nat.cast_nonneg _)
    have hδ : (0 : ℝ) < ε / (N : ℝ) := by
      have hNR : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
      exact div_pos hε hNR
    have hev1 : ∀ᶠ m in atTop, f 1 ((T^[m]) x) / (m : ℝ) < ε / (N : ℝ) :=
      hlim0.eventually (gt_mem_nhds hδ)
    have hev2 : ∀ᶠ m in atTop,
        (f 1 ((T^[m]) x) / (m : ℝ) < ε / (N : ℝ)) ∧ 1 ≤ m :=
      hev1.and (eventually_ge_atTop 1)
    obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hev2
    have htail : ∀ᶠ M in atTop, (∑ k ∈ Finset.range M,
        (if M ≤ k + N then f 1 ((T^[k]) x) else 0)) ≤ ε * (M : ℝ) := by
      filter_upwards [eventually_ge_atTop (K₀ + N)] with M hM
      have hIco_sub : Finset.Ico (M - N) M ⊆ Finset.range M := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_range]
        omega
      have hvanish : ∀ k ∈ Finset.range M, k ∉ Finset.Ico (M - N) M →
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0) = 0 := by
        intro k hk_range hk_nmem
        rw [Finset.mem_range] at hk_range
        rw [Finset.mem_Ico] at hk_nmem
        have hneg : ¬ M ≤ k + N := by omega
        rw [ite_eq_right hneg]
      have hsub_eq := Finset.sum_subset hIco_sub hvanish
      have hif_eq : (∑ k ∈ Finset.Ico (M - N) M,
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0))
          = ∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        have hMkN : M ≤ k + N := by omega
        rw [ite_eq_left hMkN]
      have hsum_eq : (∑ k ∈ Finset.range M,
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0))
          = ∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x) :=
        hsub_eq.symm.trans hif_eq
      rw [hsum_eq]
      have hterm : ∀ k ∈ Finset.Ico (M - N) M,
          f 1 ((T^[k]) x) ≤ (ε / (N : ℝ)) * (M : ℝ) := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk0 : K₀ ≤ k := by omega
        have ⟨hrat, hk1⟩ := hK₀ k hk0
        have hkR : (0 : ℝ) < (k : ℝ) := by
          exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk1
        have h1 : f 1 ((T^[k]) x) ≤ (ε / (N : ℝ)) * (k : ℝ) :=
          le_of_lt ((div_lt_iff₀ hkR).mp hrat)
        have h2 : (ε / (N : ℝ)) * (k : ℝ) ≤ (ε / (N : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast le_of_lt hk.2) (le_of_lt hδ)
        exact le_trans h1 h2
      have hcard : (Finset.Ico (M - N) M).card ≤ N := by
        rw [Nat.card_Ico]
        omega
      have hBnn : (0 : ℝ) ≤ (ε / (N : ℝ)) * (M : ℝ) :=
        mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
      have hNR : (N : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN)
      calc (∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x))
          ≤ (Finset.Ico (M - N) M).card • ((ε / (N : ℝ)) * (M : ℝ)) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((Finset.Ico (M - N) M).card : ℝ) * ((ε / (N : ℝ)) * (M : ℝ)) :=
            nsmul_eq_mul _ _
        _ ≤ (N : ℝ) * ((ε / (N : ℝ)) * (M : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hBnn
        _ = ε * (M : ℝ) := by
            rw [← mul_assoc, mul_div_cancel₀ _ hNR]
    have hN10 := kingman_pointwise_bound f hf_nn hf_zero hf_subadd ε (le_of_lt hε)
      N x hinv
    have hfinal : ∀ᶠ M in atTop,
        f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε := by
      filter_upwards [eventually_ge_atTop N', eventually_ge_atTop 1, htail] with M
        hMN' hM1 htailM
      have hS := hSbound M hMN'
      have hMR : (0 : ℝ) < (M : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM1
      rw [div_le_iff₀ hMR]
      have hN10M := hN10 M
      linarith [hN10M, hS, htailM]
    exact hbad hfinal
  have hmeasD : ∀ N : ℕ, 1 ≤ N →
      μ Bad ≤ ENNReal.ofReal ((∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε) := by
    intro N hN
    have hsub := hBadsub N hN
    have hAmeas : MeasurableSet (kingmanBadSet f ε N) :=
      kingmanBadSet_measurable f hf_meas ε N
    have hφm : Measurable ((kingmanBadSet f ε N).indicator (f 1)) :=
      (hf_meas 1).indicator hAmeas
    have hφi : Integrable ((kingmanBadSet f ε N).indicator (f 1)) μ :=
      (hf_int 1).indicator hAmeas
    have hφnn : ∀ x, 0 ≤ ((kingmanBadSet f ε N).indicator (f 1)) x :=
      Set.indicator_nonneg (fun a _ => hf_nn 1 a)
    have hN3 := measure_kingmanDick_le hT hφm hφi hφnn hε
    have hint : (∫ x, (kingmanBadSet f ε N).indicator (f 1) x ∂μ)
        = ∫ y in kingmanBadSet f ε N, f 1 y ∂μ :=
      integral_indicator hAmeas
    rw [hint] at hN3
    exact le_trans (measure_mono hsub) hN3
  have hN11 : Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop
      (nhds 0) :=
    tendsto_setIntegral_kingmanBad f hf_meas hf_int ε hε hfin
  have htoZero : Tendsto
      (fun N : ℕ => ENNReal.ofReal ((∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε))
      atTop (nhds 0) := by
    have hdiv : Tendsto (fun N : ℕ => (∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε)
        atTop (nhds (0 / ε)) :=
      hN11.div_const ε
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 / ε)).comp hdiv
    rw [zero_div, ENNReal.ofReal_zero] at hcomp
    exact hcomp
  have hBad0 : μ Bad = 0 := by
    have hle : μ Bad ≤ 0 := by
      apply ge_of_tendsto htoZero
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact hmeasD N hN
    exact le_antisymm hle zero_le
  have hBadmem : ∀ᵐ x ∂μ, x ∉ Bad := measure_eq_zero_iff_ae_notMem.mp hBad0
  filter_upwards [hOmega, hBadmem] with x hxO hxB
  by_contra hcon
  apply hxB
  rw [hBad]
  exact ⟨hxO.1, hxO.2, hcon⟩

/-- N13: convergence under everywhere hypotheses. -/
private theorem kingman_core
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / (n : ℝ)) atTop (nhds (g x)) := by
  have hN5a : ∀ n x, f n x ≤ birkhoffSum T (f 1) n x :=
    le_birkhoffSum_one f hf_zero hf_subadd
  have hN5b : ∀ n, ∫ x, f n x ∂μ ≤ (n : ℝ) * ∫ x, f 1 x ∂μ :=
    integral_le_mul_integral_one hT f hf_int hN5a
  have hLmeas : Measurable (kingmanLiminf f) := kingmanLiminf_measurable f hf_meas
  obtain ⟨hLbound, hfin⟩ :=
    kingmanLiminf_lintegral_le f hf_meas hf_int hf_nn hf_zero hN5b
  have hsub : ∀ x, kingmanLiminf f x ≤ kingmanLiminf f (T x) :=
    kingmanLiminf_le_comp f hf_nn hf_zero hf_subadd
  have hLinv1 : ∀ᵐ x ∂μ, kingmanLiminf f (T x) = kingmanLiminf f x := by
    exact (ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hsub)
      (ne_of_lt (lt_of_le_of_lt hLbound ENNReal.ofReal_lt_top))
      (hLmeas.comp hT.measurable).aemeasurable (hT.lintegral_comp hLmeas).le).symm
  have hLinv : ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x :=
    kingmanLiminf_ae_iterate_eq hT f hLinv1
  refine ⟨fun x => (kingmanLiminf f x).toReal, ?_, ?_, ?_⟩
  · apply integrable_toReal_of_lintegral_ne_top hLmeas.aemeasurable
    exact ne_of_lt (lt_of_le_of_lt hLbound ENNReal.ofReal_lt_top)
  · filter_upwards [hLinv1] with x hx
    exact congrArg ENNReal.toReal hx
  · have hup : ∀ j : ℕ, ∀ᵐ x ∂μ, ∀ᶠ M in atTop,
        f M x / (M : ℝ)
          ≤ (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) :=
      fun j => kingman_upper hT f hf_meas hf_int hf_nn hf_zero hf_subadd hLinv hfin
        (1 / ((j : ℝ) + 1)) (by positivity)
    have hupall : ∀ᵐ x ∂μ, ∀ j : ℕ, ∀ᶠ M in atTop,
        f M x / (M : ℝ)
          ≤ (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) :=
      MeasureTheory.ae_all_iff.mpr hup
    filter_upwards [hfin, hupall] with x hxfin hxup
    have hLy : kingmanLiminf f x = ENNReal.ofReal ((kingmanLiminf f x).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hxfin)).symm
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rcases lt_or_ge a' 0 with ha0 | ha0
      · exact Filter.Eventually.of_forall (fun M => lt_of_lt_of_le ha0
          (div_nonneg (hf_nn M x) (Nat.cast_nonneg _)))
      · have h0ℓ : (0 : ℝ) < (kingmanLiminf f x).toReal :=
          lt_of_le_of_lt ha0 ha'
        have hlt : ENNReal.ofReal a' < kingmanLiminf f x := by
          conv_rhs => rw [hLy]
          exact (ENNReal.ofReal_lt_ofReal_iff h0ℓ).mpr ha'
        unfold kingmanLiminf at hlt
        have hev := Filter.eventually_lt_of_lt_liminf hlt
        filter_upwards [hev] with M hM
        exact (ENNReal.ofReal_lt_ofReal_iff'.mp hM).1
    · intro a' ha'
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (a' - (kingmanLiminf f x).toReal) / 4 by linarith)
      have hj' : (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) < a' := by
        linarith [hj]
      filter_upwards [hxup j] with M hM
      exact lt_of_le_of_lt hM hj'


/-- Nonnegative integrable subadditive cocycles on any finite measure space have
an integrable invariant real limit almost everywhere. The original zeroth term
is unrestricted; division at zero uses the canonical real division. -/
theorem kingman_subadditive
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (X : ℕ → α → ℝ)
    (hX_int : ∀ n, Integrable (X n) μ)
    (hX_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ X n x)
    (hX_subadd : ∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n ((T^[m]) x)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => X n x / (n : ℝ)) atTop (nhds (g x)) := by
  classical
  by_cases hμ : μ = 0
  · subst μ
    exact ⟨fun _ => 0, integrable_zero _ _ _, by simp, by simp⟩
  letI : NeZero μ := ⟨hμ⟩
  let ν : Measure α := (μ Set.univ)⁻¹ • μ
  have hν : IsProbabilityMeasure ν := inferInstance
  letI := hν
  have hTν : MeasurePreserving T ν ν := hT.smul_measure _
  have hae : ae ν = ae μ :=
    ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.mpr (measure_ne_top μ _)) μ
  have hXi : ∀ n, Integrable (X n) ν := fun n => (hX_int n).to_average
  let Y : ℕ → α → ℝ := fun n =>
    if n = 0 then 0 else (hXi n).aestronglyMeasurable.mk (X n)
  have hYm : ∀ n, Measurable (Y n) := by
    intro n
    by_cases hn : n = 0
    · simp only [Y, if_pos hn]; exact measurable_const
    · simpa only [Y, if_neg hn] using (hXi n).aestronglyMeasurable.measurable_mk
  have hYeq : ∀ n, n ≠ 0 → Y n =ᵐ[ν] X n := by
    intro n hn
    simpa only [Y, if_neg hn] using (hXi n).aestronglyMeasurable.ae_eq_mk.symm
  have hY0 : ∀ x, Y 0 x = 0 := by simp [Y]
  have hYi : ∀ n, Integrable (Y n) ν := by
    intro n
    by_cases hn : n = 0
    · subst n; simpa only [Y, if_pos rfl] using (integrable_zero α ℝ ν)
    · exact (hXi n).congr (hYeq n hn).symm
  have hYnn : ∀ n, ∀ᵐ x ∂ν, 0 ≤ Y n x := by
    intro n
    by_cases hn : n = 0
    · subst n; exact Filter.Eventually.of_forall (fun x => (hY0 x).ge)
    · have hnn : ∀ᵐ x ∂ν, 0 ≤ X n x := by rw [hae]; exact hX_nonneg n
      filter_upwards [hYeq n hn, hnn] with x hx hnx
      rwa [hx]
  have hYsub : ∀ m n, ∀ᵐ x ∂ν,
      Y (m + n) x ≤ Y m x + Y n ((T^[m]) x) := by
    intro m n
    by_cases hm : m = 0
    · subst m; simp only [zero_add, Function.iterate_zero_apply, hY0]
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    by_cases hn : n = 0
    · subst n; simp only [add_zero, hY0]
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    have hmn : m + n ≠ 0 := by omega
    have hsub : ∀ᵐ x ∂ν, X (m + n) x ≤ X m x + X n ((T^[m]) x) := by
      rw [hae]; exact hX_subadd m n
    have hshift := (hTν.iterate m).quasiMeasurePreserving.ae (hYeq n hn)
    filter_upwards [hYeq (m + n) hmn, hYeq m hm, hshift, hsub] with x hmnx hmx hnx hx
    simpa only [hmnx, hmx, hnx] using hx
  obtain ⟨Z, hZm, hZeq, hZnn, hZ0, hZsub⟩ :=
    kingman_reduce_everywhere hTν Y hYm hYnn (Filter.Eventually.of_forall hY0) hYsub
  have hZi : ∀ n, Integrable (Z n) ν := fun n => (hYi n).congr (hZeq n).symm
  obtain ⟨g, hgi, hginv, hglim⟩ := kingman_core hTν Z hZm hZi hZnn hZ0 hZsub
  refine ⟨g, integrable_average.mp hgi, ?_, ?_⟩
  · rwa [hae] at hginv
  · have hall : ∀ᵐ x ∂ν, ∀ n, n ≠ 0 → Z n x = X n x := by
      rw [ae_all_iff]
      intro n
      by_cases hn : n = 0
      · exact Filter.Eventually.of_forall (fun _ h => (h hn).elim)
      · filter_upwards [hZeq n, hYeq n hn] with x hz hy
        exact fun _ => hz.trans hy
    have hlim : ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => X n x / (n : ℝ)) atTop (nhds (g x)) := by
      filter_upwards [hglim, hall] with x hx heq
      apply hx.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [heq n (by omega)]
    rwa [hae] at hlim

end D5.S3.Analytic.Probability.KingmanPointwise
