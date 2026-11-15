/- GID: D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/GeneratorConditioning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov-Sinai generatorconditioning for the full-shift equilibrium proof. -/

/- Copyright (c) 2026 Marcel Morgenstern. Licensed under Apache-2.0.
   Selected source port of marcmorningstar/lean4-ergodic-theory,
   revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f.
   Attribution, source mapping and full license: Library/Entropy/morgenstern2026ks.md.
   Adaptation: current Lean APIs, subject namespaces and live-dependency pruning.
   Retire each ported declaration when an equivalent declaration exists in this
   repository's pinned mathlib revision, replacing consumers by direct imports. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.KolmogorovSinai.EntropyRate



open MeasureTheory Function Filter ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]

section Bridge

variable [Fintype ι]

omit [StandardBorelSpace α]

private lemma measurableSet_generatedSigmaAlgebra_cell {μ : Measure α} (B : MeasurePartition μ ι)
    (i : ι) : MeasurableSet[generatedSigmaAlgebra μ B] (B.cells i) :=
  measurableSet_generateFrom ⟨i, rfl⟩

lemma generatedSigmaAlgebra_le {μ : Measure α} (B : MeasurePartition μ ι) :
    generatedSigmaAlgebra μ B ≤ mα :=
  generateFrom_le <| by rintro s ⟨i, rfl⟩; exact B.measurable i

private lemma generatedSigmaAlgebra_atom {μ : Measure α} (B : MeasurePartition μ ι)
    {s : Set α} (hs : MeasurableSet[generatedSigmaAlgebra μ B] s) (i : ι) :
    μ (B.cells i ∩ s) = 0 ∨ μ (B.cells i \ s) = 0 := by
  rw [generatedSigmaAlgebra] at hs
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC t ht _ =>
    obtain ⟨k, rfl⟩ := ht
    rcases eq_or_ne i k with rfl | hik
    · exact Or.inr (by simp)
    · exact Or.inl (B.aedisjoint hik)
  | empty => exact Or.inl (by simp)
  | compl t ht ih =>
    
    rw [← Set.diff_eq, Set.diff_compl]
    exact ih.symm
  | iUnion f hf ih =>
    by_cases hall : ∀ n, μ (B.cells i ∩ f n) = 0
    · refine Or.inl (measure_mono_null ?_ (measure_iUnion_null hall))
      rw [Set.inter_iUnion]
    · rw [not_forall] at hall
      obtain ⟨n, hn⟩ := hall
      refine Or.inr (measure_mono_null ?_ ((ih n).resolve_left hn))
      intro x hx; exact ⟨hx.1, fun hxU => hx.2 (Set.mem_iUnion.2 ⟨n, hxU⟩)⟩

private noncomputable def condCandidate {μ : Measure α} (B : MeasurePartition μ ι) (tj : Set α)
    (ω : α) : ℝ :=
  ∑ i, (B.cells i).indicator (fun _ => (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal) ω

private lemma stronglyMeasurable_condCandidate {μ : Measure α} (B : MeasurePartition μ ι) (tj : Set α) :
    StronglyMeasurable[generatedSigmaAlgebra μ B] (condCandidate B tj) := by
  refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact stronglyMeasurable_const.indicator (measurableSet_generatedSigmaAlgebra_cell B i)

private lemma condCandidate_cell_scaling {μ : Measure α} [IsFiniteMeasure μ] (B : MeasurePartition μ ι)
    {tj : Set α} {s : Set α} (hs : MeasurableSet[generatedSigmaAlgebra μ B] s) (i : ι) :
    (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal * (μ (s ∩ B.cells i)).toReal
      = (μ (s ∩ B.cells i ∩ tj)).toReal := by
  rcases generatedSigmaAlgebra_atom B hs i with hatom | hatom
  · 
    have h1 : μ (s ∩ B.cells i) = 0 := by rwa [Set.inter_comm] at hatom
    have h2 : μ (s ∩ B.cells i ∩ tj) = 0 := measure_mono_null Set.inter_subset_left h1
    simp [h1, h2]
  · 
    have heq1 : μ (s ∩ B.cells i) = μ (B.cells i) := by
      apply le_antisymm (measure_mono Set.inter_subset_right)
      have : B.cells i ⊆ (s ∩ B.cells i) ∪ (B.cells i \ s) := by
        intro x hx; by_cases hxs : x ∈ s
        · exact Or.inl ⟨hxs, hx⟩
        · exact Or.inr ⟨hx, hxs⟩
      calc μ (B.cells i) ≤ μ ((s ∩ B.cells i) ∪ (B.cells i \ s)) := measure_mono this
        _ ≤ μ (s ∩ B.cells i) + μ (B.cells i \ s) := measure_union_le _ _
        _ = μ (s ∩ B.cells i) := by rw [hatom, add_zero]
    have heq2 : μ (s ∩ B.cells i ∩ tj) = μ (B.cells i ∩ tj) := by
      apply le_antisymm (measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_right))
      have hsub : B.cells i ∩ tj ⊆ (s ∩ B.cells i ∩ tj) ∪ (B.cells i \ s) := by
        intro x hx; by_cases hxs : x ∈ s
        · exact Or.inl ⟨⟨hxs, hx.1⟩, hx.2⟩
        · exact Or.inr ⟨hx.1, hxs⟩
      calc μ (B.cells i ∩ tj) ≤ μ ((s ∩ B.cells i ∩ tj) ∪ (B.cells i \ s)) := measure_mono hsub
        _ ≤ μ (s ∩ B.cells i ∩ tj) + μ (B.cells i \ s) := measure_union_le _ _
        _ = μ (s ∩ B.cells i ∩ tj) := by rw [hatom, add_zero]
    rw [heq1, heq2]
    rcases eq_or_ne (μ (B.cells i)) 0 with hzero | hzero
    · have : μ (B.cells i ∩ tj) = 0 := measure_mono_null Set.inter_subset_left hzero
      rw [hzero, this, ENNReal.toReal_zero, mul_zero]
    · have hne : (μ (B.cells i)).toReal ≠ 0 := by
        rw [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
        exact ⟨hzero, measure_ne_top μ _⟩
      rw [div_mul_cancel₀ _ hne]

private lemma setIntegral_condCandidate {μ : Measure α} [IsFiniteMeasure μ] (B : MeasurePartition μ ι)
    {tj : Set α} (htj : MeasurableSet tj) {s : Set α}
    (hs : MeasurableSet[generatedSigmaAlgebra μ B] s) :
    ∫ x in s, condCandidate B tj x ∂μ = (μ (s ∩ tj)).toReal := by
  have hsm : MeasurableSet s := (generatedSigmaAlgebra_le B) s hs
  simp only [condCandidate]
  
  rw [integral_finsetSum]
  swap
  · intro i _
    exact (integrable_const _).indicator (B.measurable i) |>.restrict
  
  have hterm : ∀ i, ∫ x in s,
      (B.cells i).indicator
        (fun _ => (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal) x ∂μ
      = (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal * (μ (s ∩ B.cells i)).toReal := by
    intro i
    rw [setIntegral_indicator (B.measurable i), setIntegral_const, smul_eq_mul,
      measureReal_def, mul_comm]
  simp_rw [hterm]
  
  rw [show (∑ i, (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal
        * (μ (s ∩ B.cells i)).toReal)
      = ∑ i, (μ (s ∩ B.cells i ∩ tj)).toReal from
    Finset.sum_congr rfl fun i _ => condCandidate_cell_scaling B hs i]
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
  congr 1
  rw [B.measure_eq_sum_inter (hsm.inter htj)]
  exact Finset.sum_congr rfl fun i _ => by rw [Set.inter_right_comm]

private lemma condCandidate_ae_eq_condExp {μ : Measure α} [IsFiniteMeasure μ] (B : MeasurePartition μ ι)
    {tj : Set α} (htj : MeasurableSet tj) :
    condCandidate B tj =ᵐ[μ] μ⟦tj | generatedSigmaAlgebra μ B⟧ := by
  have hm : generatedSigmaAlgebra μ B ≤ mα := generatedSigmaAlgebra_le B
  have hsf : SigmaFinite (μ.trim hm) := inferInstance
  have hf : Integrable (tj.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator htj
  
  have hgint : ∀ s, MeasurableSet[generatedSigmaAlgebra μ B] s → μ s < ∞ →
      IntegrableOn (condCandidate B tj) s μ := by
    intro s hs _
    refine Integrable.integrableOn ?_
    refine integrable_finsetSum _ (fun i _ => ?_)
    exact (integrable_const _).indicator (B.measurable i)
  have hgeq : ∀ s, MeasurableSet[generatedSigmaAlgebra μ B] s → μ s < ∞ →
      ∫ x in s, condCandidate B tj x ∂μ = ∫ x in s, tj.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    intro s hs _
    rw [setIntegral_condCandidate B htj hs, setIntegral_indicator htj, setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def]
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf hgint hgeq
    (stronglyMeasurable_condCandidate B tj).aestronglyMeasurable

private lemma condCandidate_ae_eq_on_cell {μ : Measure α} (B : MeasurePartition μ ι) (tj : Set α)
    (i : ι) :
    (fun ω => condCandidate B tj ω)
      =ᵐ[μ.restrict (B.cells i)]
      fun _ => (μ (B.cells i ∩ tj)).toReal / (μ (B.cells i)).toReal := by
  
  
  have hnull : ∀ k, k ≠ i → ∀ᵐ ω ∂μ.restrict (B.cells i), ω ∉ B.cells k := by
    intro k hki
    rw [ae_restrict_iff' (B.measurable i)]
    have hnk : μ (B.cells i ∩ B.cells k) = 0 := B.aedisjoint (Ne.symm hki)
    have hae : ∀ᵐ ω ∂μ, ω ∉ B.cells i ∩ B.cells k := by rw [ae_iff]; simpa using hnk
    filter_upwards [hae] with ω hω hωi
    simp only [Set.mem_inter_iff, not_and] at hω
    exact hω hωi
  have hnull' : ∀ᵐ ω ∂μ.restrict (B.cells i), ∀ k, k ≠ i → ω ∉ B.cells k := by
    rw [ae_all_iff]; intro k
    by_cases hki : k = i
    · subst hki; exact Eventually.of_forall fun ω hk => absurd rfl hk
    · filter_upwards [hnull k hki] with ω hω _ using hω
  have hself : ∀ᵐ ω ∂μ.restrict (B.cells i), ω ∈ B.cells i := by
    rw [ae_restrict_iff' (B.measurable i)]; exact Eventually.of_forall (fun ω h => h)
  filter_upwards [hnull', hself] with ω hω hωi
  rw [condCandidate, Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hωi]
  · intro k _ hki
    rw [Set.indicator_of_notMem (hω k hki)]
  · intro h; exact absurd (Finset.mem_univ i) h

end Bridge

section Main

variable [Fintype ι] [Fintype κ]

private theorem condEntropyGivenPartition_eq_condEntropy_generated {μ : Measure α}
    [IsProbabilityMeasure μ] (B : MeasurePartition μ ι) (t : κ → Set α)
    (ht : ∀ j, MeasurableSet (t j)) :
    condEntropyGivenPartition μ B.cells t = condEntropy μ (generatedSigmaAlgebra μ B) t := by
  have hm : generatedSigmaAlgebra μ B ≤ mα := generatedSigmaAlgebra_le B
  
  let F : α → ℝ := fun ω =>
    ∑ j, Real.negMulLog (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) ω (t j)).toReal
  let G : α → ℝ := fun ω => ∑ j, Real.negMulLog (condCandidate B (t j) ω)
  
  have hFG : F =ᵐ[μ] G := by
    have hcell : ∀ j,
        (fun ω => (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) ω (t j)).toReal)
          =ᵐ[μ] fun ω => condCandidate B (t j) ω := by
      intro j
      have h1 := condExpKernel_ae_eq_condExp (μ := μ) (m := generatedSigmaAlgebra μ B) hm (ht j)
      have h2 := (condCandidate_ae_eq_condExp B (ht j)).symm
      filter_upwards [h1, h2] with ω hω1 hω2
      rw [measureReal_def] at hω1
      rw [hω1, ← hω2]
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun j _ => by rw [hω j]
  
  rw [condEntropy_def]
  rw [show (∫ ω, (∑ j,
        Real.negMulLog (@condExpKernel α mα _ μ _ (generatedSigmaAlgebra μ B) ω (t j)).toReal) ∂μ)
      = ∫ ω, F ω ∂μ from rfl, integral_congr_ae hFG]
  
  
  have hFint : Integrable F μ := integrable_condEntropy_integrand hm t ht
  have hGint : Integrable G μ := hFint.congr hFG
  
  have hcover : (⋃ i, B.cells i) = Set.univ := B.cover
  have hsplit : ∫ ω, G ω ∂μ = ∑ i, ∫ ω in B.cells i, G ω ∂μ := by
    rw [← setIntegral_univ (μ := μ), ← hcover,
      integral_iUnion_ae (fun i => (B.measurable i).nullMeasurableSet) B.aedisjoint
        (by rw [hcover]; exact hGint.integrableOn),
      tsum_fintype]
  rw [hsplit, condEntropyGivenPartition]
  
  refine Finset.sum_congr rfl fun i _ => ?_
  have hGcell : (fun ω => G ω)
      =ᵐ[μ.restrict (B.cells i)] fun _ => condEntropyOnCell μ (B.cells i) t := by
    have hcand : ∀ j, (fun ω => condCandidate B (t j) ω)
        =ᵐ[μ.restrict (B.cells i)]
        fun _ => (μ (B.cells i ∩ t j)).toReal / (μ (B.cells i)).toReal :=
      fun j => condCandidate_ae_eq_on_cell B (t j) i
    filter_upwards [ae_all_iff.2 hcand] with ω hω
    simp only [G, condEntropyOnCell]
    exact Finset.sum_congr rfl fun j _ => by rw [hω j]
  rw [show (∫ ω in B.cells i, G ω ∂μ)
      = ∫ _ω in B.cells i, condEntropyOnCell μ (B.cells i) t ∂μ from
    setIntegral_congr_ae (B.measurable i) (ae_imp_of_ae_restrict hGcell),
    setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]

end Main

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}

private theorem tendsto_condCellSeq_of_defect [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (hdefect : Tendsto (fun n => (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        (ksJoin hT P n).cells - condKsEntropySeq 𝒜 hT P n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => condCellSeq hT Q P n / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
  
  
  have hbridge : ∀ n, condCellSeq hT Q P n
      = condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells := fun n =>
    condEntropyGivenPartition_eq_condEntropy_generated (ksJoin hT Q n) (ksJoin hT P n).cells
      (ksJoin hT P n).measurable
  
  have hsplit : (fun n => condCellSeq hT Q P n / n)
      = fun n => condKsEntropySeq 𝒜 hT P n / n
        + (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
            - condKsEntropySeq 𝒜 hT P n) / n := by
    funext n
    rw [hbridge n, ← add_div, add_sub_cancel]
  
  have hsum : Tendsto (fun n => condKsEntropySeq 𝒜 hT P n / n
        + (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
            - condKsEntropySeq 𝒜 hT P n) / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
    have := (tendsto_condKsEntropySeq hm hT hinv P).add hdefect
    rwa [add_zero] at this
  rwa [hsplit]

theorem abramovRokhlin_partition_of_defect [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (g : ∀ n, (Fin n → ι) → (Fin n → κ))
    (hrefine : ∀ n f, (ksJoin hT P n).cells f ≤ᵐ[μ] (ksJoin hT Q n).cells (g n f))
    (hdefect : Tendsto (fun n => (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        (ksJoin hT P n).cells - condKsEntropySeq 𝒜 hT P n) / n) atTop (𝓝 0)) :
    ksEntropyPartition hT P
      = ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P :=
  abramovRokhlin_partition_of_W3 hm hT hinv Q P g hrefine
    (tendsto_condCellSeq_of_defect hm hT hinv Q P hdefect)

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} {ℱ : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

lemma condEntropy_ksJoin_le_nsmul_log_card [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hℱ : ℱ ≤ mα)
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    condEntropy μ ℱ (ksJoin hT P n).cells ≤ n * Real.log (Fintype.card ι) := by
  calc condEntropy μ ℱ (ksJoin hT P n).cells
      ≤ Real.log (Fintype.card (Fin n → ι)) := condEntropy_le_log_card hℱ (ksJoin hT P n)
    _ = Real.log (((Fintype.card ι : ℝ)) ^ n) := by
        rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    _ = n * Real.log (Fintype.card ι) := by
        rw [Real.log_pow]

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter ProbabilityTheory Set
open scoped ENNReal Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]

theorem condEntropy_tendsto_iSup [Fintype ι] [Nonempty ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (𝒜seq : ℕ → MeasurableSpace α) (hmono : Monotone 𝒜seq) (hle : ∀ n, 𝒜seq n ≤ mα)
    (P : MeasurePartition μ ι) :
    Tendsto (fun n => condEntropy μ (𝒜seq n) P.cells) atTop
      (𝓝 (condEntropy μ (⨆ n, 𝒜seq n) P.cells)) := by
  
  have hℬle : (⨆ n, 𝒜seq n) ≤ mα := iSup_le hle
  
  let ℱ : Filtration ℕ mα := ⟨𝒜seq, hmono, hle⟩
  
  let g : ι → α → ℝ := fun i => (P.cells i).indicator (fun _ => (1 : ℝ))
  
  have hcell : ∀ i, ∀ᵐ ω ∂μ, Tendsto
      (fun n => (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal) atTop
      (𝓝 (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal) := by
    intro i
    
    have hlevy : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g i | ℱ n]) ω) atTop
        (𝓝 ((μ[g i | ⨆ n, ℱ n]) ω)) :=
      MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (g i)
    
    have haen : ∀ n, (fun ω => (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal)
        =ᵐ[μ] fun ω => (μ[g i | ℱ n]) ω := fun n => by
      simpa only [measureReal_def] using
        condExpKernel_ae_eq_condExp (hle n) (P.measurable i)
    
    have haelim : (fun ω => (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal)
        =ᵐ[μ] fun ω => (μ[g i | ⨆ n, ℱ n]) ω := by
      simpa only [measureReal_def] using
        condExpKernel_ae_eq_condExp hℬle (P.measurable i)
    filter_upwards [hlevy, ae_all_iff.2 haen, haelim] with ω hω hωn hωlim
    rw [hωlim]
    exact hω.congr fun n => (hωn n).symm
  
  have hsum : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal)
      atTop
      (𝓝 (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (⨆ n, 𝒜seq n) ω (P.cells i)).toReal)) := by
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    refine tendsto_finsetSum _ fun i _ => ?_
    exact (Real.continuous_negMulLog.tendsto _).comp (hω i)
  
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal‖
        ≤ Real.log (Fintype.card ι) := by
    intro n
    filter_upwards [condExpKernel_sum_toReal_measure_eq_one (hle n) P] with ω hω
    have hnn : 0 ≤ ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal :=
      negMulLog_condExpKernel_sum_nonneg P.cells ω
    have hle' := entropy_le_log_card (μ := @condExpKernel α mα _ μ _ (𝒜seq n) ω) P.cells hω
    rw [entropy_def] at hle'
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hmeasF : ∀ n, AEStronglyMeasurable
      (fun ω => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ (𝒜seq n) ω (P.cells i)).toReal) μ :=
    fun n => (integrable_condEntropy_integrand (hle n) P.cells (fun i => P.measurable i)).1
  simpa only [condEntropy_def] using
    tendsto_integral_of_dominated_convergence (fun _ => Real.log (Fintype.card ι))
      hmeasF (integrable_const _) hbound hsum

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function MeasurableSpace

namespace D5.S3.Entropy.KolmogorovSinai

variable {α β : Type*} {ι : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [Fintype ι]
variable {μ : Measure α} {ν : Measure β}

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function MeasurableSpace

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {κ : Type*} [mα : MeasurableSpace α] {μ : Measure α} [Fintype κ]
  {T : α → α} (hT : MeasurePreserving T μ μ) (Q : MeasurePartition μ κ)

private lemma preimage_cells_eq_iUnion (n : ℕ) (k : Fin n) (i : κ) :
    (T^[(k : ℕ)]) ⁻¹' Q.cells i =
      ⋃ g : {g : Fin n → κ // g k = i}, ksJoinCells Q.cells T n (g : Fin n → κ) := by
  apply Set.Subset.antisymm
  · 
    intro x hx
    have hcov : ∀ l : Fin n, ∃ j, (T^[(l : ℕ)]) x ∈ Q.cells j := fun l => by
      have : (T^[(l : ℕ)]) x ∈ ⋃ j, Q.cells j := Q.cover ▸ Set.mem_univ _
      exact Set.mem_iUnion.mp this
    choose g₀ hg₀ using hcov
    
    refine Set.mem_iUnion.mpr ⟨⟨Function.update g₀ k i, by simp⟩, ?_⟩
    rw [ksJoinCells_apply]
    refine Set.mem_iInter.mpr fun l => ?_
    by_cases hlk : l = k
    · subst hlk; simpa using hx
    · simpa [Function.update_of_ne hlk] using hg₀ l
  · 
    refine Set.iUnion_subset fun g => ?_
    rw [ksJoinCells_apply]
    refine (Set.iInter_subset _ k).trans ?_
    rw [g.2]

private lemma measurableSet_preimage_cells (n : ℕ) (k : Fin n) (i : κ) :
    MeasurableSet[generatedSigmaAlgebra μ (ksJoin hT Q n)] ((T^[(k : ℕ)]) ⁻¹' Q.cells i) := by
  rw [preimage_cells_eq_iUnion Q n k i]
  refine MeasurableSet.iUnion fun g => ?_
  exact measurableSet_generateFrom ⟨(g : Fin n → κ), rfl⟩

lemma generatedSigmaAlgebra_ksJoin_mono {M n : ℕ} (hMn : M ≤ n) :
    generatedSigmaAlgebra μ (ksJoin hT Q M) ≤ generatedSigmaAlgebra μ (ksJoin hT Q n) := by
  refine generateFrom_le ?_
  rintro s ⟨f, rfl⟩
  rw [ksJoin_cells, ksJoinCells_apply]
  refine MeasurableSet.iInter fun k => ?_
  
  have hk : ((⟨(k : ℕ), lt_of_lt_of_le k.2 hMn⟩ : Fin n) : ℕ) = (k : ℕ) := rfl
  have := measurableSet_preimage_cells hT Q n ⟨(k : ℕ), lt_of_lt_of_le k.2 hMn⟩ (f k)
  rwa [hk] at this

lemma comap_iterate_generatedSigmaAlgebra_ksJoin_le (a b : ℕ) :
    MeasurableSpace.comap (T^[a]) (generatedSigmaAlgebra μ (ksJoin hT Q b)) ≤
      generatedSigmaAlgebra μ (ksJoin hT Q (a + b)) := by
  rw [generatedSigmaAlgebra, MeasurableSpace.comap_generateFrom]
  refine generateFrom_le ?_
  rintro s ⟨t, ⟨f, rfl⟩, rfl⟩
  
  rw [ksJoin_cells, ksJoinCells_apply, Set.preimage_iInter]
  refine MeasurableSet.iInter fun l => ?_
  
  have hcomp : (T^[a]) ⁻¹' ((T^[(l : ℕ)]) ⁻¹' Q.cells (f l))
      = (T^[(a + (l : ℕ))]) ⁻¹' Q.cells (f l) := by
    rw [← Set.preimage_comp, ← Function.iterate_add, Nat.add_comm]
  rw [hcomp]
  
  have hlt : a + (l : ℕ) < a + b := by omega
  have hidx : ((⟨a + (l : ℕ), hlt⟩ : Fin (a + b)) : ℕ) = a + (l : ℕ) := rfl
  have := measurableSet_preimage_cells hT Q (a + b) ⟨a + (l : ℕ), hlt⟩ (f l)
  rwa [hidx] at this

private lemma generatedSigmaAlgebra_ksJoin_one :
    generatedSigmaAlgebra μ (ksJoin hT Q 1) = generatedSigmaAlgebra μ Q := by
  rw [generatedSigmaAlgebra, generatedSigmaAlgebra, ksJoin_cells]
  congr 1
  
  
  have hcell : ∀ f : Fin 1 → κ, ksJoinCells Q.cells T 1 f = Q.cells (f 0) := by
    intro f
    rw [ksJoinCells_apply]
    have hbody : (fun k : Fin 1 => (T^[(k : ℕ)]) ⁻¹' Q.cells (f k))
        = fun _ : Fin 1 => Q.cells (f 0) := by
      funext k
      rw [Subsingleton.elim k 0, Fin.val_zero, Function.iterate_zero, Set.preimage_id]
    rw [hbody, Set.iInter_const]
  apply Set.Subset.antisymm
  · rintro s ⟨f, rfl⟩
    exact ⟨f 0, (hcell f).symm⟩
  · rintro s ⟨i, rfl⟩
    exact ⟨fun _ => i, hcell (fun _ => i)⟩

lemma iSup_generatedSigmaAlgebra_ksJoin_eq :
    (⨆ n : ℕ, generatedSigmaAlgebra μ (ksJoin hT Q n)) =
      ⨆ k : ℕ, MeasurableSpace.comap (T^[k]) (generatedSigmaAlgebra μ Q) := by
  apply le_antisymm
  · 
    refine iSup_le fun n => ?_
    refine generateFrom_le ?_
    rintro s ⟨f, rfl⟩
    rw [ksJoin_cells, ksJoinCells_apply]
    refine MeasurableSet.iInter fun k => ?_
    
    refine le_iSup (fun k : ℕ => MeasurableSpace.comap (T^[k]) (generatedSigmaAlgebra μ Q))
      (k : ℕ) _ ?_
    exact ⟨Q.cells (f k), measurableSet_generateFrom ⟨f k, rfl⟩, rfl⟩
  · 
    refine iSup_le fun k => ?_
    refine le_trans ?_ (le_iSup (fun n : ℕ => generatedSigmaAlgebra μ (ksJoin hT Q n)) (k + 1))
    
    rw [← generatedSigmaAlgebra_ksJoin_one hT Q]
    exact comap_iterate_generatedSigmaAlgebra_ksJoin_le hT Q k 1

end D5.S3.Entropy.KolmogorovSinai


