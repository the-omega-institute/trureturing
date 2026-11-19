/- GID: D5/S3/Entropy/KolmogorovSinai/EntropyRate
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/EntropyRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov-Sinai entropyrate for the full-shift equilibrium proof. -/

/- Copyright (c) 2026 Marcel Morgenstern. Licensed under Apache-2.0.
   Selected source port of marcmorningstar/lean4-ergodic-theory,
   revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f.
   Attribution, source mapping and full license: Library/Entropy/morgenstern2026ks.md.
   Adaptation: current Lean APIs, subject namespaces and live-dependency pruning.
   Retire each ported declaration when an equivalent declaration exists in this
   repository's pinned mathlib revision, replacing consumers by direct imports. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.KolmogorovSinai.Partition



open MeasureTheory Function Filter ProbabilityTheory Set
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} {𝒜 ℬ : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

lemma condEntropy_mono_of_le [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜ℬ : 𝒜 ≤ ℬ) (hℬ : ℬ ≤ mα) (P : MeasurePartition μ ι) :
    condEntropy μ ℬ P.cells ≤ condEntropy μ 𝒜 P.cells := by
  have h𝒜 : 𝒜 ≤ mα := h𝒜ℬ.trans hℬ
  haveI : SigmaFinite (μ.trim h𝒜) := inferInstance
  haveI : SigmaFinite (μ.trim hℬ) := inferInstance
  rw [condEntropy_def, condEntropy_def]
  
  rw [integral_finsetSum _
      (fun i _ => integrable_negMulLog_condExpKernel hℬ (P.measurable i)),
    integral_finsetSum _
      (fun i _ => integrable_negMulLog_condExpKernel h𝒜 (P.measurable i))]
  refine Finset.sum_le_sum fun i _ => ?_
  
  set fℬ : α → ℝ := fun ω => (@condExpKernel α mα _ μ _ ℬ ω (P.cells i)).toReal with hfℬ
  set f𝒜 : α → ℝ := fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal with hf𝒜
  
  have hint_fℬ : Integrable fℬ μ := integrable_toReal_condExpKernel (P.measurable i)
  have hint_gℬ : Integrable (Real.negMulLog ∘ fℬ) μ :=
    integrable_negMulLog_condExpKernel hℬ (P.measurable i)
  
  have hae_ℬ : fℬ =ᵐ[μ] μ⟦P.cells i | ℬ⟧ := by
    simpa only [hfℬ, measureReal_def] using condExpKernel_ae_eq_condExp hℬ (P.measurable i)
  have hae_𝒜 : f𝒜 =ᵐ[μ] μ⟦P.cells i | 𝒜⟧ := by
    simpa only [hf𝒜, measureReal_def] using condExpKernel_ae_eq_condExp h𝒜 (P.measurable i)
  
  have htower : μ[fℬ | 𝒜] =ᵐ[μ] f𝒜 := by
    calc μ[fℬ | 𝒜] =ᵐ[μ] μ[μ⟦P.cells i | ℬ⟧ | 𝒜] := condExp_congr_ae hae_ℬ
      _ =ᵐ[μ] μ⟦P.cells i | 𝒜⟧ := condExp_condExp_of_le h𝒜ℬ hℬ
      _ =ᵐ[μ] f𝒜 := hae_𝒜.symm
  
  have hmem : ∀ᵐ ω ∂μ, fℬ ω ∈ Set.Ici (0 : ℝ) :=
    Eventually.of_forall fun ω => Set.mem_Ici.mpr ENNReal.toReal_nonneg
  have hjensen : μ[Real.negMulLog ∘ fℬ | 𝒜] ≤ᵐ[μ] Real.negMulLog ∘ μ[fℬ | 𝒜] :=
    Real.concaveOn_negMulLog.condExp_map_le h𝒜
      Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn hmem isClosed_Ici
      hint_fℬ hint_gℬ
  
  have hjensen' : μ[Real.negMulLog ∘ fℬ | 𝒜] ≤ᵐ[μ] Real.negMulLog ∘ f𝒜 := by
    filter_upwards [hjensen, htower] with ω hω htw
    simpa only [Function.comp_apply, htw] using hω
  
  calc ∫ ω, Real.negMulLog (fℬ ω) ∂μ
      = ∫ ω, (μ[Real.negMulLog ∘ fℬ | 𝒜]) ω ∂μ := (integral_condExp h𝒜).symm
    _ ≤ ∫ ω, Real.negMulLog (f𝒜 ω) ∂μ :=
        integral_mono_ae integrable_condExp
          (integrable_negMulLog_condExpKernel h𝒜 (P.measurable i)) hjensen'

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

private lemma entropy_comp_preimage [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (s : ι → Set α) (hs : ∀ i, NullMeasurableSet (s i) μ) :
    entropy μ (fun i => T ⁻¹' s i) = entropy μ s := by
  rw [entropy_def, entropy_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hT.measure_preimage (hs i)]

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

noncomputable def MeasurePartition.pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) : MeasurePartition μ ι where
  cells := fun i => T ⁻¹' P.cells i
  measurable := fun i => (P.measurable i).preimage hT.measurable
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint, ← Set.preimage_inter]
    rw [hT.measure_preimage ((P.measurable i).inter (P.measurable j)).nullMeasurableSet]
    exact P.aedisjoint hij
  cover := by rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp]
lemma MeasurePartition.pullback_cells [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    (P.pullback hT).cells = fun i => T ⁻¹' P.cells i := rfl

private lemma entropy_pullback [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    entropy μ (P.pullback hT).cells = entropy μ P.cells := by
  rw [MeasurePartition.pullback_cells]
  exact entropy_comp_preimage hT P.cells (fun i => (P.measurable i).nullMeasurableSet)

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

def ksJoinCells (cells : ι → Set α) (T : α → α) (n : ℕ) (f : Fin n → ι) : Set α :=
  ⋂ k : Fin n, (T^[(k : ℕ)]) ⁻¹' cells (f k)

omit [MeasurableSpace α] in
@[simp]
lemma ksJoinCells_apply (cells : ι → Set α) (T : α → α) (n : ℕ) (f : Fin n → ι) :
    ksJoinCells cells T n f = ⋂ k : Fin n, (T^[(k : ℕ)]) ⁻¹' cells (f k) := rfl

noncomputable def ksJoin [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    MeasurePartition μ (Fin n → ι) where
  cells := ksJoinCells P.cells T n
  measurable f := by
    refine MeasurableSet.iInter fun k => ?_
    exact (P.measurable (f k)).preimage (hT.iterate (k : ℕ)).measurable
  aedisjoint := by
    intro f g hfg
    simp only [onFun]
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := by
      by_contra h
      exact hfg (funext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
    have hsub₁ : ksJoinCells P.cells T n f ⊆ (T^[(k : ℕ)]) ⁻¹' P.cells (f k) :=
      Set.iInter_subset _ k
    have hsub₂ : ksJoinCells P.cells T n g ⊆ (T^[(k : ℕ)]) ⁻¹' P.cells (g k) :=
      Set.iInter_subset _ k
    refine AEDisjoint.mono ?_ hsub₁ hsub₂
    simp only [AEDisjoint, ← Set.preimage_inter]
    rw [(hT.iterate (k : ℕ)).measure_preimage
      ((P.measurable (f k)).inter (P.measurable (g k))).nullMeasurableSet]
    exact P.aedisjoint hk
  cover := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : ∀ k : Fin n, ∃ i, (T^[(k : ℕ)]) x ∈ P.cells i := fun k => by
      have : (T^[(k : ℕ)]) x ∈ ⋃ i, P.cells i := P.cover ▸ Set.mem_univ _
      exact Set.mem_iUnion.mp this
    choose f hf using hx
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iInter.mpr fun k => hf k⟩

@[simp]
lemma ksJoin_cells [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    (ksJoin hT P n).cells = ksJoinCells P.cells T n := rfl

noncomputable def ksEntropySeq [Fintype ι] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  entropy μ (ksJoin hT P n).cells

@[simp]
lemma ksEntropySeq_zero [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropySeq hT P 0 = 0 := by
  rw [ksEntropySeq, ksJoin_cells, entropy_def]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [ksJoinCells_apply, Set.iInter_of_empty, measure_univ, ENNReal.toReal_one,
    Real.negMulLog_one]

lemma ksEntropySeq_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 ≤ ksEntropySeq hT P n :=
  entropy_nonneg μ _

lemma entropy_reindex [Fintype ι] {β : Type*} [Fintype β] (μ : Measure α) (e : ι ≃ β)
    (s : β → Set α) : entropy μ (fun i => s (e i)) = entropy μ s := by
  rw [entropy_def, entropy_def]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

omit [MeasurableSpace α] in

lemma ksJoinCells_append (cells : ι → Set α) (T : α → α) (n m : ℕ)
    (a : Fin n → ι) (b : Fin m → ι) :
    ksJoinCells cells T (n + m) (Fin.append a b)
      = ksJoinCells cells T n a ∩ (T^[n]) ⁻¹' ksJoinCells cells T m b := by
  
  rw [ksJoinCells_apply]
  rw [show (⋂ k : Fin (n + m), (T^[(k : ℕ)]) ⁻¹' cells (Fin.append a b k))
      = ⋂ s : Fin n ⊕ Fin m,
          (T^[((finSumFinEquiv s : Fin (n + m)) : ℕ)]) ⁻¹'
            cells (Fin.append a b (finSumFinEquiv s)) from
    Set.iInter_congr_of_surjective finSumFinEquiv.symm finSumFinEquiv.symm.surjective
      fun k => by rw [Equiv.apply_symm_apply]]
  rw [Set.iInter_sum]
  congr 1
  · 
    rw [ksJoinCells_apply]
    refine Set.iInter_congr fun i => ?_
    rw [finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.append_left]
  · 
    rw [ksJoinCells_apply, Set.preimage_iInter]
    refine Set.iInter_congr fun j => ?_
    rw [finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.append_right]
    
    rw [show (T^[n + (j : ℕ)]) = (T^[(j : ℕ)]) ∘ (T^[n]) by
      rw [← Function.iterate_add, Nat.add_comm], Set.preimage_comp]

private lemma ksEntropySeq_subadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n m : ℕ) :
    ksEntropySeq hT P (n + m) ≤ ksEntropySeq hT P n + ksEntropySeq hT P m := by
  
  set Q : MeasurePartition μ (Fin m → ι) := (ksJoin hT P m).pullback (hT.iterate n) with hQ
  
  have hreindex : ksEntropySeq hT P (n + m)
      = entropy μ (joinCells (ksJoin hT P n).cells Q.cells) := by
    rw [ksEntropySeq, ← entropy_reindex μ (Fin.appendEquiv n m) (ksJoin hT P (n + m)).cells,
      entropy_def, entropy_def]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨a, b⟩ := p
    have hcell : (ksJoin hT P (n + m)).cells (Fin.appendEquiv n m (a, b))
        = joinCells (ksJoin hT P n).cells Q.cells (a, b) := by
      simp only [ksJoin_cells, joinCells_apply, hQ, MeasurePartition.pullback_cells]
      exact ksJoinCells_append P.cells T n m a b
    rw [hcell]
  rw [hreindex, ksEntropySeq, ksEntropySeq]
  calc entropy μ (joinCells (ksJoin hT P n).cells Q.cells)
      ≤ entropy μ (ksJoin hT P n).cells + entropy μ Q.cells :=
        entropy_join_le (ksJoin hT P n) Q
    _ = entropy μ (ksJoin hT P n).cells + entropy μ (ksJoin hT P m).cells := by
        rw [hQ, entropy_pullback]

lemma ksSubadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    Subadditive (ksEntropySeq hT P) := fun k l => ksEntropySeq_subadditive hT P k l

private lemma Subadditive.lim_eq_of_eq {u v : ℕ → ℝ} (hu : Subadditive u) (hv : Subadditive v)
    (huv : u = v) : hu.lim = hv.lim := by
  subst huv; rfl

noncomputable def ksEntropyPartition [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) : ℝ :=
  (ksSubadditive hT P).lim

lemma tendsto_ksEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    Tendsto (fun n => ksEntropySeq hT P n / n) atTop (𝓝 (ksEntropyPartition hT P)) := by
  refine (ksSubadditive hT P).tendsto_lim ?_
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

@[simp]
private lemma ksEntropySeq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropySeq hT P 1 = entropy μ P.cells := by
  rw [ksEntropySeq, ksJoin_cells]
  have hcell : ∀ i : ι,
      ksJoinCells P.cells T 1 ((Equiv.funUnique (Fin 1) ι).symm i) = P.cells i := by
    intro i
    rw [ksJoinCells_apply]
    have hstep : ∀ k : Fin 1,
        (T^[(k : ℕ)]) ⁻¹' P.cells ((Equiv.funUnique (Fin 1) ι).symm i k) = P.cells i := by
      intro k
      rw [Equiv.funUnique_symm_apply, uniqueElim_const,
        show (k : ℕ) = 0 by omega, Function.iterate_zero, Set.preimage_id]
    rw [Set.iInter_congr hstep, Set.iInter_const]
  rw [← entropy_reindex μ (Equiv.funUnique (Fin 1) ι).symm (ksJoinCells P.cells T 1)]
  exact congrArg (entropy μ) (funext hcell)

private lemma ksEntropySeq_le_nsmul [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P n ≤ n • entropy μ P.cells := by
  induction n with
  | zero => simp
  | succ k IH =>
    calc ksEntropySeq hT P (k + 1)
        ≤ ksEntropySeq hT P k + ksEntropySeq hT P 1 := ksEntropySeq_subadditive hT P k 1
      _ ≤ k • entropy μ P.cells + entropy μ P.cells := by
          rw [ksEntropySeq_one]; gcongr
      _ = (k + 1) • entropy μ P.cells := by rw [succ_nsmul]

lemma ksEntropyPartition_le_entropy [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    ksEntropyPartition hT P ≤ entropy μ P.cells := by
  refine le_of_tendsto (tendsto_ksEntropySeq hT P) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn0]
  calc ksEntropySeq hT P n ≤ n • entropy μ P.cells := ksEntropySeq_le_nsmul hT P n
    _ = entropy μ P.cells * (n : ℝ) := by rw [nsmul_eq_mul, mul_comm]

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

variable (𝒜)

noncomputable def condKsEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  condEntropy μ 𝒜 (ksJoin hT P n).cells

private lemma condKsEntropySeq_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    0 ≤ condKsEntropySeq 𝒜 hT P n :=
  condEntropy_nonneg

@[simp]
private lemma condKsEntropySeq_zero [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condKsEntropySeq 𝒜 hT P 0 = 0 := by
  rw [condKsEntropySeq, condEntropy_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
  refine Finset.sum_eq_zero fun f _ => ?_
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  rw [ksJoin_cells, ksJoinCells_apply, Set.iInter_of_empty, measure_univ, ENNReal.toReal_one,
    Real.negMulLog_one]

@[simp]
private lemma condKsEntropySeq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condKsEntropySeq 𝒜 hT P 1 = condEntropy μ 𝒜 P.cells := by
  rw [condKsEntropySeq, ksJoin_cells]
  
  
  have hcell : ksJoinCells P.cells T 1 = fun f => P.cells (Equiv.funUnique (Fin 1) ι f) := by
    funext f
    rw [ksJoinCells_apply]
    have hstep : ∀ k : Fin 1,
        (T^[(k : ℕ)]) ⁻¹' P.cells (f k) = P.cells (Equiv.funUnique (Fin 1) ι f) := by
      intro k
      rw [show (k : ℕ) = 0 by omega, Function.iterate_zero, Set.preimage_id,
        Equiv.funUnique_apply, Subsingleton.elim k default]
    rw [Set.iInter_congr hstep, Set.iInter_const]
  rw [condEntropy_def, condEntropy_def, hcell]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) ι)
    (fun i => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)

variable {𝒜}

omit mα [StandardBorelSpace α] in

private lemma comap_iterate_le {T : α → α} (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) (n : ℕ) :
    MeasurableSpace.comap (T^[n]) 𝒜 ≤ 𝒜 := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, MeasurableSpace.comap_id, le_refl]
  | succ k IH =>
    rw [Function.iterate_succ', ← MeasurableSpace.comap_comp]
    exact (MeasurableSpace.comap_mono hinv).trans IH

private lemma condKsEntropySeq_subadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (n m : ℕ) :
    condKsEntropySeq 𝒜 hT P (n + m)
      ≤ condKsEntropySeq 𝒜 hT P n + condKsEntropySeq 𝒜 hT P m := by
  
  set Q : MeasurePartition μ (Fin m → ι) := (ksJoin hT P m).pullback (hT.iterate n) with hQ
  
  
  have hcell : ∀ p : (Fin n → ι) × (Fin m → ι),
      (ksJoin hT P (n + m)).cells (Fin.appendEquiv n m p)
        = joinCells (ksJoin hT P n).cells Q.cells p := by
    rintro ⟨a, b⟩
    simp only [ksJoin_cells, joinCells_apply, hQ, MeasurePartition.pullback_cells]
    exact ksJoinCells_append P.cells T n m a b
  have hreindex : condKsEntropySeq 𝒜 hT P (n + m)
      = condEntropy μ 𝒜 (joinCells (ksJoin hT P n).cells Q.cells) := by
    rw [condKsEntropySeq, condEntropy_def, condEntropy_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    refine (Equiv.sum_comp (Fin.appendEquiv n m)
      (fun g => Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω ((ksJoin hT P (n + m)).cells g)).toReal)).symm.trans ?_
    exact Finset.sum_congr rfl fun p _ => by rw [hcell p]
  
  have hcomap : MeasurableSpace.comap (T^[n]) 𝒜 ≤ 𝒜 := comap_iterate_le hinv n
  rw [hreindex, condKsEntropySeq, condKsEntropySeq]
  calc condEntropy μ 𝒜 (joinCells (ksJoin hT P n).cells Q.cells)
      ≤ condEntropy μ 𝒜 (ksJoin hT P n).cells + condEntropy μ 𝒜 Q.cells :=
        condEntropy_join_le hm (ksJoin hT P n) Q
    _ ≤ condEntropy μ 𝒜 (ksJoin hT P n).cells
          + condEntropy μ (MeasurableSpace.comap (T^[n]) 𝒜) Q.cells := by
        gcongr
        exact condEntropy_mono_of_le hcomap hm Q
    _ = condEntropy μ 𝒜 (ksJoin hT P n).cells + condEntropy μ 𝒜 (ksJoin hT P m).cells := by
        rw [hQ, MeasurePartition.pullback_cells,
          condEntropy_comap_pullback hm hT n (ksJoin hT P m)]

private lemma condKsSubadditive [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    Subadditive (condKsEntropySeq 𝒜 hT P) :=
  fun k l => condKsEntropySeq_subadditive hm hT hinv P k l

noncomputable def condKsEntropyPartition [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) : ℝ :=
  (condKsSubadditive hm hT hinv P).lim

lemma tendsto_condKsEntropySeq [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    Tendsto (fun n => condKsEntropySeq 𝒜 hT P n / n) atTop
      (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
  refine (condKsSubadditive hm hT hinv P).tendsto_lim ?_
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (condKsEntropySeq_nonneg 𝒜 hT P n) (Nat.cast_nonneg n)

private lemma condKsEntropySeq_le_nsmul [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) (n : ℕ) :
    condKsEntropySeq 𝒜 hT P n ≤ n • condEntropy μ 𝒜 P.cells := by
  induction n with
  | zero => simp
  | succ k IH =>
    calc condKsEntropySeq 𝒜 hT P (k + 1)
        ≤ condKsEntropySeq 𝒜 hT P k + condKsEntropySeq 𝒜 hT P 1 :=
          condKsEntropySeq_subadditive hm hT hinv P k 1
      _ ≤ k • condEntropy μ 𝒜 P.cells + condEntropy μ 𝒜 P.cells := by
          rw [condKsEntropySeq_one]; gcongr
      _ = (k + 1) • condEntropy μ 𝒜 P.cells := by rw [succ_nsmul]

lemma condKsEntropyPartition_nonneg [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    0 ≤ condKsEntropyPartition hm hT hinv P := by
  refine ge_of_tendsto (tendsto_condKsEntropySeq hm hT hinv P) ?_
  filter_upwards with n
  exact div_nonneg (condKsEntropySeq_nonneg 𝒜 hT P n) (Nat.cast_nonneg n)

lemma condKsEntropyPartition_le_condEntropy [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (P : MeasurePartition μ ι) :
    condKsEntropyPartition hm hT hinv P ≤ condEntropy μ 𝒜 P.cells := by
  refine le_of_tendsto (tendsto_condKsEntropySeq hm hT hinv P) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn0]
  calc condKsEntropySeq 𝒜 hT P n ≤ n • condEntropy μ 𝒜 P.cells :=
        condKsEntropySeq_le_nsmul hm hT hinv P n
    _ = condEntropy μ 𝒜 P.cells * (n : ℝ) := by rw [nsmul_eq_mul, mul_comm]

section Bot

variable {T : α → α}

end Bot

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} [MeasurableSpace α]

noncomputable def ksEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) : EReal :=
  ⨆ n : ℕ, ⨆ P : MeasurePartition μ (Fin n), ((ksEntropyPartition hT P : ℝ) : EReal)

lemma le_ksEntropy {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {n : ℕ} (P : MeasurePartition μ (Fin n)) :
    ((ksEntropyPartition hT P : ℝ) : EReal) ≤ ksEntropy hT :=
  le_trans (le_iSup (fun P : MeasurePartition μ (Fin n) =>
      ((ksEntropyPartition hT P : ℝ) : EReal)) P)
    (le_iSup (fun n : ℕ =>
      ⨆ P : MeasurePartition μ (Fin n), ((ksEntropyPartition hT P : ℝ) : EReal)) n)

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory

namespace D5.S3.Entropy.KolmogorovSinai

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {T : α → α} {S : β → β} {π : α → β}

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function

namespace D5.S3.Entropy.KolmogorovSinai

variable {α β : Type*} {ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def MeasurePartition.pulledBack [Fintype ι] {μ : Measure α} {ν : Measure β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (R : MeasurePartition ν ι) :
    MeasurePartition μ ι where
  cells := fun i => π ⁻¹' R.cells i
  measurable := fun i => (R.measurable i).preimage hπ.measurable
  aedisjoint := by
    intro i j hij
    simp only [onFun, AEDisjoint, ← Set.preimage_inter]
    rw [hπ.measure_preimage ((R.measurable i).inter (R.measurable j)).nullMeasurableSet]
    exact R.aedisjoint hij
  cover := by rw [← Set.preimage_iUnion, R.cover, Set.preimage_univ]

@[simp]
private lemma MeasurePartition.pulledBack_cells [Fintype ι] {μ : Measure α} {ν : Measure β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (R : MeasurePartition ν ι) :
    (R.pulledBack hπ).cells = fun i => π ⁻¹' R.cells i := rfl

omit [MeasurableSpace α] [MeasurableSpace β] in

private lemma ksJoinCells_pulledBack {T : α → α} {S : β → β} {π : α → β}
    (hπS : π ∘ T = S ∘ π) (R : ι → Set β) (n : ℕ) (f : Fin n → ι) :
    ksJoinCells (fun i => π ⁻¹' R i) T n f = π ⁻¹' ksJoinCells R S n f := by
  
  have hsemi : Function.Semiconj π T S := Function.semiconj_iff_comp_eq.mpr hπS
  rw [ksJoinCells_apply, ksJoinCells_apply, Set.preimage_iInter]
  refine Set.iInter_congr fun k => ?_
  
  rw [← Set.preimage_comp, ← Set.preimage_comp, (hsemi.iterate_right (k : ℕ)).comp_eq]

variable [Fintype ι]

theorem factor_relative_eq {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β} {π : α → β}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hπ : MeasurePreserving π μ ν) (hπS : π ∘ T = S ∘ π) (R : MeasurePartition ν ι) :
    ksEntropyPartition hT (R.pulledBack hπ) = ksEntropyPartition hS R := by
  rw [ksEntropyPartition, ksEntropyPartition]
  refine Subadditive.lim_eq_of_eq _ _ (funext fun n => ?_)
  
  rw [ksEntropySeq, ksEntropySeq, ksJoin_cells, ksJoin_cells, entropy_def, entropy_def]
  refine Finset.sum_congr rfl fun f _ => ?_
  
  rw [MeasurePartition.pulledBack_cells, ksJoinCells_pulledBack hπS R.cells n f]
  rw [hπ.measure_preimage]
  exact ((ksJoin hS R n).measurable f).nullMeasurableSet

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]

theorem entropy_joinCells_of_refines [Fintype ι] [Fintype κ] {μ : Measure α}
    (s : ι → Set α) (hs_meas : ∀ i, MeasurableSet (s i))
    (hs_disj : Pairwise (AEDisjoint μ on s)) (t : κ → Set α)
    (g : κ → ι) (hrefine : ∀ j, t j ≤ᵐ[μ] s (g j)) :
    entropy μ (joinCells s t) = entropy μ t := by
  rw [entropy_def, entropy_def]
  
  rw [show (∑ x, Real.negMulLog (μ (joinCells s t x)).toReal)
      = ∑ j, ∑ i, Real.negMulLog (μ (s i ∩ t j)).toReal from by
        rw [Fintype.sum_prod_type_right]; rfl]
  refine Finset.sum_congr rfl fun j _ => ?_
  
  
  have hdiff : μ (t j \ s (g j)) = 0 := by
    have := (hrefine j)
    rwa [ae_le_set] at this
  have hdiag : μ (s (g j) ∩ t j) = μ (t j) := by
    
    have hsplit := measure_inter_add_diff (μ := μ) (t j) (hs_meas (g j))
    rw [hdiff, add_zero] at hsplit
    rw [Set.inter_comm]; exact hsplit
  have hoff : ∀ i, i ≠ g j → μ (s i ∩ t j) = 0 := by
    intro i hi
    
    have hnull : μ (s i ∩ s (g j)) = 0 := hs_disj hi
    
    have hsub : (s i ∩ t j : Set α) ⊆ (s i ∩ s (g j)) ∪ (t j \ s (g j)) := by
      intro x hx
      by_cases hmem : x ∈ s (g j)
      · exact Or.inl ⟨hx.1, hmem⟩
      · exact Or.inr ⟨hx.2, hmem⟩
    exact measure_mono_null hsub (measure_union_null hnull hdiff)
  
  rw [show (∑ i, Real.negMulLog (μ (s i ∩ t j)).toReal)
      = Real.negMulLog (μ (s (g j) ∩ t j)).toReal from ?_]
  · rw [hdiag]
  · rw [Finset.sum_eq_single (g j)]
    · intro i _ hi; rw [hoff i hi]; simp
    · intro h; exact absurd (Finset.mem_univ (g j)) h

private theorem entropy_join_eq_of_refines [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (B : MeasurePartition μ ι) (A : MeasurePartition μ κ)
    (g : κ → ι) (hrefine : ∀ f, A.cells f ≤ᵐ[μ] B.cells (g f)) :
    entropy μ A.cells
      = entropy μ B.cells + condEntropyGivenPartition μ B.cells A.cells := by
  rw [← entropy_join_eq_add_condEntropyGivenPartition B A,
    entropy_joinCells_of_refines B.cells B.measurable B.aedisjoint A.cells g hrefine]

variable {μ : Measure α} [IsProbabilityMeasure μ] [StandardBorelSpace α]
variable {T : α → α}

noncomputable def condCellSeq [Fintype ι] [Fintype κ]
    (hT : MeasurePreserving T μ μ) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι) (n : ℕ) :
    ℝ :=
  condEntropyGivenPartition μ (ksJoin hT Q n).cells (ksJoin hT P n).cells

theorem abramovRokhlin_partition_of_W3 [Fintype ι] [Fintype κ]
    (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜)
    (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (g : ∀ n, (Fin n → ι) → (Fin n → κ))
    (hrefine : ∀ n f, (ksJoin hT P n).cells f ≤ᵐ[μ] (ksJoin hT Q n).cells (g n f))
    (hW3 : Tendsto (fun n => condCellSeq hT Q P n / n) atTop
        (𝓝 (condKsEntropyPartition hm hT hinv P))) :
    ksEntropyPartition hT P
      = ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P := by
  
  have hpern : ∀ n, ksEntropySeq hT P n = ksEntropySeq hT Q n + condCellSeq hT Q P n := fun n =>
    entropy_join_eq_of_refines (ksJoin hT Q n) (ksJoin hT P n) (g n) (hrefine n)
  
  have hdiv : (fun n => ksEntropySeq hT P n / n)
      = fun n => ksEntropySeq hT Q n / n + condCellSeq hT Q P n / n := by
    funext n; rw [hpern n, add_div]
  
  have hA : Tendsto (fun n => ksEntropySeq hT P n / n) atTop (𝓝 (ksEntropyPartition hT P)) :=
    tendsto_ksEntropySeq hT P
  
  have hRHS : Tendsto (fun n => ksEntropySeq hT Q n / n + condCellSeq hT Q P n / n) atTop
      (𝓝 (ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P)) :=
    (tendsto_ksEntropySeq hT Q).add hW3
  
  exact tendsto_nhds_unique (hdiv ▸ hA) hRHS

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function MeasurableSpace

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [Fintype ι]

@[reducible]
def generatedSigmaAlgebra (μ : Measure α) (P : MeasurePartition μ ι) : MeasurableSpace α :=
  MeasurableSpace.generateFrom (Set.range P.cells)

def IsGenerating (μ : Measure α) (T : α → α) (P : MeasurePartition μ ι) : Prop :=
  (⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (generatedSigmaAlgebra μ P)) = mα

end D5.S3.Entropy.KolmogorovSinai


