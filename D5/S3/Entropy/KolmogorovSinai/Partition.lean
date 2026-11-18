/- GID: D5/S3/Entropy/KolmogorovSinai/Partition
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/Partition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov-Sinai partition for the full-shift equilibrium proof. -/

/- Copyright (c) 2026 Marcel Morgenstern. Licensed under Apache-2.0.
   Selected source port of marcmorningstar/lean4-ergodic-theory,
   revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f.
   Attribution, source mapping and full license: Library/Entropy/morgenstern2026ks.md.
   Adaptation: current Lean APIs, subject namespaces and live-dependency pruning.
   Retire each ported declaration when an equivalent declaration exists in this
   repository's pinned mathlib revision, replacing consumers by direct imports. -/

import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.PiNat
/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.EntropyEquality
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Martingale.Convergence



open MeasureTheory Function

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

noncomputable def entropy [Fintype ι] (μ : Measure α) (s : ι → Set α) : ℝ :=
  ∑ i, Real.negMulLog (μ (s i)).toReal

@[simp]
lemma entropy_def [Fintype ι] (μ : Measure α) (s : ι → Set α) :
    entropy μ s = ∑ i, Real.negMulLog (μ (s i)).toReal := rfl

structure MeasurePartition (μ : Measure α) (ι : Type*) [Fintype ι] where
  
  cells : ι → Set α
  
  measurable : ∀ i, MeasurableSet (cells i)
  
  aedisjoint : Pairwise (AEDisjoint μ on cells)
  
  cover : ⋃ i, cells i = Set.univ

lemma entropy_nonneg [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ] (s : ι → Set α) :
    0 ≤ entropy μ s := by
  rw [entropy_def]
  refine Finset.sum_nonneg fun i _ => ?_
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s i))
  rwa [ENNReal.toReal_one] at h

lemma entropy_le_log_card [Fintype ι] [Nonempty ι] (μ : Measure α) (s : ι → Set α)
    (hsum : ∑ i, (μ (s i)).toReal = 1) :
    entropy μ s ≤ Real.log (Fintype.card ι) :=
  D5.S3.Entropy.MaxEntropy.entropy_le_log_card _ ⟨fun _ => ENNReal.toReal_nonneg, hsum⟩

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

lemma MeasurePartition.sum_toReal_measure_eq_one [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) :
    ∑ i, (μ (P.cells i)).toReal = 1 := by
  have hadd : μ (⋃ i ∈ (Finset.univ : Finset ι), P.cells i) = ∑ i, μ (P.cells i) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij => P.aedisjoint hij)
      (fun i _ => (P.measurable i).nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true] at hadd
  rw [P.cover, measure_univ] at hadd
  have hfin : ∀ i, μ (P.cells i) ≠ ⊤ := fun i => measure_ne_top μ (P.cells i)
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hadd, ENNReal.toReal_one]

lemma entropy_le_log_card_partition [Fintype ι] [Nonempty ι] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) :
    entropy μ P.cells ≤ Real.log (Fintype.card ι) :=
  entropy_le_log_card μ P.cells P.sum_toReal_measure_eq_one

def joinCells (s : ι → Set α) (t : κ → Set α) : ι × κ → Set α :=
  fun p => s p.1 ∩ t p.2

omit [MeasurableSpace α] in
@[simp]
lemma joinCells_apply (s : ι → Set α) (t : κ → Set α) (p : ι × κ) :
    joinCells s t p = s p.1 ∩ t p.2 := rfl

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

lemma MeasurePartition.measure_eq_sum_inter [Fintype κ] {μ : Measure α}
    (Q : MeasurePartition μ κ) {A : Set α} (hA : MeasurableSet A) :
    μ A = ∑ j, μ (A ∩ Q.cells j) := by
  have hcover : A = ⋃ j ∈ (Finset.univ : Finset κ), A ∩ Q.cells j := by
    simp only [Finset.mem_univ, Set.iUnion_true, ← Set.inter_iUnion, Q.cover, Set.inter_univ]
  have hadd : μ (⋃ j ∈ (Finset.univ : Finset κ), A ∩ Q.cells j) = ∑ j, μ (A ∩ Q.cells j) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij =>
        AEDisjoint.mono (Q.aedisjoint hij) Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => (hA.inter (Q.measurable j)).nullMeasurableSet)
  rw [← hadd, ← hcover]

private lemma sum_negMulLog_le {ω : Type*} [Fintype ω] (p q : ω → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i ≤ 1)
    (hac : ∀ i, p i ≠ 0 → q i ≠ 0) :
    ∑ i, Real.negMulLog (p i) ≤ - ∑ i, p i * Real.log (q i) := by
  
  have hkey : ∀ i, Real.negMulLog (p i) + p i * Real.log (q i) ≤ q i - p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · 
      simp only [← hpi, Real.negMulLog_zero, zero_mul, add_zero, sub_zero]
      exact hq i
    · 
      have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm (hac i (ne_of_gt hpi)))
      have hdiv : 0 < q i / p i := div_pos hqi hpi
      have hlog := Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt hpi)] at hlog
      have hmul : p i * (Real.log (q i) - Real.log (p i)) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
      have hcancel : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rw [hcancel] at hmul
      simp only [Real.negMulLog, neg_mul]
      nlinarith [hmul]
  have hsum : ∑ i, (Real.negMulLog (p i) + p i * Real.log (q i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum (fun i _ => hkey i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hpsum] at hsum
  linarith [hsum]

lemma entropy_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ (joinCells P.cells Q.cells) ≤ entropy μ P.cells + entropy μ Q.cells := by
  
  let a : ι → ℝ := fun i => (μ (P.cells i)).toReal
  let b : κ → ℝ := fun j => (μ (Q.cells j)).toReal
  let p : ι × κ → ℝ := fun x => (μ (P.cells x.1 ∩ Q.cells x.2)).toReal
  let q : ι × κ → ℝ := fun x => a x.1 * b x.2
  
  have hrow : ∀ i, ∑ j, p (i, j) = a i := fun i => by
    change ∑ j, (μ (P.cells i ∩ Q.cells j)).toReal = (μ (P.cells i)).toReal
    rw [Q.measure_eq_sum_inter (P.measurable i),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  have hcol : ∀ j, ∑ i, p (i, j) = b j := fun j => by
    change ∑ i, (μ (P.cells i ∩ Q.cells j)).toReal = (μ (Q.cells j)).toReal
    rw [P.measure_eq_sum_inter (Q.measurable j),
      ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
    exact Finset.sum_congr rfl fun i _ => by rw [Set.inter_comm]
  
  have hasum : ∑ i, a i = 1 := P.sum_toReal_measure_eq_one
  have hbsum : ∑ j, b j = 1 := Q.sum_toReal_measure_eq_one
  
  have hpsum : ∑ x, p x = 1 := by
    rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hasum
  
  have hqsum : ∑ x, q x = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ i j, q (i, j) = a i * b j from fun _ _ => rfl, ← Finset.mul_sum, hbsum,
      mul_one, hasum]
  
  have hpnn : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hann : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hbnn : ∀ j, 0 ≤ b j := fun _ => ENNReal.toReal_nonneg
  have hqnn : ∀ x, 0 ≤ q x := fun x => mul_nonneg (hann x.1) (hbnn x.2)
  
  have hac : ∀ x, p x ≠ 0 → q x ≠ 0 := by
    rintro ⟨i, j⟩ hpx
    have hμ : μ (P.cells i ∩ Q.cells j) ≠ 0 := (ENNReal.toReal_ne_zero.mp hpx).1
    have hpos : 0 < μ (P.cells i ∩ Q.cells j) := pos_iff_ne_zero.mpr hμ
    have ha_pos : 0 < a i :=
      ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le hpos (measure_mono Set.inter_subset_left))) (measure_ne_top μ _)
    have hb_pos : 0 < b j :=
      ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le hpos (measure_mono Set.inter_subset_right))) (measure_ne_top μ _)
    exact ne_of_gt (mul_pos ha_pos hb_pos)
  
  have hgibbs := sum_negMulLog_le p q hpnn hqnn hpsum (le_of_eq hqsum) hac
  
  have hLHS : ∑ x, Real.negMulLog (p x) = entropy μ (joinCells P.cells Q.cells) := by
    rw [entropy_def]; exact Finset.sum_congr rfl fun x _ => by rw [joinCells_apply]
  
  have hexpand : ∀ x : ι × κ, p x * Real.log (q x)
      = p x * Real.log (a x.1) + p x * Real.log (b x.2) := by
    rintro ⟨i, j⟩
    rcases eq_or_lt_of_le (hpnn (i, j)) with hpi | hpi
    · simp only [← hpi, zero_mul, add_zero]
    · obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.mp (hac (i, j) (ne_of_gt hpi))
      change p (i, j) * Real.log (a i * b j) = _
      rw [Real.log_mul ha0 hb0, mul_add]
  
  have hA : ∑ x, p x * Real.log (a x.1) = - entropy μ P.cells := by
    rw [Fintype.sum_prod_type, entropy_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, p (i, j) * Real.log (a i) = (∑ j, p (i, j)) * Real.log (a i) :=
      (Finset.sum_mul ..).symm
    rw [this, hrow, Real.negMulLog]
    change (μ (P.cells i)).toReal * Real.log (μ (P.cells i)).toReal = _
    ring
  
  have hB : ∑ x, p x * Real.log (b x.2) = - entropy μ Q.cells := by
    rw [Fintype.sum_prod_type_right, entropy_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∑ i, p (i, j) * Real.log (b j) = (∑ i, p (i, j)) * Real.log (b j) :=
      (Finset.sum_mul ..).symm
    rw [this, hcol, Real.negMulLog]
    change (μ (Q.cells j)).toReal * Real.log (μ (Q.cells j)).toReal = _
    ring
  have hRHS : - ∑ x, p x * Real.log (q x) = entropy μ P.cells + entropy μ Q.cells := by
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, hA, hB]; ring
  rw [hLHS, hRHS] at hgibbs
  exact hgibbs

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

noncomputable def condEntropy {mΩ : MeasurableSpace α} [Fintype ι] [StandardBorelSpace α]
    (μ : @Measure α mΩ) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α) : ℝ :=
  ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mΩ _ μ _ 𝒜 ω (s i)).toReal) ∂μ

omit mα [StandardBorelSpace α] in
@[simp]
lemma condEntropy_def {mΩ : MeasurableSpace α} [Fintype ι] [StandardBorelSpace α]
    (μ : @Measure α mΩ) [IsFiniteMeasure μ] (𝒜 : MeasurableSpace α) (s : ι → Set α) :
    condEntropy μ 𝒜 s
      = ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mΩ _ μ _ 𝒜 ω (s i)).toReal) ∂μ := rfl

private lemma toReal_condExpKernel_le_one {μ : Measure α} [IsFiniteMeasure μ] (A : Set α) (ω : α) :
    (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal ≤ 1 := by
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := @condExpKernel α mα _ μ _ 𝒜 ω) (s := A))
  rwa [ENNReal.toReal_one] at h

lemma negMulLog_condExpKernel_sum_nonneg [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]
    (s : ι → Set α) (ω : α) :
    0 ≤ ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (s i)).toReal :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg ENNReal.toReal_nonneg (toReal_condExpKernel_le_one (s i) ω)

lemma condEntropy_nonneg [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ] {s : ι → Set α} :
    0 ≤ condEntropy μ 𝒜 s := by
  rw [condEntropy_def]
  exact integral_nonneg fun ω => negMulLog_condExpKernel_sum_nonneg s ω

lemma integrable_negMulLog_condExpKernel {μ : Measure α} [IsFiniteMeasure μ] (h𝒜 : 𝒜 ≤ mα)
    {A : Set α} (hA : MeasurableSet A) :
    Integrable (fun ω => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal) μ := by
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal) μ := by
    have h1 : Measurable[mα] fun ω => @condExpKernel α mα _ μ _ 𝒜 ω A :=
      (measurable_condExpKernel hA).mono h𝒜 le_rfl
    exact Real.continuous_negMulLog.comp_aestronglyMeasurable
      h1.ennreal_toReal.aestronglyMeasurable
  refine Integrable.of_bound hmeas 1 (Eventually.of_forall fun ω => ?_)
  have h01 : (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal ≤ 1 := toReal_condExpKernel_le_one A ω
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.negMulLog_nonneg ENNReal.toReal_nonneg h01)]
  calc Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal
      ≤ 1 - (@condExpKernel α mα _ μ _ 𝒜 ω A).toReal :=
        Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg
    _ ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := @condExpKernel α mα _ μ _ 𝒜 ω A)]

lemma integrable_condEntropy_integrand [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    Integrable (fun ω => ∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (s i)).toReal) μ :=
  integrable_finsetSum _ fun i _ => integrable_negMulLog_condExpKernel h𝒜 (hs i)

lemma condExpKernel_sum_toReal_measure_eq_one [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    ∀ᵐ ω ∂μ, ∑ i, (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal = 1 := by
  
  
  have hdisj : ∀ᵐ ω ∂μ, ∀ i j, i ≠ j →
      @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ P.cells j) = 0 := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    refine eventually_imp_distrib_left.2 fun hij => ?_
    
    have hμ0 : μ (P.cells i ∩ P.cells j) = 0 := P.aedisjoint hij
    have hμ : ∀ᵐ ω ∂μ, ω ∉ P.cells i ∩ P.cells j := by
      rw [ae_iff]; simpa using hμ0
    have hμ2 : ∀ᵐ ω ∂(@condExpKernel α mα _ μ _ 𝒜 ∘ₘ μ.trim h𝒜),
        ω ∉ P.cells i ∩ P.cells j := by
      rw [condExpKernel_comp_trim h𝒜]; exact hμ
    have hae := Measure.ae_ae_of_ae_comp hμ2
    refine ae_of_ae_trim h𝒜 ?_
    filter_upwards [hae] with ω hω
    simpa using ae_iff.mp hω
  filter_upwards [hdisj] with ω hω
  
  have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
    IsMarkovKernel.isProbabilityMeasure ω
  have hadd : @condExpKernel α mα _ μ _ 𝒜 ω (⋃ i ∈ (Finset.univ : Finset ι), P.cells i)
      = ∑ i, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i) :=
    measure_biUnion_finset₀
      (fun i _ j _ hij => hω i j hij)
      (fun i _ => (P.measurable i).nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true] at hadd
  rw [P.cover, measure_univ] at hadd
  have hfin : ∀ i, @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i) ≠ ⊤ :=
    fun i => measure_ne_top _ (P.cells i)
  rw [← ENNReal.toReal_sum (fun i _ => hfin i), ← hadd, ENNReal.toReal_one]

lemma condEntropy_le_log_card [Fintype ι] [Nonempty ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    condEntropy μ 𝒜 P.cells ≤ Real.log (Fintype.card ι) := by
  rw [condEntropy_def]
  have hbound : ∀ᵐ ω ∂μ,
      (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)
        ≤ Real.log (Fintype.card ι) := by
    filter_upwards [condExpKernel_sum_toReal_measure_eq_one h𝒜 P] with ω hω
    have := entropy_le_log_card (μ := @condExpKernel α mα _ μ _ 𝒜 ω) P.cells hω
    rwa [entropy_def] at this
  calc
    ∫ ω, (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal) ∂μ
        ≤ ∫ _ω, Real.log (Fintype.card ι) ∂μ :=
          integral_mono_ae
            (integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i))
            (integrable_const _) hbound
    _ = Real.log (Fintype.card ι) := by
          rw [integral_const, probReal_univ, one_smul]

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

private lemma condExpKernel_pairwise_aedisjoint [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) :
    ∀ᵐ ω ∂μ, Pairwise (AEDisjoint (@condExpKernel α mα _ μ _ 𝒜 ω) on P.cells) := by
  have hdisj : ∀ᵐ ω ∂μ, ∀ i j, i ≠ j →
      @condExpKernel α mα _ μ _ 𝒜 ω (P.cells i ∩ P.cells j) = 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    refine eventually_imp_distrib_left.2 fun hij => ?_
    have hμ0 : μ (P.cells i ∩ P.cells j) = 0 := P.aedisjoint hij
    have hμ : ∀ᵐ ω ∂μ, ω ∉ P.cells i ∩ P.cells j := by
      rw [ae_iff]; simpa using hμ0
    have hμ2 : ∀ᵐ ω ∂(@condExpKernel α mα _ μ _ 𝒜 ∘ₘ μ.trim h𝒜),
        ω ∉ P.cells i ∩ P.cells j := by
      rw [condExpKernel_comp_trim h𝒜]; exact hμ
    have hae := Measure.ae_ae_of_ae_comp hμ2
    refine ae_of_ae_trim h𝒜 ?_
    filter_upwards [hae] with ω hω
    simpa using ae_iff.mp hω
  filter_upwards [hdisj] with ω hω i j hij
  exact hω i j hij

lemma condEntropy_join_le [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (h𝒜 : 𝒜 ≤ mα) (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    condEntropy μ 𝒜 (joinCells P.cells Q.cells)
      ≤ condEntropy μ 𝒜 P.cells + condEntropy μ 𝒜 Q.cells := by
  rw [condEntropy_def, condEntropy_def, condEntropy_def,
    ← integral_add (integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i))
      (integrable_condEntropy_integrand h𝒜 Q.cells (fun j => Q.measurable j))]
  
  have hbound : ∀ᵐ ω ∂μ,
      (∑ x, Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 ω ((joinCells P.cells Q.cells) x)).toReal)
        ≤ (∑ i, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (P.cells i)).toReal)
          + ∑ j, Real.negMulLog (@condExpKernel α mα _ μ _ 𝒜 ω (Q.cells j)).toReal := by
    filter_upwards [condExpKernel_pairwise_aedisjoint h𝒜 P,
      condExpKernel_pairwise_aedisjoint h𝒜 Q] with ω hPd hQd
    
    have : IsProbabilityMeasure (@condExpKernel α mα _ μ _ 𝒜 ω) :=
      IsMarkovKernel.isProbabilityMeasure ω
    let Pω : MeasurePartition (@condExpKernel α mα _ μ _ 𝒜 ω) ι :=
      { cells := P.cells, measurable := P.measurable, aedisjoint := hPd, cover := P.cover }
    let Qω : MeasurePartition (@condExpKernel α mα _ μ _ 𝒜 ω) κ :=
      { cells := Q.cells, measurable := Q.measurable, aedisjoint := hQd, cover := Q.cover }
    have hjoin := entropy_join_le Pω Qω
    rw [entropy_def, entropy_def, entropy_def] at hjoin
    exact hjoin
  
  exact integral_mono_ae
    (integrable_condEntropy_integrand h𝒜 (joinCells P.cells Q.cells)
      (fun x => (P.measurable x.1).inter (Q.measurable x.2)))
    ((integrable_condEntropy_integrand h𝒜 P.cells (fun i => P.measurable i)).add
      (integrable_condEntropy_integrand h𝒜 Q.cells (fun j => Q.measurable j)))
    hbound

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter ProbabilityTheory Finset
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]

private lemma sum_negMulLog_row [Fintype κ] (r : κ → ℝ) (a : ℝ) (ha : a ≠ 0)
    (hrow : ∑ j, r j = a) :
    ∑ j, Real.negMulLog (r j)
      = Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
  
  have hcsum : ∑ j, (r j / a) = 1 := by
    rw [← Finset.sum_div, hrow, div_self ha]
  have hstep : ∀ j, Real.negMulLog (r j)
      = (r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a) := by
    intro j
    have hrw : a * (r j / a) = r j := by field_simp
    calc Real.negMulLog (r j)
        = Real.negMulLog (a * (r j / a)) := by rw [hrw]
      _ = (r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a) := Real.negMulLog_mul _ _
  calc ∑ j, Real.negMulLog (r j)
      = ∑ j, ((r j / a) * Real.negMulLog a + a * Real.negMulLog (r j / a)) := by
        exact Finset.sum_congr rfl fun j _ => hstep j
    _ = (∑ j, (r j / a)) * Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = Real.negMulLog a + a * ∑ j, Real.negMulLog (r j / a) := by
        rw [hcsum, one_mul]

noncomputable def condEntropyOnCell [Fintype κ] (μ : Measure α) (sᵢ : Set α)
    (t : κ → Set α) : ℝ :=
  ∑ j, Real.negMulLog ((μ (sᵢ ∩ t j)).toReal / (μ sᵢ).toReal)

noncomputable def condEntropyGivenPartition [Fintype ι] [Fintype κ] (μ : Measure α)
    (s : ι → Set α) (t : κ → Set α) : ℝ :=
  ∑ i, (μ (s i)).toReal * condEntropyOnCell μ (s i) t

theorem entropy_join_eq_add_condEntropyGivenPartition [Fintype ι] [Fintype κ] {μ : Measure α}
    [IsProbabilityMeasure μ] (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ (joinCells P.cells Q.cells)
      = entropy μ P.cells + condEntropyGivenPartition μ P.cells Q.cells := by
  rw [entropy_def, entropy_def, condEntropyGivenPartition]
  
  rw [show (∑ x, Real.negMulLog (μ (joinCells P.cells Q.cells x)).toReal)
      = ∑ i, ∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal from by
        rw [Fintype.sum_prod_type]; rfl]
  
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  
  set a : ℝ := (μ (P.cells i)).toReal with ha
  set r : κ → ℝ := fun j => (μ (P.cells i ∩ Q.cells j)).toReal with hr
  rcases eq_or_ne a 0 with ha0 | ha0
  · 
    have ha0' : (μ (P.cells i)).toReal = 0 := by rw [← ha]; exact ha0
    have hμ0 : μ (P.cells i) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (μ (P.cells i))).mp ha0' with h | h
      · exact h
      · exact absurd h (measure_ne_top μ _)
    have hrow0 : ∀ j, r j = 0 := by
      intro j
      have hz : μ (P.cells i ∩ Q.cells j) = 0 := measure_mono_null Set.inter_subset_left hμ0
      simp only [hr, hz, ENNReal.toReal_zero]
    have hLHS : ∑ j, Real.negMulLog (r j) = 0 := by
      simp only [hrow0, Real.negMulLog_zero, Finset.sum_const_zero]
    rw [show (∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal)
        = ∑ j, Real.negMulLog (r j) from rfl, hLHS, ha0]
    simp only [Real.negMulLog_zero, zero_mul, add_zero]
  · 
    have hrow : ∑ j, r j = a := by
      simp only [hr, ha]
      rw [Q.measure_eq_sum_inter (P.measurable i),
        ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
    have hchain := sum_negMulLog_row r a ha0 hrow
    have hcell : (∑ j, Real.negMulLog (r j / a))
        = condEntropyOnCell μ (P.cells i) Q.cells := by
      simp only [condEntropyOnCell, hr, ha]
    rw [show (∑ j, Real.negMulLog (μ (P.cells i ∩ Q.cells j)).toReal)
        = ∑ j, Real.negMulLog (r j) from rfl, hchain, hcell]

section Conditional

variable [StandardBorelSpace α]

end Conditional

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

section Helpers

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

private theorem measurableSet_preimage_of_measurePreserving
    (hT : MeasurePreserving T μ μ) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (T ⁻¹' B) :=
  hT.measurable hB

private theorem integrable_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => f (T ω)) μ :=
  Integrable.comp_measurable (by rwa [hT.map_eq]) hT.measurable

private theorem integral_comp_self
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫ ω, f (T ω) ∂μ = ∫ ω, f ω ∂μ := by
  rw [← integral_map (φ := T) hT.measurable.aemeasurable (hf.mono_ac (by rw [hT.map_eq])),
    hT.map_eq]

private theorem setIntegral_comp_preimage
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {A' : Set Ω} (hA' : MeasurableSet A') :
    ∫ ω in T ⁻¹' A', f (T ω) ∂μ = ∫ ω in A', f ω ∂μ := by
  rw [← integral_indicator (hT.measurable hA'), ← integral_indicator hA']
  have hcomp : (T ⁻¹' A').indicator (fun ω => f (T ω))
      = fun ω => (A'.indicator f) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ A'
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  rw [hcomp]
  exact integral_comp_self hT (hf.indicator hA')

end Helpers

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} {𝒜 : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α]

section JointPullback

variable {T : α → α}

omit [StandardBorelSpace α] in

private theorem condExp_indicator_preimage_comap {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ)
    {B : Set α} (hB : @MeasurableSet α mα B) :
    (μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) := by
  classical
  
  have hcm : MeasurableSpace.comap T 𝒜 ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ hS.measurable (hm A' hA')
  
  have hSA : @Measurable α α (MeasurableSpace.comap T 𝒜) 𝒜 T :=
    fun A' hA' => ⟨A', hA', rfl⟩
  have hTB : @MeasurableSet α mα (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mα) hS hB
  
  have hind : Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))
      = fun ω => Set.indicator B (fun _ => (1 : ℝ)) (T ω) := by
    funext ω
    by_cases hω : T ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [Set.mem_preimage])]
  have hfintB : Integrable (Set.indicator B (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hfintTB : Integrable (Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hTB
  
  set g : α → ℝ := fun ω => (μ⟦B | 𝒜⟧) (T ω) with hg
  have hgSM : StronglyMeasurable[MeasurableSpace.comap T 𝒜] g :=
    (stronglyMeasurable_condExp).comp_measurable hSA
  have hgint : Integrable g μ := integrable_comp_self (mΩ := mα) hS integrable_condExp
  have : SigmaFinite (μ.trim hcm) := inferInstance
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hcm hfintTB
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hgSM.aestronglyMeasurable
  
  obtain ⟨A', hA'mem, hA'eq⟩ := hs
  have hA'meas : @MeasurableSet α mα A' := hm A' hA'mem
  
  have hL : ∫ ω in s, g ω ∂μ = ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ := by
    rw [← hA'eq, hg]
    exact setIntegral_comp_preimage (mΩ := mα) hS
      integrable_condExp.aestronglyMeasurable hA'meas
  
  have hcond : ∫ ω in A', (μ⟦B | 𝒜⟧) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ :=
    setIntegral_condExp hm hfintB hA'mem
  
  have hR : ∫ ω in s, Set.indicator (T ⁻¹' B) (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in A', Set.indicator B (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [← hA'eq, hind]
    exact setIntegral_comp_preimage (mΩ := mα) hS hfintB.aestronglyMeasurable hA'meas
  rw [hL, hcond, hR]

private theorem condExpKernel_preimage_comap_toReal_ae_eq {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ)
    {B : Set α} (hB : @MeasurableSet α mα B) :
    (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal := by
  have hcm : MeasurableSpace.comap T 𝒜 ≤ mα := fun s ⟨A', hA', hA'eq⟩ =>
    hA'eq ▸ hS.measurable (hm A' hA')
  have hTB : @MeasurableSet α mα (T ⁻¹' B) :=
    measurableSet_preimage_of_measurePreserving (mΩ := mα) hS hB
  
  have h1 : (fun ω => (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' B)).toReal)
      =ᵐ[μ] μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hcm hTB
  
  have h2 : (μ⟦T ⁻¹' B | MeasurableSpace.comap T 𝒜⟧) =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    condExp_indicator_preimage_comap hm hS hB
  
  have h3 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 ω B).toReal) =ᵐ[μ] μ⟦B | 𝒜⟧ := by
    simpa only [measureReal_def] using condExpKernel_ae_eq_condExp hm hB
  have h4 : (fun ω => (@condExpKernel α mα _ μ _ 𝒜 (T ω) B).toReal)
      =ᵐ[μ] fun ω => (μ⟦B | 𝒜⟧) (T ω) :=
    hS.quasiMeasurePreserving.ae_eq_comp h3
  exact (h1.trans h2).trans h4.symm

private theorem condEntropy_comap_preimage [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hS : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) :
    condEntropy μ (MeasurableSpace.comap T 𝒜) (fun i => T ⁻¹' P.cells i)
      = condEntropy μ 𝒜 P.cells := by
  rw [condEntropy_def, condEntropy_def]
  
  have hae : (fun ω => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' P.cells i)).toReal)
      =ᵐ[μ] fun ω => (fun ω' => ∑ i, Real.negMulLog
        (@condExpKernel α mα _ μ _ 𝒜 ω' (P.cells i)).toReal) (T ω) := by
    have hcell : ∀ i, (fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ (MeasurableSpace.comap T 𝒜) ω (T ⁻¹' P.cells i)).toReal)
        =ᵐ[μ] fun ω => Real.negMulLog
          (@condExpKernel α mα _ μ _ 𝒜 (T ω) (P.cells i)).toReal := by
      intro i
      filter_upwards [condExpKernel_preimage_comap_toReal_ae_eq hm hS (P.measurable i)]
        with ω hω
      rw [hω]
    filter_upwards [ae_all_iff.2 hcell] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  rw [integral_congr_ae hae]
  
  exact integral_comp_self (mΩ := mα) hS
    (integrable_condEntropy_integrand hm P.cells (fun i => P.measurable i)).aestronglyMeasurable

theorem condEntropy_comap_pullback [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    (hm : 𝒜 ≤ mα) (hT : @MeasurePreserving α α mα mα T μ μ) (n : ℕ)
    (P : MeasurePartition μ ι) :
    condEntropy μ (MeasurableSpace.comap (T^[n]) 𝒜) (fun i => (T^[n]) ⁻¹' P.cells i)
      = condEntropy μ 𝒜 P.cells :=
  condEntropy_comap_preimage hm (hT.iterate n) P

end JointPullback

end D5.S3.Entropy.KolmogorovSinai


