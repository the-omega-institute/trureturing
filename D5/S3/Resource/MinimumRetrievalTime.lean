/- GID: D5/S3/Resource/MinimumRetrievalTime
   generality: G
   mirror-B: D5/B/S3/Resource/MinimumRetrievalTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Resource/MinimumRetrievalTime.claim; result=D5/S3/Resource/MinimumRetrievalTime.result; claim=D5/S3/Resource/MinimumRetrievalTime.claim
   digest: Actual uniform iid span retrieval admits a rank-three four-column pair (2,6) that no five-column code Pareto dominates. -/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.MinimumRetrievalTime

open MeasureTheory Set
open scoped ENNReal BigOperators

open Classical in
def minimumTime {Ω : Type*} (recovered : ℕ → Ω → Prop) (sample : Ω) : ℝ≥0∞ :=
  if found : ∃ time, recovered time sample then (Nat.find found : ℝ≥0∞) else ⊤

def uniformSamples (alphabet : Type*) [Fintype alphabet] [Nonempty alphabet]
    [MeasurableSpace alphabet] : Measure (ℕ → alphabet) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype alphabet).toMeasure)

def prefixSpan {K V alphabet : Type*} [Field K] [AddCommGroup V] [Module K V]
    (columns : alphabet → V) (sample : ℕ → alphabet) (time : ℕ) : Submodule K V :=
  Submodule.span K (Set.range (fun index : Fin time => columns (sample index)))

def recovered {K V alphabet : Type*} [Field K] [AddCommGroup V] [Module K V]
    (columns : alphabet → V) (file : Submodule K V) (time : ℕ)
    (sample : ℕ → alphabet) : Prop :=
  file ≤ prefixSpan columns sample time

def retrievalTime {K V alphabet : Type*} [Field K] [AddCommGroup V] [Module K V]
    (columns : alphabet → V) (file : Submodule K V) (sample : ℕ → alphabet) : ℝ≥0∞ :=
  minimumTime (recovered columns file) sample

theorem retrieval_time_probability_bridge {K V alphabet : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [Fintype alphabet] [Nonempty alphabet] [MeasurableSpace alphabet]
    [MeasurableSingletonClass alphabet]
    (columns : alphabet → V) (file : Submodule K V)
    (hfile : file ≤ Submodule.span K (Set.range columns)) :
    Measurable (retrievalTime columns file) ∧
    (∀ (time : ℕ) sample, (time : ℝ≥0∞) < retrievalTime columns file sample ↔
      ¬ recovered columns file time sample) ∧
    (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) =
      ∑' time : ℕ, uniformSamples alphabet {sample | ¬ recovered columns file time sample} ∧
    (∀ time : ℕ, uniformSamples alphabet {sample | ¬ recovered columns file time sample} ≤
      (Fintype.card alphabet : ℝ≥0∞) *
        (1 - (Fintype.card alphabet : ℝ≥0∞)⁻¹) ^ time) ∧
    (∀ horizon : ℕ, (∑ time ∈ Finset.range horizon,
      uniformSamples alphabet {sample | ¬ recovered columns file time sample}) ≤
        ∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) ∧
    (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) < ⊤ ∧
    Integrable (fun sample => (retrievalTime columns file sample).toReal)
      (uniformSamples alphabet) ∧
    (∫ sample, (retrievalTime columns file sample).toReal ∂uniformSamples alphabet) =
      (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet).toReal := by
  classical
  let μ := uniformSamples alphabet
  let oneDraw := (PMF.uniformOfFintype alphabet).toMeasure
  let ratio : ℝ≥0∞ := 1 - (Fintype.card alphabet : ℝ≥0∞)⁻¹
  have hmeas : ∀ time, MeasurableSet {sample | recovered columns file time sample} := by
    intro time
    let wordRecovery : Set (Fin time → alphabet) :=
      {word | file ≤ Submodule.span K (Set.range (fun index => columns (word index)))}
    have hprefix : Measurable (fun sample : ℕ → alphabet =>
        fun index : Fin time => sample index.val) :=
      measurable_pi_iff.mpr (fun index => measurable_pi_apply index.val)
    have hw := wordRecovery.to_countable.measurableSet.preimage hprefix
    simpa only [wordRecovery, recovered, prefixSpan, Set.preimage, Set.mem_ofPred_eq] using hw
  have hmono : ∀ sample, Monotone (fun time => recovered columns file time sample) := by
    intro sample earlier later hle hrec
    apply hrec.trans
    apply Submodule.span_mono
    rintro _ ⟨index, rfl⟩
    exact ⟨⟨index.val, lt_of_lt_of_le index.isLt hle⟩, rfl⟩
  have htail : ∀ (time : ℕ) sample, (time : ℝ≥0∞) < retrievalTime columns file sample ↔
      ¬ recovered columns file time sample := by
    intro time sample
    unfold retrievalTime minimumTime
    split_ifs with found
    · have hcast : (time : ℝ≥0∞) < (Nat.find found : ℝ≥0∞) ↔
          time < Nat.find found := by exact_mod_cast Iff.rfl
      rw [hcast]
      constructor
      · intro hlt hrec
        exact (not_lt_of_ge (Nat.find_min' found hrec)) hlt
      · intro hnot
        by_contra hlt
        exact hnot (hmono sample (Nat.le_of_not_gt hlt) (Nat.find_spec found))
    · simp only [ENNReal.natCast_lt_top, true_iff]
      exact fun hrec => found ⟨time, hrec⟩
  let indicator : ℕ → (ℕ → alphabet) → ℝ≥0∞ := fun time =>
    {sample | ¬ recovered columns file time sample}.indicator (fun _ => 1)
  have hind : ∀ time, Measurable (indicator time) := by
    intro time
    exact measurable_const.indicator (hmeas time).compl
  have hsum : ∀ sample, retrievalTime columns file sample = ∑' time, indicator time sample := by
    intro sample
    unfold retrievalTime minimumTime
    split_ifs with found
    · have hterm : ∀ time, indicator time sample =
          if time < Nat.find found then 1 else 0 := by
        intro time
        simp only [indicator, Set.indicator_apply, Set.mem_ofPred_eq]
        congr 1
        have ht := htail time sample
        rw [retrievalTime, minimumTime, dif_pos found] at ht
        exact propext (ht.symm.trans (by exact_mod_cast Iff.rfl))
      simp_rw [hterm]
      rw [tsum_eq_sum (s := Finset.range (Nat.find found))]
      · rw [Finset.sum_congr rfl (fun time hmem => if_pos (Finset.mem_range.mp hmem))]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      · intro time hnot
        simp only [Finset.mem_range, not_lt] at hnot
        simp [not_lt.mpr hnot]
    · have hterm : ∀ time, indicator time sample = 1 := by
        intro time
        simp [indicator, show ¬ recovered columns file time sample from
          fun hrec => found ⟨time, hrec⟩]
      simp_rw [hterm]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  have hmeasurable : Measurable (retrievalTime columns file) := by
    have hfunction : retrievalTime columns file = fun sample => ∑' time, indicator time sample :=
      funext hsum
    rw [hfunction]
    exact Measurable.tsum hind
  have hmean : (∫⁻ sample, retrievalTime columns file sample ∂μ) =
      ∑' time : ℕ, μ {sample | ¬ recovered columns file time sample} := by
    simp_rw [hsum]
    rw [lintegral_tsum (fun time => (hind time).aemeasurable)]
    congr 1
    funext time
    exact lintegral_indicator_one (hmeas time).compl
  have hsingleton : ∀ index : alphabet, oneDraw {index} =
      (Fintype.card alphabet : ℝ≥0∞)⁻¹ := by
    intro index
    rw [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton index)]
    simp
  have havoid : ∀ (time : ℕ) (index : alphabet),
      μ {sample | ∀ draw < time, sample draw ≠ index} = ratio ^ time := by
    intro time index
    have hevent : {sample : ℕ → alphabet | ∀ draw < time, sample draw ≠ index} =
        Set.pi (Finset.range time) (fun _ => ({index} : Set alphabet)ᶜ) := by
      ext sample
      simp
    rw [hevent]
    dsimp only [μ, uniformSamples]
    rw [Measure.infinitePi_pi (fun _ : ℕ => oneDraw)
      (fun _ _ => (measurableSet_singleton index).compl)]
    have hone : oneDraw ({index} : Set alphabet)ᶜ = ratio := by
      rw [measure_compl (measurableSet_singleton index) (by
        rw [hsingleton]; simp)]
      simp only [measure_univ, hsingleton, ratio]
    change (∏ _ ∈ Finset.range time, oneDraw ({index} : Set alphabet)ᶜ) = ratio ^ time
    simp [hone]
  have hbound : ∀ time, μ {sample | ¬ recovered columns file time sample} ≤
      (Fintype.card alphabet : ℝ≥0∞) * ratio ^ time := by
    intro time
    have hinclusion : {sample | ¬ recovered columns file time sample} ⊆
        ⋃ index : alphabet, {sample | ∀ draw < time, sample draw ≠ index} := by
      intro sample hnot
      by_contra hmissing
      have hseen : ∀ index : alphabet, ∃ draw < time, sample draw = index := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_forall,
          not_not, exists_prop] using hmissing
      apply hnot
      apply hfile.trans
      apply Submodule.span_mono
      rintro _ ⟨index, rfl⟩
      obtain ⟨draw, hdraw, hindex⟩ := hseen index
      exact ⟨⟨draw, hdraw⟩, by simp [hindex]⟩
    calc
      μ {sample | ¬ recovered columns file time sample} ≤
          μ (⋃ index : alphabet, {sample | ∀ draw < time, sample draw ≠ index}) :=
        measure_mono hinclusion
      _ ≤ ∑' index : alphabet, μ {sample | ∀ draw < time, sample draw ≠ index} :=
        measure_iUnion_le _
      _ = (Fintype.card alphabet : ℝ≥0∞) * ratio ^ time := by
        simp [havoid, tsum_fintype]
  have hratio : ratio < 1 := by
    apply ENNReal.sub_lt_self (by simp) (by simp)
    simp
  have hfinite : (∫⁻ sample, retrievalTime columns file sample ∂μ) < ⊤ := by
    rw [hmean]
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by simp) (tsum_geometric_lt_top.mpr hratio)
  refine ⟨hmeasurable, htail, hmean, hbound, ?_, hfinite, ?_, ?_⟩
  · intro horizon
    rw [hmean]
    exact ENNReal.sum_le_tsum _
  · exact integrable_toReal_of_lintegral_ne_top hmeasurable.aemeasurable hfinite.ne
  · exact integral_toReal hmeasurable.aemeasurable
      (ae_lt_top hmeasurable hfinite.ne)

def oldAddress : Fin 4 → Fin 3 := ![0, 0, 1, 2]

def oldColumns {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (basis : Module.Basis (Fin 3) K V) : Fin 4 → V := fun index => basis (oldAddress index)

def oldFirstFile {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (basis : Module.Basis (Fin 3) K V) : Submodule K V :=
  Submodule.span K ({basis 0} : Set V)

def oldSecondFile {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (basis : Module.Basis (Fin 3) K V) : Submodule K V :=
  Submodule.span K ({basis 1, basis 2} : Set V)

theorem old_code_actual_expectations {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (basis : Module.Basis (Fin 3) K V) :
    Submodule.span K (Set.range (oldColumns basis)) = ⊤ ∧
    (∫ sample, (retrievalTime (oldColumns basis) (oldFirstFile basis) sample).toReal
      ∂uniformSamples (Fin 4)) = 2 ∧
    (∫ sample, (retrievalTime (oldColumns basis) (oldSecondFile basis) sample).toReal
      ∂uniformSamples (Fin 4)) = 6 := by
  classical
  let μ := uniformSamples (Fin 4)
  have hhalf : (2 : ℝ≥0∞) / 4 = 2⁻¹ := by
    rw [← one_div]
    apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).mpr
    norm_num
  have hsurj : Function.Surjective oldAddress := by
    intro index
    fin_cases index
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hrange : Set.range (oldColumns basis) = Set.range basis := by
    change Set.range (basis ∘ oldAddress) = Set.range basis
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
  have hfull : Submodule.span K (Set.range (oldColumns basis)) = ⊤ := by
    rw [hrange, basis.span_eq]
  have hprefix : ∀ sample time, prefixSpan (oldColumns basis) sample time =
      Submodule.span K
        (basis '' Set.range (fun index : Fin time => oldAddress (sample index))) := by
    intro sample time
    simp only [prefixSpan, oldColumns, ← Set.range_comp]
    rfl
  have hfirst : ∀ sample time, recovered (oldColumns basis) (oldFirstFile basis) time sample ↔
      ∃ draw < time, (sample draw : Fin 4) = 0 ∨ sample draw = 1 := by
    intro sample time
    rw [recovered, oldFirstFile, Submodule.span_singleton_le_iff_mem, hprefix,
      basis.self_mem_span_image]
    have haddress : ∀ index : Fin 4, oldAddress index = 0 ↔ index = 0 ∨ index = 1 := by
      intro index
      fin_cases index <;> simp [oldAddress]
    simp only [Set.mem_range, haddress]
    constructor
    · rintro ⟨draw, hdraw⟩
      exact ⟨draw.val, draw.isLt, hdraw⟩
    · rintro ⟨draw, hdraw, hindex⟩
      exact ⟨⟨draw, hdraw⟩, hindex⟩
  have hsecond : ∀ sample time, recovered (oldColumns basis) (oldSecondFile basis) time sample ↔
      (∃ draw < time, (sample draw : Fin 4) = 2) ∧ (∃ draw < time, sample draw = 3) := by
    intro sample time
    rw [recovered, oldSecondFile, Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      hprefix, basis.self_mem_span_image, Set.mem_range]
    have haddress : ∀ index : Fin 4,
        (oldAddress index = 1 ↔ index = 2) ∧ (oldAddress index = 2 ↔ index = 3) := by
      intro index
      fin_cases index <;> simp [oldAddress]
    simp only [(haddress _).1, (haddress _).2]
    constructor
    · rintro ⟨⟨first, hfirst⟩, ⟨second, hsecond⟩⟩
      exact ⟨⟨first.val, first.isLt, hfirst⟩, ⟨second.val, second.isLt, hsecond⟩⟩
    · rintro ⟨⟨first, hfirst, hfirstEq⟩, ⟨second, hsecond, hsecondEq⟩⟩
      exact ⟨⟨⟨first, hfirst⟩, hfirstEq⟩, ⟨⟨second, hsecond⟩, hsecondEq⟩⟩
  have hallowed : ∀ (time : ℕ) (allowed : Set (Fin 4)),
      μ {sample | ∀ draw < time, sample draw ∈ allowed} =
        ((Fintype.card allowed : ℝ≥0∞) / 4) ^ time := by
    intro time allowed
    have hevent : {sample : ℕ → Fin 4 | ∀ draw < time, sample draw ∈ allowed} =
        Set.pi (Finset.range time) (fun _ => allowed) := by ext sample; simp
    rw [hevent]
    dsimp only [μ, uniformSamples]
    rw [Measure.infinitePi_pi (fun _ : ℕ => (PMF.uniformOfFintype (Fin 4)).toMeasure)
      (fun _ _ => allowed.to_countable.measurableSet)]
    simp only [PMF.toMeasure_uniformOfFintype_apply allowed allowed.to_countable.measurableSet,
      Fintype.card_fin, Finset.prod_const, Finset.card_range]
    rfl
  have htailFirst : ∀ time,
      μ {sample | ¬ recovered (oldColumns basis) (oldFirstFile basis) time sample} =
      (2⁻¹ : ℝ≥0∞) ^ time := by
    intro time
    have hevent : {sample | ¬ recovered (oldColumns basis) (oldFirstFile basis) time sample} =
        {sample | ∀ draw < time, sample draw ∈ ({0, 1} : Set (Fin 4))ᶜ} := by
      ext sample
      simp [hfirst]
    rw [hevent, hallowed]
    have hcard : ∀ inst : Fintype ↑(({0, 1} : Set (Fin 4))ᶜ),
        @Fintype.card ↑(({0, 1} : Set (Fin 4))ᶜ) inst = 2 := by
      intro inst
      rw [Fintype.card_of_finset' ({2, 3} : Finset (Fin 4)) (by
        intro index; fin_cases index <;> simp)]
      decide
    rw [hcard]
    simp only [Nat.cast_ofNat, hhalf]
  let misses : Fin 4 → ℕ → Set (ℕ → Fin 4) :=
    fun index time => {sample | ∀ draw < time, sample draw ≠ index}
  have hmisses : ∀ index time, μ (misses index time) = ((3 : ℝ≥0∞) / 4) ^ time := by
    intro index time
    change μ {sample | ∀ draw < time, sample draw ∈ ({index} : Set (Fin 4))ᶜ} = _
    rw [hallowed]
    have hcard : ∀ inst : Fintype ↑(({index} : Set (Fin 4))ᶜ),
        @Fintype.card ↑(({index} : Set (Fin 4))ᶜ) inst = 3 := by
      intro inst
      rw [Fintype.card_of_finset' (Finset.univ.erase index) (by intro candidate; simp)]
      simp [Finset.card_univ, Fintype.card_fin]
    rw [hcard]
    simp only [Nat.cast_ofNat]
  have hmissMeas : ∀ index time, MeasurableSet (misses index time) := by
    intro index time
    simp only [misses, Set.ofPred_forall]
    exact MeasurableSet.iInter fun draw => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton index).compl.preimage (measurable_pi_apply draw)
  have htailSecond : ∀ time,
      μ {sample | ¬ recovered (oldColumns basis) (oldSecondFile basis) time sample} +
        (2⁻¹ : ℝ≥0∞) ^ time =
        ((3 : ℝ≥0∞) / 4) ^ time + ((3 : ℝ≥0∞) / 4) ^ time := by
    intro time
    have hbad : {sample | ¬ recovered (oldColumns basis) (oldSecondFile basis) time sample} =
        misses 2 time ∪ misses 3 time := by
      ext sample
      rw [Set.mem_ofPred_eq, hsecond, not_and_or]
      simp [misses]
    have hinter : misses 2 time ∩ misses 3 time =
        {sample | ∀ draw < time, sample draw ∈ ({2, 3} : Set (Fin 4))ᶜ} := by
      ext sample
      simp [misses, forall_and]
    have hinterMeasure : μ (misses 2 time ∩ misses 3 time) = (2⁻¹ : ℝ≥0∞) ^ time := by
      rw [hinter, hallowed]
      have hcard : ∀ inst : Fintype ↑(({2, 3} : Set (Fin 4))ᶜ),
          @Fintype.card ↑(({2, 3} : Set (Fin 4))ᶜ) inst = 2 := by
        intro inst
        rw [Fintype.card_of_finset' ({0, 1} : Finset (Fin 4)) (by
          intro index; fin_cases index <;> simp)]
        decide
      rw [hcard]
      simp only [Nat.cast_ofNat, hhalf]
    rw [hbad, ← hinterMeasure, measure_union_add_inter _ (hmissMeas 3 time), hmisses, hmisses]
  obtain ⟨_, _, hmeanFirst, _, _, _, _, hrealFirst⟩ := retrieval_time_probability_bridge
    (oldColumns basis) (oldFirstFile basis) (by rw [hfull]; exact le_top)
  obtain ⟨_, _, hmeanSecond, _, _, _, _, hrealSecond⟩ := retrieval_time_probability_bridge
    (oldColumns basis) (oldSecondFile basis) (by rw [hfull]; exact le_top)
  have hmeanFirstExact :
      (∫⁻ sample, retrievalTime (oldColumns basis) (oldFirstFile basis) sample ∂μ) = 2 := by
    change (∫⁻ sample, retrievalTime (oldColumns basis) (oldFirstFile basis) sample
      ∂uniformSamples (Fin 4)) = 2
    rw [hmeanFirst]
    change (∑' time,
      μ {sample | ¬ recovered (oldColumns basis) (oldFirstFile basis) time sample}) = 2
    simp_rw [htailFirst]
    exact ENNReal.tsum_geometric_two
  have hmeanSecondExact :
      (∫⁻ sample, retrievalTime (oldColumns basis) (oldSecondFile basis) sample ∂μ) = 6 := by
    rw [hmeanSecond]
    have hquarter : (1 - (3 : ℝ≥0∞) / 4) = 4⁻¹ := by
      symm
      apply ENNReal.eq_sub_of_add_eq (by finiteness)
      rw [← one_div, ← ENNReal.add_div]
      norm_num
      exact ENNReal.div_self (by norm_num) (by norm_num)
    have hsummed := congrArg (fun sequence : ℕ → ℝ≥0∞ => ∑' time, sequence time)
      (funext htailSecond)
    simp only [ENNReal.tsum_add, ENNReal.tsum_geometric,
      ENNReal.one_sub_inv_two, hquarter, inv_inv] at hsummed
    apply (ENNReal.add_left_inj (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
    calc
      _ = 4 + 4 := hsummed
      _ = (6 : ℝ≥0∞) + 2 := by norm_num
  refine ⟨hfull, ?_, ?_⟩
  · rw [hrealFirst, hmeanFirstExact]
    norm_num
  · rw [hrealSecond, hmeanSecondExact]
    norm_num

theorem five_column_three_kernel_obstruction {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (columns : Fin 5 → V) (file : Submodule K V) (projection : V →ₗ[K] W)
    (first second : V) (hfirst : first ∈ file) (hsecond : second ∈ file)
    (hindependent : LinearIndependent K ![projection first, projection second])
    (left right : Fin 5) (hleftRight : left ≠ right)
    (hzero : ∀ index : Fin 5, index ≠ left → index ≠ right →
      projection (columns index) = 0)
    (hfile : file ≤ Submodule.span K (Set.range columns)) :
    6 < ∫ sample, (retrievalTime columns file sample).toReal ∂uniformSamples (Fin 5) := by
  classical
  let μ := uniformSamples (Fin 5)
  have : IsProbabilityMeasure μ := by dsimp [μ, uniformSamples]; infer_instance
  have hneeded : ∀ (missing other : Fin 5),
      (∀ index : Fin 5, index ≠ missing →
        projection (columns index) ∈ Submodule.span K ({projection (columns other)} : Set W)) →
      ∀ sample time, recovered columns file time sample →
        ∃ draw < time, sample draw = missing := by
    intro missing other hsupport sample time hrec
    by_contra hnot
    push Not at hnot
    let line := Submodule.span K ({projection (columns other)} : Set W)
    have hspan : prefixSpan columns sample time ≤ line.comap projection := by
      apply Submodule.span_le.mpr
      rintro _ ⟨draw, rfl⟩
      exact hsupport (sample draw.val) (hnot draw.val draw.isLt)
    have hfirstLine : projection first ∈ line := hspan (hrec hfirst)
    have hsecondLine : projection second ∈ line := hspan (hrec hsecond)
    obtain ⟨firstCoefficient, hfirstCoefficient⟩ := Submodule.mem_span_singleton.mp hfirstLine
    obtain ⟨secondCoefficient, hsecondCoefficient⟩ :=
      Submodule.mem_span_singleton.mp hsecondLine
    have hrelation : secondCoefficient • projection first +
        (-firstCoefficient) • projection second = 0 := by
      rw [← hfirstCoefficient, ← hsecondCoefficient]
      module
    have hcoefficients := hindependent.eq_zero_of_pair hrelation
    have hfirstZero : projection first = 0 := by
      rw [← hfirstCoefficient, neg_eq_zero.mp hcoefficients.2, zero_smul]
    exact hindependent.ne_zero 0 hfirstZero
  have hneedsLeft : ∀ sample time, recovered columns file time sample →
      ∃ draw < time, sample draw = left := by
    apply hneeded left right
    intro index hne
    by_cases hright : index = right
    · subst index; exact Submodule.subset_span (by simp)
    · rw [hzero index hne hright]; exact Submodule.zero_mem _
  have hneedsRight : ∀ sample time, recovered columns file time sample →
      ∃ draw < time, sample draw = right := by
    apply hneeded right left
    intro index hne
    by_cases hleft : index = left
    · subst index; exact Submodule.subset_span (by simp)
    · rw [hzero index hleft hne]; exact Submodule.zero_mem _
  let misses : Fin 5 → ℕ → Set (ℕ → Fin 5) :=
    fun index time => {sample | ∀ draw < time, sample draw ≠ index}
  have hmissMeas : ∀ index time, MeasurableSet (misses index time) := by
    intro index time
    simp only [misses, Set.ofPred_forall]
    exact MeasurableSet.iInter fun draw => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton index).compl.preimage (measurable_pi_apply draw)
  have hallowed : ∀ (time : ℕ) (allowed : Set (Fin 5)),
      μ {sample | ∀ draw < time, sample draw ∈ allowed} =
        ((Fintype.card allowed : ℝ≥0∞) / 5) ^ time := by
    intro time allowed
    have hevent : {sample : ℕ → Fin 5 | ∀ draw < time, sample draw ∈ allowed} =
        Set.pi (Finset.range time) (fun _ => allowed) := by ext sample; simp
    rw [hevent]
    dsimp only [μ, uniformSamples]
    rw [Measure.infinitePi_pi (fun _ : ℕ => (PMF.uniformOfFintype (Fin 5)).toMeasure)
      (fun _ _ => allowed.to_countable.measurableSet)]
    simp only [PMF.toMeasure_uniformOfFintype_apply allowed allowed.to_countable.measurableSet,
      Fintype.card_fin, Finset.prod_const, Finset.card_range]
    rfl
  have hmisses : ∀ index time, μ (misses index time) = ((4 : ℝ≥0∞) / 5) ^ time := by
    intro index time
    change μ {sample | ∀ draw < time, sample draw ∈ ({index} : Set (Fin 5))ᶜ} = _
    rw [hallowed]
    have hcard : ∀ inst : Fintype ↑(({index} : Set (Fin 5))ᶜ),
        @Fintype.card ↑(({index} : Set (Fin 5))ᶜ) inst = 4 := by
      intro inst
      rw [Fintype.card_of_finset' (Finset.univ.erase index) (by intro candidate; simp)]
      simp [Finset.card_univ, Fintype.card_fin]
    rw [hcard]
    simp only [Nat.cast_ofNat]
  have hinter : ∀ time, μ (misses left time ∩ misses right time) = ((3 : ℝ≥0∞) / 5) ^ time := by
    intro time
    have hevent : misses left time ∩ misses right time =
        {sample | ∀ draw < time, sample draw ∈ ({left, right} : Set (Fin 5))ᶜ} := by
      ext sample
      simp [misses, forall_and]
    rw [hevent, hallowed]
    have hcard : ∀ inst : Fintype ↑(({left, right} : Set (Fin 5))ᶜ),
        @Fintype.card ↑(({left, right} : Set (Fin 5))ᶜ) inst = 3 := by
      intro inst
      rw [Fintype.card_of_finset' ((Finset.univ.erase left).erase right) (by
        intro index; simp [and_comm])]
      rw [Finset.card_erase_of_mem (by simp [hleftRight.symm]),
        Finset.card_erase_of_mem (Finset.mem_univ left)]
      simp
    rw [hcard]
    simp only [Nat.cast_ofNat]
  have hpoint : ∀ time, (μ (misses left time ∪ misses right time)).toReal =
      2 * ((4 : ℝ) / 5) ^ time - ((3 : ℝ) / 5) ^ time := by
    intro time
    have hidentity := measure_union_add_inter (μ := μ) (misses left time) (hmissMeas right time)
    have hreal := congrArg ENNReal.toReal hidentity
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      hinter, hmisses, hmisses] at hreal
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hreal
    linarith
  have hsubset : ∀ time, misses left time ∪ misses right time ⊆
      {sample | ¬ recovered columns file time sample} := by
    intro time sample hmiss hrec
    rcases hmiss with hmiss | hmiss
    · obtain ⟨draw, hdraw, heq⟩ := hneedsLeft sample time hrec
      exact hmiss draw hdraw heq
    · obtain ⟨draw, hdraw, heq⟩ := hneedsRight sample time hrec
      exact hmiss draw hdraw heq
  obtain ⟨_, _, _, _, hpartial, hfinite, _, hreal⟩ :=
    retrieval_time_probability_bridge columns file hfile
  have hbound : (∑ time ∈ Finset.range 9, μ (misses left time ∪ misses right time)) ≤
      ∫⁻ sample, retrievalTime columns file sample ∂μ := by
    exact (Finset.sum_le_sum (fun time _ => measure_mono (hsubset time))).trans (hpartial 9)
  have hrealBound := ENNReal.toReal_mono hfinite.ne hbound
  rw [ENNReal.toReal_sum (fun time _ => measure_ne_top μ _)] at hrealBound
  simp_rw [hpoint] at hrealBound
  rw [hreal]
  have hsum : (∑ time ∈ Finset.range 9,
      (2 * ((4 : ℝ) / 5) ^ time - ((3 : ℝ) / 5) ^ time)) = 2415241 / 390625 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hrealBound
  exact lt_of_lt_of_le (by norm_num : (6 : ℝ) < 2415241 / 390625) hrealBound

theorem five_column_bad_pairs_obstruction {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (columns : Fin 5 → V) (file : Submodule K V)
    (common left right : Fin 5) (hcommonLeft : common ≠ left)
    (hcommonRight : common ≠ right) (hleftRight : left ≠ right)
    (hbadLeft : ¬ file ≤ Submodule.span K ({columns common, columns left} : Set V))
    (hbadRight : ¬ file ≤ Submodule.span K ({columns common, columns right} : Set V))
    (hfile : file ≤ Submodule.span K (Set.range columns)) :
    2 < ∫ sample, (retrievalTime columns file sample).toReal ∂uniformSamples (Fin 5) := by
  classical
  let μ := uniformSamples (Fin 5)
  have : IsProbabilityMeasure μ := by dsimp [μ, uniformSamples]; infer_instance
  let only : Set (Fin 5) → ℕ → Set (ℕ → Fin 5) :=
    fun allowed time => {sample | ∀ draw < time, sample draw ∈ allowed}
  have honlyMeas : ∀ allowed time, MeasurableSet (only allowed time) := by
    intro allowed time
    simp only [only, Set.ofPred_forall]
    exact MeasurableSet.iInter fun draw => MeasurableSet.iInter fun _ =>
      allowed.to_countable.measurableSet.preimage (measurable_pi_apply draw)
  have hallowed : ∀ (time : ℕ) (allowed : Set (Fin 5)),
      μ (only allowed time) = ((Fintype.card allowed : ℝ≥0∞) / 5) ^ time := by
    intro time allowed
    have hevent : only allowed time = Set.pi (Finset.range time) (fun _ => allowed) := by
      ext sample
      simp [only]
    rw [hevent]
    dsimp only [μ, uniformSamples]
    rw [Measure.infinitePi_pi (fun _ : ℕ => (PMF.uniformOfFintype (Fin 5)).toMeasure)
      (fun _ _ => allowed.to_countable.measurableSet)]
    simp only [PMF.toMeasure_uniformOfFintype_apply allowed allowed.to_countable.measurableSet,
      Fintype.card_fin, Finset.prod_const, Finset.card_range]
    rfl
  have hpair : ∀ (first second : Fin 5), first ≠ second → ∀ time,
      μ (only {first, second} time) = ((2 : ℝ≥0∞) / 5) ^ time := by
    intro first second hne time
    rw [hallowed]
    have hcard : ∀ inst : Fintype ↑({first, second} : Set (Fin 5)),
        @Fintype.card ↑({first, second} : Set (Fin 5)) inst = 2 := by
      intro inst
      rw [Fintype.card_of_finset' ({first, second} : Finset (Fin 5)) (by intro index; simp)]
      simp [hne]
    rw [hcard]
    simp only [Nat.cast_ofNat]
  have hinterSet : ({common, left} : Set (Fin 5)) ∩ {common, right} = {common} := by
    ext index
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hinter : ∀ time,
      μ (only {common, left} time ∩ only {common, right} time) =
        ((1 : ℝ≥0∞) / 5) ^ time := by
    intro time
    have hevent : only {common, left} time ∩ only {common, right} time =
        only ({common} : Set (Fin 5)) time := by
      have heq : only {common, left} time ∩ only {common, right} time =
          only (({common, left} : Set (Fin 5)) ∩ {common, right}) time := by
        ext sample
        simp [only, forall_and]
      rw [heq, hinterSet]
    rw [hevent, hallowed]
    have hcard : ∀ inst : Fintype ↑({common} : Set (Fin 5)),
        @Fintype.card ↑({common} : Set (Fin 5)) inst = 1 := by
      intro inst
      rw [Fintype.card_of_finset' ({common} : Finset (Fin 5)) (by intro index; simp)]
      simp
    rw [hcard]
    simp only [Nat.cast_one]
  have hpoint : ∀ time,
      (μ (only {common, left} time ∪ only {common, right} time)).toReal =
        2 * ((2 : ℝ) / 5) ^ time - ((1 : ℝ) / 5) ^ time := by
    intro time
    have hidentity := measure_union_add_inter (μ := μ) (only {common, left} time)
      (honlyMeas {common, right} time)
    have hreal := congrArg ENNReal.toReal hidentity
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      hinter, hpair common left hcommonLeft, hpair common right hcommonRight] at hreal
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at hreal
    linarith
  have hbadOnly : ∀ (first second : Fin 5),
      (¬ file ≤ Submodule.span K ({columns first, columns second} : Set V)) →
      ∀ time, only {first, second} time ⊆ {sample | ¬ recovered columns file time sample} := by
    intro first second hbad time sample hsample hrec
    apply hbad
    apply hrec.trans
    apply Submodule.span_mono
    rintro _ ⟨draw, rfl⟩
    have hdraw := hsample draw.val draw.isLt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdraw
    rcases hdraw with hdraw | hdraw <;> simp [hdraw]
  have hsubset : ∀ time, only {common, left} time ∪ only {common, right} time ⊆
      {sample | ¬ recovered columns file time sample} := by
    intro time sample hsample
    rcases hsample with hsample | hsample
    · exact hbadOnly common left hbadLeft time hsample
    · exact hbadOnly common right hbadRight time hsample
  obtain ⟨_, _, _, _, hpartial, hfinite, _, hreal⟩ :=
    retrieval_time_probability_bridge columns file hfile
  have hbound : (∑ time ∈ Finset.range 5,
      μ (only {common, left} time ∪ only {common, right} time)) ≤
        ∫⁻ sample, retrievalTime columns file sample ∂μ := by
    exact (Finset.sum_le_sum (fun time _ => measure_mono (hsubset time))).trans (hpartial 5)
  have hrealBound := ENNReal.toReal_mono hfinite.ne hbound
  rw [ENNReal.toReal_sum (fun time _ => measure_ne_top μ _)] at hrealBound
  simp_rw [hpoint] at hrealBound
  rw [hreal]
  have hsum : (∑ time ∈ Finset.range 5,
      (2 * ((2 : ℝ) / 5) ^ time - ((1 : ℝ) / 5) ^ time)) = 1281 / 625 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hrealBound
  exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 1281 / 625) hrealBound

theorem five_column_projected_obstruction {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (columns : Fin 5 → V) (file : Submodule K V) (projection : V →ₗ[K] W)
    (target : V) (htarget : target ∈ file) (htargetNe : target ≠ 0)
    (htargetProjection : projection target = 0)
    (left right third : Fin 5) (hleftRight : left ≠ right)
    (hleftThird : left ≠ third) (hrightThird : right ≠ third)
    (hindependent : LinearIndependent K ![projection (columns left), projection (columns right)])
    (hthird : target ∉ Submodule.span K ({columns third} : Set V))
    (hfile : file ≤ Submodule.span K (Set.range columns)) :
    2 < ∫ sample, (retrievalTime columns file sample).toReal ∂uniformSamples (Fin 5) := by
  classical
  have hbadPair : target ∉ Submodule.span K ({columns left, columns right} : Set V) := by
    intro hmem
    obtain ⟨leftCoefficient, rightCoefficient, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hmap := congrArg projection hsum
    simp only [map_add, map_smul, htargetProjection] at hmap
    have hcoefficients := hindependent.eq_zero_of_pair hmap
    simp only [hcoefficients.1, hcoefficients.2, zero_smul, zero_add] at hsum
    exact htargetNe hsum.symm
  have hotherPair :
      target ∉ Submodule.span K ({columns third, columns left} : Set V) ∨
      target ∉ Submodule.span K ({columns third, columns right} : Set V) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨firstThird, firstLeft, hfirst⟩ := Submodule.mem_span_pair.mp hnot.1
    obtain ⟨secondThird, secondRight, hsecond⟩ := Submodule.mem_span_pair.mp hnot.2
    have hmapFirst := congrArg projection hfirst
    have hmapSecond := congrArg projection hsecond
    simp only [map_add, map_smul, htargetProjection] at hmapFirst hmapSecond
    have hsecondThird : secondThird ≠ 0 := by
      intro hzero
      have hrightNe : projection (columns right) ≠ 0 := by
        simpa using hindependent.ne_zero 1
      have hrightZero : secondRight = 0 :=
        (smul_eq_zero.mp (by simpa [hzero] using hmapSecond)).resolve_right hrightNe
      simp only [hzero, hrightZero, zero_smul, zero_add] at hsecond
      exact htargetNe hsecond.symm
    have hrelation : (secondThird * firstLeft) • projection (columns left) +
        (-firstThird * secondRight) • projection (columns right) = 0 := by
      calc
        _ = secondThird • (firstThird • projection (columns third) +
              firstLeft • projection (columns left)) -
            firstThird • (secondThird • projection (columns third) +
              secondRight • projection (columns right)) := by module
        _ = 0 := by rw [hmapFirst, hmapSecond]; simp
    have hcoefficients := hindependent.eq_zero_of_pair hrelation
    have hfirstLeft : firstLeft = 0 :=
      (mul_eq_zero.mp hcoefficients.1).resolve_left hsecondThird
    apply hthird
    apply Submodule.mem_span_singleton.mpr
    exact ⟨firstThird, by simpa [hfirstLeft] using hfirst⟩
  rcases hotherPair with hbadLeft | hbadRight
  · apply five_column_bad_pairs_obstruction columns file left right third
      hleftRight hleftThird hrightThird
    · exact fun hrec => hbadPair (hrec htarget)
    · intro hrec
      apply hbadLeft
      simpa only [Set.pair_comm] using hrec htarget
    · exact hfile
  · apply five_column_bad_pairs_obstruction columns file right left third
      hleftRight.symm hrightThird hleftThird
    · intro hrec
      apply hbadPair
      simpa only [Set.pair_comm] using hrec htarget
    · intro hrec
      apply hbadRight
      simpa only [Set.pair_comm] using hrec htarget
    · exact hfile

theorem five_column_universal_obstruction {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (basis : Module.Basis (Fin 3) K V)
    (columns : Fin 5 → V) (hfull : Submodule.span K (Set.range columns) = ⊤) :
    (2 < ∫ sample, (retrievalTime columns (oldFirstFile basis) sample).toReal
      ∂uniformSamples (Fin 5)) ∨
    (6 < ∫ sample, (retrievalTime columns (oldSecondFile basis) sample).toReal
      ∂uniformSamples (Fin 5)) := by
  classical
  let projection : V →ₗ[K] (Fin 2 → K) := LinearMap.pi ![basis.coord 1, basis.coord 2]
  have htargetProjection : projection (basis 0) = 0 := by
    ext index
    fin_cases index <;> simp [projection, Module.Basis.coord_apply]
  have hindependent : LinearIndependent K ![projection (basis 1), projection (basis 2)] := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro hzero
      have hvalue := congrFun hzero 1
      simp [projection, Module.Basis.coord_apply] at hvalue
    · intro scalar heq
      have hvalue := congrFun heq 0
      simp [projection, Module.Basis.coord_apply] at hvalue
  have hcover : ∀ vector : V,
      projection vector ∈
        Submodule.span K (Set.range (fun index => projection (columns index))) := by
    intro vector
    have hmem : projection vector ∈
        (Submodule.span K (Set.range columns)).map projection :=
      Submodule.mem_map.mpr ⟨vector, by rw [hfull]; trivial, rfl⟩
    simpa only [Submodule.map_span, ← Set.range_comp'] using hmem
  have hexistsLeft : ∃ left : Fin 5, projection (columns left) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hspan : Submodule.span K (Set.range (fun index => projection (columns index))) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      simp [hnone index]
    have hzero := hspan (hcover (basis 1))
    exact hindependent.ne_zero 0 (by simpa using hzero)
  obtain ⟨left, hleft⟩ := hexistsLeft
  let line := Submodule.span K ({projection (columns left)} : Set (Fin 2 → K))
  have hexistsRight : ∃ right : Fin 5, projection (columns right) ∉ line := by
    by_contra hnone
    push Not at hnone
    have hspan : Submodule.span K (Set.range (fun index => projection (columns index))) ≤ line := by
      apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      exact hnone index
    obtain ⟨firstCoefficient, hfirstCoefficient⟩ :=
      Submodule.mem_span_singleton.mp (hspan (hcover (basis 1)))
    obtain ⟨secondCoefficient, hsecondCoefficient⟩ :=
      Submodule.mem_span_singleton.mp (hspan (hcover (basis 2)))
    have hrelation : secondCoefficient • projection (basis 1) +
        (-firstCoefficient) • projection (basis 2) = 0 := by
      rw [← hfirstCoefficient, ← hsecondCoefficient]
      module
    have hcoefficients := hindependent.eq_zero_of_pair hrelation
    have hzero : projection (basis 1) = 0 := by
      rw [← hfirstCoefficient, neg_eq_zero.mp hcoefficients.2, zero_smul]
    exact hindependent.ne_zero 0 hzero
  obtain ⟨right, hright⟩ := hexistsRight
  have hrightLeft : right ≠ left := by
    intro heq
    apply hright
    rw [heq]
    exact Submodule.subset_span (by simp)
  have hcolumnsIndependent :
      LinearIndependent K ![projection (columns right), projection (columns left)] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hleft, ?_⟩
    intro scalar heq
    exact hright (Submodule.mem_span_singleton.mpr ⟨scalar, heq⟩)
  by_cases hthird : ∃ third : Fin 5,
      third ≠ right ∧ third ≠ left ∧ projection (columns third) ≠ 0
  · obtain ⟨third, hthirdRight, hthirdLeft, hthirdNe⟩ := hthird
    left
    apply five_column_projected_obstruction columns (oldFirstFile basis) projection
      (basis 0) (Submodule.subset_span (by simp)) (basis.ne_zero 0)
      htargetProjection right left third hrightLeft hthirdRight.symm hthirdLeft.symm
      hcolumnsIndependent
    · intro hmem
      obtain ⟨scalar, heq⟩ := Submodule.mem_span_singleton.mp hmem
      have hmap := congrArg projection heq
      simp only [map_smul, htargetProjection] at hmap
      have hscalar : scalar = 0 := (smul_eq_zero.mp hmap).resolve_right hthirdNe
      rw [hscalar, zero_smul] at heq
      exact basis.ne_zero 0 heq.symm
    · rw [hfull]; exact le_top
  · right
    apply five_column_three_kernel_obstruction columns (oldSecondFile basis) projection
      (basis 1) (basis 2) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) hindependent right left hrightLeft
    · intro index hindexRight hindexLeft
      by_contra hne
      exact hthird ⟨index, hindexRight, hindexLeft, hne⟩
    · rw [hfull]; exact le_top

def firstCoordinateFile (K : Type*) [Field K] (firstSize secondSize : ℕ) :
    Submodule K (Fin (firstSize + secondSize) → K) :=
  Submodule.span K ((Pi.basisFun K (Fin (firstSize + secondSize))) ''
    {index | index.val < firstSize})

def secondCoordinateFile (K : Type*) [Field K] (firstSize secondSize : ℕ) :
    Submodule K (Fin (firstSize + secondSize) → K) :=
  Submodule.span K ((Pi.basisFun K (Fin (firstSize + secondSize))) ''
    {index | firstSize ≤ index.val})

def paretoCodeLengthMonotonicity (K : Type*) [Field K] : Prop :=
  ∀ firstSize secondSize : ℕ, ∀ (_hfirst : 0 < firstSize), 0 < secondSize →
    2 ≤ max firstSize secondSize →
    ∀ length : ℕ, ∀ (_hlength : firstSize + secondSize ≤ length),
    letI : NeZero length := ⟨by omega⟩
    ∀ columns : Fin length → (Fin (firstSize + secondSize) → K),
      Matrix.rank (Matrix.of (fun row column => columns column row)) =
          firstSize + secondSize →
      ∃ successor : Fin (length + 1) → (Fin (firstSize + secondSize) → K),
        Matrix.rank (Matrix.of (fun row column => successor column row)) =
            firstSize + secondSize ∧
        (∫ sample, (retrievalTime successor
          (firstCoordinateFile K firstSize secondSize) sample).toReal
          ∂uniformSamples (Fin (length + 1))) ≤
        (∫ sample, (retrievalTime columns
          (firstCoordinateFile K firstSize secondSize) sample).toReal
          ∂uniformSamples (Fin length)) ∧
        (∫ sample, (retrievalTime successor
          (secondCoordinateFile K firstSize secondSize) sample).toReal
          ∂uniformSamples (Fin (length + 1))) ≤
        (∫ sample, (retrievalTime columns
          (secondCoordinateFile K firstSize secondSize) sample).toReal
          ∂uniformSamples (Fin length))

structure FiniteFieldModel where
  carrier : Type
  field : Field carrier
  finite : Fintype carrier

def claim : Prop :=
  ∀ model : FiniteFieldModel, @paretoCodeLengthMonotonicity model.carrier model.field

theorem result : ¬ claim := by
  classical
  intro hclaim
  let basis : Module.Basis (Fin 3) (ZMod 2) (Fin 3 → ZMod 2) := Pi.basisFun _ _
  have hfirstIndices : {index : Fin (1 + 2) | index.val < 1} = {0} := by
    ext index
    fin_cases index <;> decide
  have hsecondIndices : {index : Fin (1 + 2) | 1 ≤ index.val} = {1, 2} := by
    ext index
    fin_cases index <;> decide
  have hfirst : firstCoordinateFile (ZMod 2) 1 2 = oldFirstFile basis := by
    simp only [firstCoordinateFile, hfirstIndices, Set.image_singleton]
    rfl
  have hsecond : secondCoordinateFile (ZMod 2) 1 2 = oldSecondFile basis := by
    simp only [secondCoordinateFile, hsecondIndices, Set.image_pair]
    rfl
  obtain ⟨hfull, hfirstMean, hsecondMean⟩ := old_code_actual_expectations basis
  have holdRank :
      Matrix.rank (Matrix.of (fun row column => oldColumns basis column row)) =
        1 + 2 := by
    rw [Matrix.rank_eq_finrank_span_cols]
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (oldColumns basis))) = _
    rw [hfull]
    simp
  obtain ⟨successor, hsuccessor, hfirstBound, hsecondBound⟩ :=
    hclaim ⟨ZMod 2, inferInstance, inferInstance⟩ 1 2 (by decide) (by decide) (by decide)
      4 (by decide) (oldColumns basis) holdRank
  have hsuccessorFull : Submodule.span (ZMod 2) (Set.range successor) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.rank_eq_finrank_span_cols] at hsuccessor
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range successor)) =
      1 + 2 at hsuccessor
    simpa using hsuccessor
  rw [hfirst, hfirstMean] at hfirstBound
  rw [hsecond, hsecondMean] at hsecondBound
  rcases five_column_universal_obstruction basis successor hsuccessorFull with hbad | hbad
  · exact (not_lt_of_ge hfirstBound) hbad
  · exact (not_lt_of_ge hsecondBound) hbad

end D5.S3.Resource.MinimumRetrievalTime
