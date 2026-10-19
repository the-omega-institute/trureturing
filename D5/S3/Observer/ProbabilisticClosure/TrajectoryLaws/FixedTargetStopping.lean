/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed fixed-past observable finite returns have positive error on the actual law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.IndependentSeedPosterior
import Mathlib.Probability.Process.Stopping

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set Function
open scoped Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetStopping
open TwelveStatePresentation IndependentSeedPosterior

/-- Complete information by the null events of the whole ambient probability law. -/
def completed {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[m] t ∧ s =ᵐ[μ] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, Filter.EventuallyEq.rfl⟩
  measurableSet_compl s hs := by
    obtain ⟨t,ht,he⟩ := hs
    refine ⟨tᶜ,ht.compl,?_⟩
    filter_upwards [he] with z hz
    exact congrArg Not hz
  measurableSet_iUnion s hs := by
    choose t ht he using hs
    exact ⟨⋃ i, t i,MeasurableSet.iUnion ht,Filter.EventuallyEq.countable_iUnion he⟩

private theorem completed_mono {Ω : Type*} {m k : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (h : m ≤ k) : completed μ m ≤ completed μ k := by
  rintro s ⟨t,ht,he⟩
  exact ⟨t,h t ht,he⟩

theorem past_succ (r : ℕ) : pastField r ≤ pastField (r+1) := by
  have he : pastWord r =
      (fun w : Fin (r+1) → Bool => fun k : Fin r => w k.succ) ∘ pastWord (r+1) := by
    funext z k
    change z.2 (-(r : ℤ) + (k.val : ℤ)) =
      z.2 (-((r+1 : ℕ) : ℤ) + ((k.val+1 : ℕ) : ℤ))
    apply congrArg z.2
    push_cast
    omega
  exact MeasurableSpace.comap_le_comap_of_eq_comp _
    (Measurable.of_eval fun k => measurable_pi_apply k.succ) he

private theorem enlarged_mono {U : Type*} [MeasurableSpace U]
    {m k : MeasurableSpace Process} (h : m ≤ k) :
    enlarged (U := U) m ≤ enlarged k :=
  sup_le_sup (MeasurableSpace.comap_mono h) le_rfl

private theorem enlarged_le {U : Type*} [MeasurableSpace U] (r : ℕ) :
    enlarged (U := U) (pastField r) ≤ (inferInstance : MeasurableSpace (Process × U)) := by
  have h : pastField r ≤ (inferInstance : MeasurableSpace Process) :=
    (Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd).comap_le
  exact enlarged_mono h

/-- One nested filtration for the fixed time-zero target, completed under the product law.
The seed is independent of the entire original hidden/output process. -/
def pastFiltration {U : Type*} [MeasurableSpace U] (ν : Measure U) :
    Filtration ℕ (completed ((joint : Measure Process).prod ν)
      (inferInstance : MeasurableSpace (Process × U))) where
  seq r := completed ((joint : Measure Process).prod ν) (enlarged (pastField r))
  mono' := monotone_nat_of_le_succ fun r =>
    completed_mono _ (enlarged_mono (past_succ r))
  le' r := completed_mono _ (enlarged_le r)


private theorem completion_condExp {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable f μ) :
    (μ[f | m]) =ᵐ[μ] (μ.completion)[f | completed μ m] := by
  have h0 : mΩ ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω μ)) :=
    fun s hs => hs.nullMeasurableSet
  have hc : completed μ m ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω μ)) := by
    rintro s ⟨t,ht,he⟩
    exact (hm t ht).nullMeasurableSet.congr he.symm
  have hmc : m ≤ completed μ m := fun s hs => ⟨s,hs,Filter.EventuallyEq.rfl⟩
  letI : IsProbabilityMeasure μ.completion := ⟨by change μ Set.univ = 1; simp⟩
  have htrim : μ.completion.trim h0 = μ := by
    apply @Measure.ext Ω mΩ
    intro s hs
    rw [trim_measurableSet_eq h0 hs]
    rfl
  have hfi' : Integrable f μ.completion :=
    integrable_of_integrable_trim h0 (by rwa [htrim])
  have hgi : Integrable (μ[f | m]) μ.completion :=
    integrable_of_integrable_trim h0 (by rw [htrim]; exact integrable_condExp)
  have hg : StronglyMeasurable[m] (μ[f | m]) := stronglyMeasurable_condExp
  apply ae_eq_condExp_of_forall_setIntegral_eq hc hfi' (fun _ _ _ => hgi.integrableOn)
    (fun s hs _ => ?_) (hg.mono hmc).aestronglyMeasurable
  obtain ⟨t,ht,he⟩ := hs
  have hst : s =ᵐ[μ.completion] t := he
  calc
    ∫ x in s, (μ[f | m]) x ∂μ.completion = ∫ x in t, (μ[f | m]) x ∂μ.completion :=
      setIntegral_congr_set hst
    _ = ∫ x in t, (μ[f | m]) x ∂μ := by
      have h := setIntegral_trim (X := Ω) (m := mΩ)
        (m0 := inferInstanceAs (MeasurableSpace (NullMeasurableSpace Ω μ)))
        (μ := μ.completion) h0 (hg.mono hm) (hm t ht)
      rw [htrim] at h
      convert h using 1 <;> rfl
    _ = ∫ x in t, f x ∂μ := setIntegral_condExp hm hfi ht
    _ = ∫ x in t, f x ∂μ.completion := by
      have h := (setIntegral_trim (X := Ω) (m := mΩ)
        (m0 := inferInstanceAs (MeasurableSpace (NullMeasurableSpace Ω μ)))
        (μ := μ.completion) h0 hf (hm t ht)).symm
      rw [htrim] at h
      convert h using 1 <;> rfl
    _ = ∫ x in s, f x ∂μ.completion := setIntegral_congr_set hst.symm

/-- The independent-seed posterior identity holds under the completed enlarged field itself.
Completion uses the actual product law, and every radius still estimates the fixed Q0. -/
theorem actual_completed_posterior {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (r : ℕ) (a : Label) :
    (fun z : Process × U => ((joint : Measure Process)[targetIndicator a | pastField r]) z.1)
      =ᵐ[(joint : Measure Process).prod ν]
      (((joint : Measure Process).prod ν).completion)[fun z => targetIndicator a z.1 |
        pastFiltration ν r] := by
  let μ := (joint : Measure Process).prod ν
  have ht : Measurable target := by
    exact (measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst)
  have hti : Integrable (targetIndicator a) (joint : Measure Process) :=
    (integrable_const (μ := (joint : Measure Process)) (1 : ℝ)).indicator
      (ht (measurableSet_singleton a))
  have hp : Measurable (pastWord r) :=
    Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd
  have hb := product_condExp (joint : Measure Process) ν hp.comap_le (targetIndicator a) hti
  have hf : StronglyMeasurable (fun z : Process × U => targetIndicator a z.1) := by
    exact ((stronglyMeasurable_const.indicator (ht (measurableSet_singleton a))).comp_measurable
      measurable_fst)
  exact hb.trans (completion_condExp (enlarged (pastField r)) μ (enlarged_le r) _ hf
    (hti.comp_fst ν))

#print axioms actual_completed_posterior

/-- Every positive event observable at a finite completed past radius has positive error
when it returns a specified actual time-zero class, even with the whole independent seed. -/
theorem local_positive_error {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (r : ℕ) (a : Label) (E : Set (Process × U))
    (hE : MeasurableSet[pastFiltration ν r] E)
    (hpos : 0 < ((joint : Measure Process).prod ν) E) :
    0 < ((joint : Measure Process).prod ν) (E ∩ {z | target z.1 ≠ a}) := by
  let μ := (joint : Measure Process).prod ν
  obtain ⟨B,hB,hEB⟩ := hE
  have hB' : MeasurableSet[enlarged (pastField (r+1))] B :=
    enlarged_mono (past_succ r) B hB
  have hm := enlarged_le (U := U) (r+1)
  have hBm : MeasurableSet B := hm B hB'
  have hBpos : 0 < μ B := by rwa [measure_congr hEB] at hpos
  suffices h : 0 < μ (B ∩ {z | target z.1 ≠ a}) by
    have he : (E ∩ {z : Process × U | target z.1 ≠ a} : Set (Process × U)) =ᵐ[μ]
        (B ∩ {z : Process × U | target z.1 ≠ a} : Set (Process × U)) := by
      filter_upwards [hEB] with z hz
      exact propext (and_congr (iff_of_eq hz) Iff.rfl)
    rwa [measure_congr he]
  by_contra hn
  have hz : μ (B ∩ {z | target z.1 ≠ a}) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  let f : Process × U → ℝ := fun z => targetIndicator a z.1
  have hf : Integrable f μ := by
    have htm : Measurable (fun z : Process × U => target z.1) := by
      change Measurable (fun z : Process × U => label (z.1.1 0))
      exact (measurable_of_countable label).comp
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_fst))
    apply ((integrable_const (μ := μ) (1 : ℝ)).indicator
      (htm (measurableSet_singleton a))).congr
    exact Filter.Eventually.of_forall fun z => by simp [f,targetIndicator,Set.indicator]
  have hgood : ∀ᵐ z ∂μ, z ∈ B → target z.1 = a := by
    simpa only [ae_iff,Classical.not_imp,Set.inter_def,Set.mem_setOf_eq] using hz
  have hi : ∫ z in B, f z ∂μ = μ.real B := by
    calc
      _ = ∫ _ in B, (1 : ℝ) ∂μ := setIntegral_congr_ae hBm (hgood.mono fun z hz hb => by
        simp [f,targetIndicator,hz hb])
      _ = _ := by simp
  have hc : ∫ z in B, (μ[f | enlarged (pastField (r+1))]) z ∂μ = μ.real B :=
    (setIntegral_condExp hm hf hB').trans hi
  have hlt : ∀ᵐ z ∂μ, (μ[f | enlarged (pastField (r+1))]) z < 1 :=
    (actual_seeded_support ν r a).2.mono fun _ h => h.2
  let g : Process × U → ℝ := fun z => 1 - (μ[f | enlarged (pastField (r+1))]) z
  have hg : Integrable g μ := (integrable_const 1).sub integrable_condExp
  have hgpos : ∀ᵐ z ∂μ, 0 < g z := hlt.mono fun _ h => sub_pos.mpr h
  have hs : (Function.support g ∩ B : Set (Process × U)) =ᵐ[μ] B := by
    filter_upwards [hgpos] with z hz
    change (g z ≠ 0 ∧ z ∈ B) = (z ∈ B)
    exact propext (and_iff_right (ne_of_gt hz))
  have hp : 0 < ∫ z in B, g z ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_ae (hgpos.mono fun _ h => h.le)) hg.integrableOn).mpr
        (by rwa [measure_congr hs])
  have hzero : ∫ z in B, g z ∂μ = 0 := by
    change (∫ z in B, (1 : ℝ) - (μ[f | enlarged (pastField (r+1))]) z ∂μ) = 0
    rw [integral_sub (integrable_const (μ := μ.restrict B) (1 : ℝ))
      (integrable_condExp (μ := μ) (m := enlarged (pastField (r+1))) (f := f)).integrableOn, hc]
    simp
  linarith

/-- Every class choice observable on a positive completed finite-past event has
positive actual error there. Observability is required only on that event. -/
theorem local_choice_positive_error {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (r : ℕ) (E : Set (Process × U))
    (C : Process × U → Label)
    (hchoice : ∀ a, MeasurableSet[pastFiltration ν r] (E ∩ {z | C z = a}))
    (hpos : 0 < ((joint : Measure Process).prod ν) E) :
    0 < ((joint : Measure Process).prod ν) (E ∩ {z | C z ≠ target z.1}) := by
  let μ := (joint : Measure Process).prod ν
  have he : E = ⋃ a : Label, E ∩ {z | C z = a} := by ext z; simp
  obtain ⟨a,ha⟩ : ∃ a : Label, 0 < μ (E ∩ {z | C z = a}) := by
    by_contra hn
    have hz : ∀ a : Label, μ (E ∩ {z | C z = a}) = 0 :=
      fun a => le_antisymm (le_of_not_gt (fun h => hn ⟨a,h⟩)) bot_le
    have hnul : μ E = 0 := by rw [he]; exact measure_iUnion_null hz
    exact (ne_of_gt hpos) hnul
  apply (local_positive_error ν r a _ (hchoice a) ha).trans_le (measure_mono _)
  rintro z ⟨⟨hE,hC⟩,hne⟩
  change C z = a at hC
  exact ⟨hE,fun he => hne ((hC.symm.trans he).symm)⟩

#print axioms local_choice_positive_error

/-- An observable returned class at each finite return radius supplies a genuine possibly
infinite stopping time. Positive probability of any finite return forces positive error. -/
theorem finite_return_error {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν]
    (τ : Process × U → WithTop ℕ) (A : Process × U → Label)
    (hreturn : ∀ r a, MeasurableSet[pastFiltration ν r]
      {z | τ z = (r : WithTop ℕ) ∧ A z = a}) :
    IsStoppingTime (pastFiltration ν) τ ∧
    (0 < ((joint : Measure Process).prod ν) {z | τ z ≠ ⊤} →
      0 < ((joint : Measure Process).prod ν) {z | τ z ≠ ⊤ ∧ A z ≠ target z.1}) := by
  constructor
  · apply isStoppingTime_of_measurableSet_eq
    intro r
    have he : {z | τ z = (r : WithTop ℕ)} =
        ⋃ a : Label, {z | τ z = (r : WithTop ℕ) ∧ A z = a} := by
      ext z
      simp
    exact (MeasurableSet.iUnion (hreturn r)).congr he.symm
  · intro hpos
    let μ := (joint : Measure Process).prod ν
    have he : {z | τ z ≠ ⊤} =
        ⋃ r : ℕ, ⋃ a : Label, {z | τ z = (r : WithTop ℕ) ∧ A z = a} := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp h
        exact ⟨r,A z,hr.symm,rfl⟩
      · rintro ⟨r,a,hr,_⟩
        rw [hr]
        exact WithTop.coe_ne_top
    obtain ⟨r,a,hcell⟩ : ∃ (r : ℕ) (a : Label), 0 < μ {z | τ z = (r : WithTop ℕ) ∧ A z = a} := by
      by_contra hn
      have hz : ∀ (r : ℕ) (a : Label), μ {z | τ z = (r : WithTop ℕ) ∧ A z = a} = 0 := by
        intro r a
        exact le_antisymm (le_of_not_gt fun h => hn ⟨r,a,h⟩) bot_le
      have hnull : μ {z | τ z ≠ ⊤} = 0 := by
        rw [he]
        exact measure_iUnion_null fun r => measure_iUnion_null (hz r)
      exact (ne_of_gt hpos) hnull
    have herr := local_choice_positive_error ν r
      {z | τ z = (r : WithTop ℕ) ∧ A z = a} (fun _ => a)
      (fun b => by
        by_cases hb : a = b
        · simpa only [hb,Set.setOf_true,Set.inter_univ] using hreturn r b
        · simp only [hb,Set.setOf_false,Set.inter_empty]; exact @MeasurableSet.empty _ (pastFiltration ν r)) hcell
    apply herr.trans_le (measure_mono _)
    rintro z ⟨⟨hr,ha⟩,hne⟩
    exact ⟨by rw [hr]; exact WithTop.coe_ne_top, by simpa [ha,ne_comm] using hne⟩

#print axioms local_positive_error
#print axioms finite_return_error
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetStopping
