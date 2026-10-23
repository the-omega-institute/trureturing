/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-target zero-error stopping is equivalent to almost-sure finite posterior Dirac hitting. -/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePosteriorDiracStopping
variable {Ω Q : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Q]
  [Fintype Q] [Nonempty Q] [MeasurableSingletonClass Q]

/-- One at the actual target label, zero at every other label. -/
def indicator (Y : Ω → Q) (a : Q) : Ω → ℝ := {ω | Y ω = a}.indicator (fun _ => 1)

private theorem indicator_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Q) (hY : Measurable Y) (a : Q) : Integrable (indicator Y a) μ :=
  (integrable_const 1).indicator (hY (measurableSet_singleton a))

private theorem posterior_certificate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Q) (hY : Measurable Y) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (p : Q → Ω → ℝ) (hpost : ∀ a, p a =ᵐ[μ] μ[indicator Y a | m])
    (hle : ∀ a ω, p a ω ≤ 1) (a : Q) (E : Set Ω) (hE : MeasurableSet[m] E) :
    μ (E ∩ {ω | Y ω ≠ a}) = 0 ↔ ∀ᵐ ω ∂μ, ω ∈ E → p a ω = 1 := by
  letI : MeasurableSpace Ω := mΩ
  have hEm : MeasurableSet E := hm E hE
  have hpi : Integrable (p a) μ := integrable_condExp.congr (hpost a).symm
  have hfi := indicator_integrable μ Y hY a
  have hint : ∫ ω in E, (1 - p a ω) ∂μ = μ.real (E ∩ {ω | Y ω ≠ a}) := by
    rw [integral_sub (integrable_const (μ := μ.restrict E) (1 : ℝ)) hpi.integrableOn]
    have he : (∫ ω in E, p a ω ∂μ) = ∫ ω in E, (μ[indicator Y a | m]) ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hpost a))
    rw [he,setIntegral_condExp hm hfi hE]
    rw [← integral_sub (integrable_const (μ := μ.restrict E) (1 : ℝ)) hfi.integrableOn]
    have hf : (fun ω => 1 - indicator Y a ω) = {ω | Y ω ≠ a}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : Y ω = a <;> simp [indicator,h]
    have hneq : MeasurableSet {ω | Y ω ≠ a} := by
      exact (hY (measurableSet_singleton a)).compl
    rw [hf,integral_indicator hneq]
    simp only [integral_const,smul_eq_mul,mul_one]
    rw [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.restrict_apply hneq,Set.inter_comm]
    rfl
  have hz := integral_eq_zero_iff_of_nonneg (μ := μ.restrict E)
    (f := fun ω => 1 - p a ω) (fun ω => sub_nonneg.mpr (hle a ω))
    ((integrable_const 1).sub hpi.integrableOn)
  rw [hint] at hz
  rw [measureReal_def,ENNReal.toReal_eq_zero_iff] at hz
  simp only [or_iff_left (measure_ne_top μ _),Filter.EventuallyEq,Pi.zero_apply,sub_eq_zero] at hz
  rw [ae_restrict_iff' hEm] at hz
  simpa only [eq_comm] using hz

/-- The posterior is Dirac precisely when one of its finite coordinates equals one. -/
def diracEvent (p : ℕ → Q → Ω → ℝ) (r : ℕ) : Set Ω := {ω | ∃ a, p r a ω = 1}

/-- For a fixed finite target and a nested discrete information filtration, an almost-surely
finite observable zero-error return exists exactly when a finite posterior is Dirac almost surely.
The posterior hypotheses are actual conditional-expectation identities on this same measure. -/
theorem zero_error_iff_dirac_hitting (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Q) (hY : Measurable Y) (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (p : ℕ → Q → Ω → ℝ)
    (hpm : ∀ r a, Measurable[ℱ r] (p r a))
    (hprob : ∀ r ω, (∀ a, 0 ≤ p r a ω) ∧ ∑ a, p r a ω = 1)
    (hpost : ∀ r a, p r a =ᵐ[μ] μ[indicator Y a | ℱ r]) :
    (∃ (τ : Ω → WithTop ℕ) (A : Ω → Q),
      IsStoppingTime ℱ τ ∧
      (∀ r a, MeasurableSet[ℱ r] {ω | τ ω = (r : WithTop ℕ) ∧ A ω = a}) ∧
      (∀ᵐ ω ∂μ, τ ω ≠ ⊤) ∧ μ {ω | τ ω ≠ ⊤ ∧ A ω ≠ Y ω} = 0) ↔
    ∀ᵐ ω ∂μ, ∃ r, ω ∈ diracEvent p r := by
  classical
  have hle (r : ℕ) (a : Q) (ω : Ω) : p r a ω ≤ 1 := by
    rw [← (hprob r ω).2]
    exact Finset.single_le_sum (fun b _ => (hprob r ω).1 b) (Finset.mem_univ a)
  have huniq (r : ℕ) (ω : Ω) (a b : Q) (ha : p r a ω = 1) (hb : p r b ω = 1) : a = b := by
    by_contra hab
    have hsum : p r a ω + p r b ω ≤ ∑ c, p r c ω := by
      calc
        _ = ∑ c ∈ ({a,b} : Finset Q), p r c ω := by simp [hab]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => (hprob r ω).1 c)
    rw [ha,hb,(hprob r ω).2] at hsum
    norm_num at hsum
  have hD (r : ℕ) : MeasurableSet[ℱ r] (diracEvent p r) := by
    have he : diracEvent p r = ⋃ a, {ω | p r a ω = 1} := by ext ω; simp [diracEvent]
    rw [he]
    exact MeasurableSet.iUnion fun a => measurableSet_eq_fun (hpm r a) measurable_const
  constructor
  · rintro ⟨τ,A,_hτ,hreturn,hfin,hzero⟩
    have hc (r : ℕ) (a : Q) : ∀ᵐ ω ∂μ, (τ ω = (r : WithTop ℕ) ∧ A ω = a) → p r a ω = 1 := by
      apply (posterior_certificate μ Y hY (ℱ r) (ℱ.le r) (p r) (hpost r) (hle r) a _ (hreturn r a)).mp
      apply measure_mono_null _ hzero
      rintro ω ⟨⟨hr,ha⟩,hne⟩
      exact ⟨by rw [hr]; exact WithTop.coe_ne_top,by simpa [ha,ne_comm] using hne⟩
    have hall : ∀ᵐ ω ∂μ, ∀ (r : ℕ) (a : Q), (τ ω = (r : WithTop ℕ) ∧ A ω = a) → p r a ω = 1 :=
      ae_all_iff.mpr fun r => ae_all_iff.mpr (hc r)
    filter_upwards [hfin,hall] with ω hf hh
    obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp hf
    exact ⟨r,A ω,hh r (A ω) ⟨hr.symm,rfl⟩⟩
  · intro hhit
    let τ : Ω → WithTop ℕ := fun ω =>
      if h : ∃ r, ω ∈ diracEvent p r then (Nat.find h : WithTop ℕ) else ⊤
    let A : Ω → Q := fun ω =>
      if h : ∃ r, ω ∈ diracEvent p r then Classical.choose (Nat.find_spec h) else Classical.choice inferInstance
    have heq (r : ℕ) : {ω | τ ω = (r : WithTop ℕ)} =
        diracEvent p r ∩ ⋂ k : Fin r, (diracEvent p k.val)ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_compl_iff]
      dsimp only [τ]
      split_ifs with h
      · change ((Nat.find h : WithTop ℕ) = (r : WithTop ℕ)) ↔ _
        have hinj : ((Nat.find h : WithTop ℕ) = (r : WithTop ℕ)) ↔ Nat.find h = r :=
          WithTop.coe_eq_coe
        rw [hinj,Nat.find_eq_iff h]
        exact and_congr_right fun _ => ⟨fun hh k => hh k.val k.isLt,fun hh k hk => hh ⟨k,hk⟩⟩
      · constructor
        · intro he; exact False.elim (WithTop.top_ne_coe he)
        · rintro ⟨hr,_⟩; exact False.elim (h ⟨r,hr⟩)
    have hτr (r : ℕ) : MeasurableSet[ℱ r] {ω | τ ω = (r : WithTop ℕ)} := by
      rw [heq]
      exact (hD r).inter (MeasurableSet.iInter fun k => (ℱ.mono k.isLt.le _ (hD k.val)).compl)
    have hcert (ω : Ω) (r : ℕ) (hr : τ ω = (r : WithTop ℕ)) : p r (A ω) ω = 1 := by
      dsimp only [τ] at hr
      split_ifs at hr with h
      · have he : Nat.find h = r := WithTop.coe_eq_coe.mp hr
        dsimp [A]
        rw [dif_pos h,← he]
        exact Classical.choose_spec (Nat.find_spec h)
      · exact False.elim (WithTop.top_ne_coe hr)
    have hreturn (r : ℕ) (a : Q) : MeasurableSet[ℱ r] {ω | τ ω = (r : WithTop ℕ) ∧ A ω = a} := by
      have he : {ω | τ ω = (r : WithTop ℕ) ∧ A ω = a} =
          {ω | τ ω = (r : WithTop ℕ)} ∩ {ω | p r a ω = 1} := by
        ext ω
        constructor
        · rintro ⟨hr,ha⟩
          exact ⟨hr,by simpa [ha] using hcert ω r hr⟩
        · rintro ⟨hr,ha⟩
          exact ⟨hr,huniq r ω (A ω) a (hcert ω r hr) ha⟩
      rw [he]
      exact (hτr r).inter (measurableSet_eq_fun (hpm r a) measurable_const)
    refine ⟨τ,A,isStoppingTime_of_measurableSet_eq hτr,hreturn,?_,?_⟩
    · filter_upwards [hhit] with ω h
      change (if h : ∃ r, ω ∈ diracEvent p r then (Nat.find h : WithTop ℕ) else ⊤) ≠ ⊤
      rw [dif_pos h]
      exact WithTop.coe_ne_top
    · have hz (r : ℕ) (a : Q) : μ ({ω | τ ω = (r : WithTop ℕ) ∧ A ω = a} ∩ {ω | Y ω ≠ a}) = 0 := by
        apply (posterior_certificate μ Y hY (ℱ r) (ℱ.le r) (p r) (hpost r) (hle r) a _ (hreturn r a)).mpr
        exact Eventually.of_forall fun ω h => by simpa [h.2] using hcert ω r h.1
      apply measure_mono_null (t := ⋃ r : ℕ, ⋃ a : Q,
        {ω | τ ω = (r : WithTop ℕ) ∧ A ω = a} ∩ {ω | Y ω ≠ a}) _
        (measure_iUnion_null fun r => measure_iUnion_null (hz r))
      rintro ω ⟨hf,herr⟩
      obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp hf
      exact Set.mem_iUnion.mpr ⟨r,Set.mem_iUnion.mpr ⟨A ω,⟨⟨hr.symm,rfl⟩,Ne.symm herr⟩⟩⟩

#print axioms zero_error_iff_dirac_hitting
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePosteriorDiracStopping
