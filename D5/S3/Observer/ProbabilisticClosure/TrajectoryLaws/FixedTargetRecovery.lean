/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same-law fixed-Q0 MAP estimates stabilize and their posterior converges to the target Dirac mass. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetStopping
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateTail
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePosteriorDiracStopping
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators Classical Topology ENNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalFutureScreening
open OriginalErasureComparison PositiveSupportPresentation TwelveStatePresentation
open IndependentSeedPosterior FixedTargetStopping TwelveStateTail

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetRecovery

/-- The raw increasing past information estimates one target at time zero. -/
def pastInformation : Filtration ℕ (inferInstance : MeasurableSpace Process) where
  seq := pastField
  mono' := monotone_nat_of_le_succ past_succ
  le' r := (Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd).comap_le

/-- Fixed-order MAP choices from the original actual cell-mass maximizers. -/
def fixedMAP (r : ℕ) (w : Fin r → Bool) : Label :=
  labelEquiv (Classical.choose (current_map_error parameter r) w)

/-- The native conditional-law posterior on the actual positive or null finite word. -/
def posterior (r : ℕ) (a : Label) (z : Process) : ℝ :=
  (ProbabilityTheory.condDistrib target (pastWord r) (joint : Measure Process) (pastWord r z)).real {a}

private theorem map_measurable (r : ℕ) :
    Measurable[pastField r] (fun z : Process => fixedMAP r (pastWord r z)) :=
  (measurable_of_finite (fixedMAP r)).comp (Measurable.of_comap_le le_rfl)

private theorem class_label (z : Process) : labelEquiv (originalClass parameter 0 z) = target z := by
  change label (retainState parameter (z.1 0)).val = label (z.1 0)
  simp only [retainState,dif_pos (show 0 < parameter.initial (z.1 0) from mass_pos _)]

private theorem map_error (r : ℕ) :
    (joint : Measure Process) {z | target z ≠ fixedMAP r (pastWord r z)} = classError parameter r := by
  have hm := (Classical.choose_spec (current_map_error parameter r)).1
  rw [← hm]
  apply congrArg (fun E : Set Process => (joint : Measure Process) E)
  ext z
  change target z ≠ labelEquiv _ ↔ originalClass parameter 0 z ≠ _
  rw [← class_label]
  exact not_congr labelEquiv.injective.eq_iff

private theorem posterior_condExp (r : ℕ) (a : Label) :
    posterior r a =ᵐ[(joint : Measure Process)]
      (joint : Measure Process)[targetIndicator a | pastField r] := by
  exact ProbabilityTheory.condDistrib_ae_eq_condExp
    (Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd)
    ((measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst))
    (measurableSet_singleton a)

private theorem ae_condExp_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ)
    (hf : Integrable f μ) (hfm : AEStronglyMeasurable[⨆ r, ℱ r] f μ) :
    ∀ᵐ z ∂μ, Tendsto (fun r => (μ[f | ℱ r]) z) atTop (𝓝 (f z)) := by
  have heq := hfm.ae_eq_mk
  have hc := (hf.congr heq).tendsto_ae_condExp (ℱ := ℱ) hfm.stronglyMeasurable_mk
  have hall : ∀ᵐ z ∂μ, ∀ r, (μ[f | ℱ r]) z = (μ[hfm.mk f | ℱ r]) z :=
    ae_all_iff.mpr fun r => condExp_congr_ae heq
  filter_upwards [hc,heq,hall] with z hz he hh
  simpa only [he] using hz.congr' (Eventually.of_forall fun r => (hh r).symm)

/-- On the single original J, MAP error has the explicit geometric bound and the fixed-Q0
estimates are eventually correct. Each posterior coordinate converges to the target indicator;
the same is true after any independent whole-process seed and completed enlargement. -/
theorem actual_map_recovery :
    (∀ r : ℕ, (joint : Measure Process) {z | target z ≠ fixedMAP r (pastWord r z)} ≤
      ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2))) ∧
    (∀ᵐ z ∂(joint : Measure Process), ∀ᶠ r : ℕ in atTop, target z = fixedMAP r (pastWord r z)) ∧
    (∀ a : Label, AEStronglyMeasurable[⨆ r, pastField r] (targetIndicator a) (joint : Measure Process) ∧
      (∀ᵐ z ∂(joint : Measure Process), Tendsto (fun r => posterior r a z) atTop (𝓝 (targetIndicator a z))) ∧
      ∀ (U : Type*) [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν],
        ∀ᵐ z ∂(joint : Measure Process).prod ν,
          Tendsto (fun r => (((joint : Measure Process).prod ν).completion)[fun z => targetIndicator a z.1 | pastFiltration ν r] z) atTop (𝓝 (targetIndicator a z.1))) := by
  have ht := actual_explicit_tail
  have hbound (r : ℕ) := (ht.2.2.1 r).1
  have hsum : (∑' r : ℕ, (joint : Measure Process) {z | target z ≠ fixedMAP r (pastWord r z)}) ≠ ⊤ := by
    simpa only [map_error] using ht.2.2.2.2
  have hevent : ∀ᵐ z ∂(joint : Measure Process), ∀ᶠ r : ℕ in atTop, target z = fixedMAP r (pastWord r z) := by
    simpa only [Set.mem_setOf_eq,not_not] using ae_eventually_notMem hsum
  refine ⟨fun r => by rw [map_error]; exact hbound r,hevent,?_⟩
  intro a
  let S : Set Process := {z | ∀ᶠ r : ℕ in atTop, fixedMAP r (pastWord r z) = a}
  have hS : MeasurableSet[⨆ r, pastField r] S := by
    have he : S = ⋃ n : ℕ, ⋂ r : ℕ, ⋂ (_ : n ≤ r), {z | fixedMAP r (pastWord r z) = a} := by
      ext z
      simp only [S,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_iInter,eventually_atTop]
    rw [he]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun r =>
      MeasurableSet.iInter fun _ => (le_iSup pastField r) _
        ((map_measurable r) (measurableSet_singleton a))
  have hAES : AEStronglyMeasurable[⨆ r, pastField r] (targetIndicator a) (joint : Measure Process) := by
    refine ⟨S.indicator (fun _ => (1 : ℝ)),stronglyMeasurable_const.indicator hS,?_⟩
    filter_upwards [hevent] with z hz
    have he : z ∈ S ↔ target z = a := by
      constructor
      · intro hs
        obtain ⟨r,hr,hra⟩ := (hz.and hs).exists
        exact hr.trans hra
      · intro ha
        exact hz.mono fun r hr => hr.symm.trans ha
    simp only [targetIndicator,Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    by_cases h : target z = a
    · simp only [if_pos h,if_pos (he.mpr h)]
    · simp only [if_neg h,if_neg (fun hs => h (he.mp hs))]
  have hi : Integrable (targetIndicator a) (joint : Measure Process) :=
    (integrable_const 1).indicator
      (((measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst)) (measurableSet_singleton a))
  have hc := ae_condExp_convergence (joint : Measure Process) pastInformation (targetIndicator a) hi hAES
  refine ⟨hAES,?_,?_⟩
  · have hall := ae_all_iff.mpr fun r => posterior_condExp r a
    filter_upwards [hc,hall] with z hz hh
    exact hz.congr' (Eventually.of_forall fun r => (hh r).symm)
  · intro U _ ν _
    have hlift := (Measure.quasiMeasurePreserving_fst (μ := (joint : Measure Process)) (ν := ν)).ae hc
    have hall := ae_all_iff.mpr fun r => actual_completed_posterior ν r a
    filter_upwards [hlift,hall] with z hz hh
    exact hz.congr' (Eventually.of_forall hh)

#print axioms actual_map_recovery

private def seededInformation {U : Type*} [MeasurableSpace U] (ν : Measure U) :
    Filtration ℕ (inferInstance : MeasurableSpace
      (NullMeasurableSpace (Process × U) ((joint : Measure Process).prod ν))) where
  seq r := pastFiltration ν r
  mono' := fun _ _ h => (pastFiltration ν).mono h
  le' r s hs := by
    obtain ⟨t,ht,he⟩ := (pastFiltration ν).le r s hs
    exact ht.nullMeasurableSet.congr he.symm

/-- An actual observable return is allowed to be infinite, but this class requires it to
return at a finite radius almost surely. Its information is completed under the common product law. -/
def admissible {U : Type*} [MeasurableSpace U] (ν : Measure U)
    (τ : Process × U → WithTop ℕ) (A : Process × U → Label) : Prop :=
  (∀ r a, MeasurableSet[pastFiltration ν r] {z | τ z = (r : WithTop ℕ) ∧ A z = a}) ∧
  ∀ᵐ z ∂(joint : Measure Process).prod ν, τ z ≠ ⊤

/-- Infimum over every almost-surely finite observable stopped classifier with this seed law. -/
def stoppingErrorInf {U : Type*} [MeasurableSpace U] (ν : Measure U) : ℝ≥0∞ :=
  ⨅ (τ : Process × U → WithTop ℕ) (A : Process × U → Label) (_ : admissible ν τ A),
    ((joint : Measure Process).prod ν) {z | A z ≠ target z.1}

/-- For any measurable independent whole-process seed, the actual stopped-error infimum is
zero and every almost-surely finite observable stopped classifier has strictly positive error.
In particular each finite-radius actual MAP error is positive. -/
theorem actual_zero_unattained_infimum {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] :
    stoppingErrorInf ν = 0 ∧
    (∀ (τ : Process × U → WithTop ℕ) (A : Process × U → Label), admissible ν τ A →
      IsStoppingTime (pastFiltration ν) τ ∧
      0 < ((joint : Measure Process).prod ν) {z | A z ≠ target z.1}) ∧
    ∀ r : ℕ, 0 < (joint : Measure Process) {z | target z ≠ fixedMAP r (pastWord r z)} := by
  let μ := (joint : Measure Process).prod ν
  letI : IsProbabilityMeasure μ.completion := ⟨by change μ Set.univ = 1; simp⟩
  let p : ℕ → Label → Process × U → ℝ := fun r a z => posterior r a z.1
  have hpm (r : ℕ) (a : Label) : Measurable[seededInformation ν r] (p r a) := by
    have hraw : Measurable[pastField r] (posterior r a) :=
      (ProbabilityTheory.measurable_condDistrib (measurableSet_singleton a)).ennreal_toReal
    have hprod : Measurable[enlarged (pastField r)] (p r a) :=
      hraw.comp (@measurable_fst Process U (pastField r) inferInstance)
    exact hprod.mono (fun s hs => ⟨s,hs,Filter.EventuallyEq.rfl⟩) le_rfl
  have hprob (r : ℕ) (z : Process × U) : (∀ a, 0 ≤ p r a z) ∧ ∑ a, p r a z = 1 := by
    refine ⟨fun _ => ENNReal.toReal_nonneg,?_⟩
    dsimp [p,posterior]
    rw [sum_measureReal_singleton]
    simp
  have hpost (r : ℕ) (a : Label) : p r a =ᵐ[μ.completion]
      μ.completion[FinitePosteriorDiracStopping.indicator (fun z => target z.1) a | seededInformation ν r] := by
    have hk : (fun z : Process × U => posterior r a z.1) =ᵐ[μ]
        (fun z => (joint : Measure Process)[targetIndicator a | pastField r] z.1) :=
      (Measure.quasiMeasurePreserving_fst (μ := (joint : Measure Process)) (ν := ν)).ae
        (posterior_condExp r a)
    exact hk.trans (actual_completed_posterior ν r a)
  have hY : @Measurable (Process × U) Label
      (inferInstanceAs (MeasurableSpace (NullMeasurableSpace (Process × U) μ))) inferInstance
      (fun z => target z.1) := by
    have ht : Measurable target :=
      (measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst)
    have hraw : Measurable (fun z : Process × U => target z.1) := ht.comp measurable_fst
    exact hraw.mono (fun s hs => hs.nullMeasurableSet) le_rfl
  have hcriterion := FinitePosteriorDiracStopping.zero_error_iff_dirac_hitting μ.completion
    (fun z => target z.1) hY (seededInformation ν) p hpm hprob hpost
  have hlt (r : ℕ) (a : Label) : ∀ᵐ z ∂μ.completion, p r a z < 1 := by
    cases r with
    | zero =>
      apply Filter.Eventually.of_forall
      intro z
      let K : Measure Label := ProbabilityTheory.condDistrib target (pastWord 0)
        (joint : Measure Process) (fun i => nomatch i)
      haveI : IsProbabilityMeasure K := by dsimp [K]; infer_instance
      let b : Label := (!a.1,a.2)
      have hba : b ≠ a := by
        intro he
        have hh := congrArg Prod.fst he
        cases h : a.1 <;> simp [b,h] at hh
      have hb : 0 < K.real {b} := by
        convert (actual_empty_conditional_distribution b).2 using 1 <;>
          first | norm_num [K,Measure.real] | skip
        congr 3
      have hc : K.real {b} ≤ K.real ({a}ᶜ) := measureReal_mono (by
        intro c hc
        simp only [Set.mem_singleton_iff] at hc
        subst c
        exact hba)
      have hs := measureReal_add_measureReal_compl (μ := K) (measurableSet_singleton a)
      have hu : K.real Set.univ = 1 := probReal_univ
      rw [hu] at hs
      have he : pastWord 0 z.1 = (fun i => nomatch i) := Subsingleton.elim _ _
      change (ProbabilityTheory.condDistrib target (pastWord 0) (joint : Measure Process) (pastWord 0 z.1)).real {a} < 1
      rw [he]
      change K.real {a} < 1
      linarith
    | succ n =>
      have hk := (Measure.quasiMeasurePreserving_fst (μ := (joint : Measure Process)) (ν := ν)).ae
        (posterior_condExp (n+1) a)
      have hs := actual_seeded_support ν n a
      filter_upwards [hk,hs.1,hs.2] with z hk hb hlt
      change posterior (n+1) a z.1 < 1
      rw [hk,hb]
      exact hlt.2
  have hnever : ∀ᵐ z ∂μ.completion, ¬∃ r, z ∈ FinitePosteriorDiracStopping.diracEvent p r := by
    have hh : ∀ᵐ z ∂μ.completion, ∀ r a, p r a z < 1 :=
      ae_all_iff.mpr fun r => ae_all_iff.mpr (hlt r)
    filter_upwards [hh] with z hz
    rintro ⟨r,a,ha⟩
    exact (ne_of_lt (hz r a)) ha
  have hpositive (τ : Process × U → WithTop ℕ) (A : Process × U → Label)
      (h : admissible ν τ A) : IsStoppingTime (pastFiltration ν) τ ∧ 0 < μ {z | A z ≠ target z.1} := by
    have hτ := (finite_return_error ν τ A h.1).1
    refine ⟨hτ,?_⟩
    by_contra hn
    have hz : μ {z | A z ≠ target z.1} = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have herr : μ.completion {z | τ z ≠ ⊤ ∧ A z ≠ target z.1} = 0 :=
      measure_mono_null (fun _ h => h.2) hz
    have hhit := hcriterion.mp ⟨τ,A,hτ,h.1,h.2,herr⟩
    have hf : ∀ᵐ z ∂μ.completion, False := by
      filter_upwards [hhit,hnever] with z hh hn
      exact hn hh
    exact (Filter.Eventually.exists hf).choose_spec
  have hfixed (r : ℕ) : admissible ν (fun _ => (r : WithTop ℕ))
      (fun z => fixedMAP r (pastWord r z.1)) := by
    constructor
    · intro k a
      by_cases hk : r = k
      · subst k
        have hm : Measurable[enlarged (pastField r)]
            (fun z : Process × U => fixedMAP r (pastWord r z.1)) :=
          (map_measurable r).comp (@measurable_fst Process U (pastField r) inferInstance)
        have hh : MeasurableSet[pastFiltration ν r] {z : Process × U | fixedMAP r (pastWord r z.1) = a} :=
          ⟨_,hm (measurableSet_singleton a),Filter.EventuallyEq.rfl⟩
        simpa using hh
      · have hne : (r : WithTop ℕ) ≠ (k : WithTop ℕ) := fun he => hk (WithTop.coe_eq_coe.mp he)
        have he : {z : Process × U | (r : WithTop ℕ) = (k : WithTop ℕ) ∧
            fixedMAP r (pastWord r z.1) = a} = ∅ := by ext z; simp [hne]
        rw [he]
        exact @MeasurableSet.empty (Process × U) (pastFiltration ν k)
    · exact Filter.Eventually.of_forall fun _ => WithTop.coe_ne_top
  have herr (r : ℕ) : μ {z | fixedMAP r (pastWord r z.1) ≠ target z.1} =
      (joint : Measure Process) {z | target z ≠ fixedMAP r (pastWord r z)} := by
    have hm : MeasurableSet {z : Process | target z ≠ fixedMAP r (pastWord r z)} := by
      have ht : Measurable target := (measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst)
      exact (measurableSet_eq_fun ht ((measurable_of_finite (fixedMAP r)).comp
        (Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd))).compl
    calc
      _ = μ (Prod.fst ⁻¹' {z : Process | target z ≠ fixedMAP r (pastWord r z)}) := by
        congr 1
        ext z
        exact ne_comm
      _ = (μ.map Prod.fst) {z : Process | target z ≠ fixedMAP r (pastWord r z)} :=
        (Measure.map_apply measurable_fst hm).symm
      _ = _ := by simp [μ,Measure.map_fst_prod]
  refine ⟨?_,hpositive,fun r => ?_⟩
  · have hi (r : ℕ) : stoppingErrorInf ν ≤ ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2)) := by
      calc
        _ ≤ μ {z | fixedMAP r (pastWord r z.1) ≠ target z.1} :=
          by
            unfold stoppingErrorInf
            exact iInf_le_of_le (fun _ : Process × U => (r : WithTop ℕ))
              (iInf_le_of_le (fun z : Process × U => fixedMAP r (pastWord r z.1))
                (iInf_le_of_le (hfixed r) le_rfl))
        _ ≤ _ := by rw [herr]; exact actual_map_recovery.{0}.1 r
    have hr := actual_explicit_tail
    have hlim : Tendsto (fun r : ℕ => ENNReal.ofReal ((5/2 : ℝ)*rho^(r/2))) atTop (𝓝 0) := by
      have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2.1).comp
        (Nat.tendsto_div_const_atTop (by decide : (2 : ℕ) ≠ 0))).const_mul (5/2 : ℝ)
      have hh' : Tendsto (fun r : ℕ => (5/2 : ℝ)*rho^(r/2)) atTop (𝓝 0) := by
        simpa only [Function.comp_def,mul_zero] using hh
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp hh'
    exact le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hi)) bot_le
  · have hp := (hpositive _ _ (hfixed r)).2
    rwa [herr] at hp

#print axioms actual_zero_unattained_infimum

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FixedTargetRecovery
