/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/IndependentSeedPosterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent product seeds preserve conditional posteriors of the original twelve-state target. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.CondDistrib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set
open scoped Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.IndependentSeedPosterior

/-- Adjoining the whole seed coordinate to the old information on the process coordinate. -/
def enlarged {Ω U : Type*} [MeasurableSpace U] (m : MeasurableSpace Ω) :
    MeasurableSpace (Ω × U) := @Prod.instMeasurableSpace Ω U m inferInstance

theorem product_condExp {Ω U : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω]
    [mU : MeasurableSpace U] (μ : Measure Ω) (ν : Measure U)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : m ≤ mΩ) (f : Ω → ℝ) (hf : Integrable f μ) :
    (fun z : Ω × U => (μ[f | m]) z.1) =ᵐ[μ.prod ν]
      (μ.prod ν)[fun z : Ω × U => f z.1 | enlarged m] := by
  have hmP : enlarged (U := U) m ≤ @Prod.instMeasurableSpace Ω U mΩ mU :=
    sup_le (le_trans (MeasurableSpace.comap_mono hm) le_sup_left) le_sup_right
  have hfp : Integrable (fun z : Ω × U => f z.1) (μ.prod ν) := hf.comp_fst ν
  have hgp : Integrable (fun z : Ω × U => (μ[f | m]) z.1) (μ.prod ν) :=
    (integrable_condExp (μ := μ) (m := m) (f := f)).comp_fst ν
  have rect (s : Set Ω) (t : Set U) (hs : MeasurableSet[m] s) :
      ∫ z in s ×ˢ t, (μ[f | m]) z.1 ∂μ.prod ν =
        ∫ z in s ×ˢ t, f z.1 ∂μ.prod ν := by
    have hg := setIntegral_prod_mul (μ := μ) (ν := ν) (μ[f | m]) (fun _ : U => (1 : ℝ)) s t
    have hh := setIntegral_prod_mul (μ := μ) (ν := ν) f (fun _ : U => (1 : ℝ)) s t
    simp only [mul_one] at hg hh
    rw [hg,hh,setIntegral_condExp hm hf hs]
  have allsets (s : Set (Ω × U)) (hs : MeasurableSet[enlarged m] s) :
      ∫ z in s, (μ[f | m]) z.1 ∂μ.prod ν = ∫ z in s, f z.1 ∂μ.prod ν := by
    induction s, hs using MeasurableSpace.induction_on_inter
      (@generateFrom_prod Ω U m mU).symm (@isPiSystem_prod Ω U m mU) with
    | empty => simp
    | basic s hs =>
      obtain ⟨s,hs,t,_,rfl⟩ := hs
      exact rect s t hs
    | compl s hs ih =>
      rw [setIntegral_compl (hmP s hs) hgp, setIntegral_compl (hmP s hs) hfp, ih]
      have hu := rect Set.univ Set.univ MeasurableSet.univ
      simpa using hu
    | iUnion s hd hs ih =>
      rw [integral_iUnion (fun i => hmP _ (hs i)) hd hgp.integrableOn,
        integral_iUnion (fun i => hmP _ (hs i)) hd hfp.integrableOn]
      simp_rw [ih]
  exact ae_eq_condExp_of_forall_setIntegral_eq hmP hfp
    (fun _ _ _ => hgp.integrableOn) (fun s hs _ => allsets s hs)
    ((stronglyMeasurable_condExp (μ := μ) (m := m) (f := f)).comp_measurable
      (@measurable_fst Ω U m mU)).aestronglyMeasurable

open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation

abbrev Process := MarkedPredictiveQuotient.PathSpace Hidden

/-- The fixed target is the phase/residue label of the original hidden state at time zero. -/
def target (z : MarkedPredictiveQuotient.PathSpace Hidden) : Label := label (z.1 0)

/-- A finite past window keeps the original emitted-bit coordinates and the target at zero. -/
def pastWord (r : ℕ) (z : MarkedPredictiveQuotient.PathSpace Hidden) : Fin r → Bool :=
  fun k => z.2 (-(r : ℤ) + k.val)

def pastField (r : ℕ) : MeasurableSpace (MarkedPredictiveQuotient.PathSpace Hidden) :=
  MeasurableSpace.comap (pastWord r) inferInstance

/-- One representative of each actual two-lift future class. -/
def representative (a : Label) : Hidden :=
  (a.1, ⟨a.2.val, lt_trans a.2.isLt (by decide)⟩)

private theorem representative_label (a : Label) : label (representative a) = a := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact Nat.mod_eq_of_lt a.2.isLt

private theorem class_label (i : Hidden) (a : Label) :
    MarkedPredictiveQuotient.classOf marked i =
      MarkedPredictiveQuotient.classOf marked (representative a) ↔ label i = a := by
  constructor
  · intro h
    exact ((future_classes i (representative a)).mp (Quotient.exact h)).trans (representative_label a)
  · intro h
    exact Quotient.sound ((future_classes i (representative a)).mpr
      (h.trans (representative_label a).symm))

private theorem target_measurable : Measurable target :=
  (measurable_of_countable label).comp ((measurable_pi_apply 0).comp measurable_fst)

private theorem past_measurable (r : ℕ) : Measurable (pastWord r) :=
  Measurable.of_eval fun k => (measurable_pi_apply _).comp measurable_snd

private theorem visible_measurable (t : ℤ) (r : ℕ) (w : Fin r → Bool) :
    MeasurableSet (OriginalMarkedLaw.visibleCylinder t r w) := by
  simp only [OriginalMarkedLaw.visibleCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => (measurableSet_singleton (w k)).preimage
    (measurable_pi_apply (t + k.val))

private theorem past_atom (r : ℕ) (w : Fin r → Bool) :
    ((joint : Measure Process).map (pastWord r)).real {w} =
      (visible : Measure _).real (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r w) := by
  change ((joint : Measure Process).map (pastWord r)).real {w} =
    ((joint : Measure Process).map Prod.snd).real (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r w)
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (past_measurable r) (measurableSet_singleton w),
    Measure.map_apply measurable_snd (visible_measurable _ _ _)]
  congr 2
  ext z
  simp [pastWord, OriginalMarkedLaw.visibleCylinder, funext_iff]

private theorem past_class_atom (r : ℕ) (w : Fin r → Bool) (a : Label) :
    ((joint : Measure Process).map (fun z => (pastWord r z,target z))).real ({w} ×ˢ {a}) =
      (joint : Measure Process).real (MarkedPredictiveQuotient.endpointEvent marked (-(r : ℤ)) r w
        (MarkedPredictiveQuotient.classOf marked (representative a))) := by
  rw [measureReal_def, Measure.map_apply ((past_measurable r).prodMk target_measurable)
    ((measurableSet_singleton w).prod (measurableSet_singleton a))]
  change ((joint : Measure Process) _).toReal = ((joint : Measure Process) _).toReal
  congr 2
  ext z
  simp only [Set.mem_preimage,Set.mem_prod,Set.mem_singleton_iff,
    MarkedPredictiveQuotient.endpointEvent,Set.mem_ofPred_eq]
  rw [show -(r : ℤ) + r = 0 by omega, class_label]
  simp only [target,pastWord,funext_iff]

private theorem conditional_ratio (r : ℕ) (w : Fin r → Bool)
    (hw : 0 < (visible : Measure _).real
      (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r w)) (a : Label) :
    ((ProbabilityTheory.condDistrib target (pastWord r) (joint : Measure Process) w) {a}).toReal =
      atomPosterior (-(r : ℤ)) r w (representative a) := by
  have hp : ((joint : Measure Process).map (pastWord r)) {w} ≠ 0 := by
    intro hz
    have he := past_atom r w
    have hz' : (((joint : Measure Process).map (pastWord r)).real {w}) = 0 := by
      simp [measureReal_def,hz]
    rw [hz'] at he
    exact (ne_of_gt hw) he.symm
  rw [ProbabilityTheory.condDistrib_apply_of_ne_zero (past_measurable r) target_measurable w hp,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (((joint : Measure Process).map (pastWord r)).real {w})⁻¹ *
    (((joint : Measure Process).map (fun z => (pastWord r z,target z))).real ({w} ×ˢ {a})) = _
  rw [past_atom,past_class_atom]
  simp only [atomPosterior,div_eq_mul_inv,mul_comm]

/-- The actual regular conditional distribution agrees with the original-law finite-cell ratio,
and its support after a positive nonempty past word is exactly the three last-phase classes. -/
theorem actual_conditional_distribution (n : ℕ) (w : Fin (n+1) → Bool)
    (hw : 0 < (visible : Measure _).real
      (OriginalMarkedLaw.visibleCylinder (-((n+1 : ℕ) : ℤ)) (n+1) w)) (a : Label) :
    ((ProbabilityTheory.condDistrib target (pastWord (n+1)) (joint : Measure Process) w) {a}).toReal =
      atomPosterior (-((n+1 : ℕ) : ℤ)) (n+1) w (representative a) ∧
    (0 < ((ProbabilityTheory.condDistrib target (pastWord (n+1)) (joint : Measure Process) w) {a}).toReal
      ↔ a.1 = w (Fin.last n)) := by
  have he := conditional_ratio (n+1) w hw a
  refine ⟨he,?_⟩
  rw [he]
  exact actual_atom_posterior_support _ n w hw (representative a)

/-- With the empty observation, the native conditional distribution is the actual joint-law
class marginal; every one of the six singleton probabilities is strictly positive. -/
theorem actual_empty_conditional_distribution (a : Label) :
    ((ProbabilityTheory.condDistrib target (pastWord 0) (joint : Measure Process)
      (fun i => nomatch i)) {a}).toReal =
        (joint : Measure Process).real {z | target z = a} ∧
    0 < ((ProbabilityTheory.condDistrib target (pastWord 0) (joint : Measure Process)
      (fun i => nomatch i)) {a}).toReal := by
  let w : Fin 0 → Bool := fun i => nomatch i
  have hw : 0 < (visible : Measure _).real (OriginalMarkedLaw.visibleCylinder 0 0 w) :=
    (actual_visible_support 0 0 w).mpr trivial
  have hc := conditional_ratio 0 w (by simpa using hw) a
  have he : MarkedPredictiveQuotient.endpointEvent marked 0 0 w
      (MarkedPredictiveQuotient.classOf marked (representative a)) = {z | target z = a} := by
    ext z
    simp [MarkedPredictiveQuotient.endpointEvent, class_label, target]
  have hv : OriginalMarkedLaw.visibleCylinder 0 0 w = Set.univ := by
    ext z
    simp [OriginalMarkedLaw.visibleCylinder]
  have hc' : ((ProbabilityTheory.condDistrib target (pastWord 0) (joint : Measure Process) w) {a}).toReal =
      (joint : Measure Process).real {z | target z = a} := by
    simpa only [Nat.cast_zero,neg_zero,atomPosterior,he,hv,measureReal_def,measure_univ,ENNReal.toReal_one,div_one] using hc
  refine ⟨hc',?_⟩
  rw [hc',← he]
  exact actual_empty_support 0 (representative a)


private theorem past_positive (r : ℕ) :
    ∀ᵐ z ∂(joint : Measure Process),
      0 < (visible : Measure _).real (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r (pastWord r z)) := by
  have hall (w : Fin r → Bool) : ∀ᵐ z ∂(joint : Measure Process), pastWord r z = w →
      0 < (visible : Measure _).real (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r w) := by
    by_cases hp : 0 < (visible : Measure _).real (OriginalMarkedLaw.visibleCylinder (-(r : ℤ)) r w)
    · exact Filter.Eventually.of_forall fun _ _ => hp
    · have hz : ((joint : Measure Process).map (pastWord r)) {w} = 0 := by
        apply (measureReal_eq_zero_iff (μ := (joint : Measure Process).map (pastWord r))
          (s := {w})).mp
        rw [past_atom]
        exact le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
      have hnull : (joint : Measure Process) {z | pastWord r z = w} = 0 := by
        rw [Measure.map_apply (past_measurable r) (measurableSet_singleton w)] at hz
        exact hz
      have hae : ∀ᵐ z ∂(joint : Measure Process), pastWord r z ≠ w := by
        simpa only [ae_iff,not_not] using hnull
      filter_upwards [hae] with z hz he
      exact (hz he).elim
  have h := ae_all_iff.mpr hall
  filter_upwards [h] with z hz
  exact hz (pastWord r z) rfl

private theorem kernel_lt_one (n : ℕ) (w : Fin (n+1) → Bool)
    (hw : 0 < (visible : Measure _).real
      (OriginalMarkedLaw.visibleCylinder (-((n+1 : ℕ) : ℤ)) (n+1) w)) (a : Label) :
    ((ProbabilityTheory.condDistrib target (pastWord (n+1)) (joint : Measure Process) w) {a}).toReal < 1 := by
  let K := ProbabilityTheory.condDistrib target (pastWord (n+1)) (joint : Measure Process) w
  obtain ⟨b,hb,hba⟩ : ∃ b : MarkedPredictiveQuotient.FutureClass marked,
      0 < (joint : Measure Process).real
        (MarkedPredictiveQuotient.endpointEvent marked (-((n+1 : ℕ) : ℤ)) (n+1) w b) ∧
      b ≠ MarkedPredictiveQuotient.classOf marked (representative a) := by
    by_contra hn
    apply no_synchronizing_word
    refine ⟨-((n+1 : ℕ) : ℤ),n+1,w,MarkedPredictiveQuotient.classOf marked (representative a),hw,?_⟩
    intro b hb
    by_contra hba
    exact hn ⟨b,hb,hba⟩
  let j : Hidden := b.out
  have hj : MarkedPredictiveQuotient.classOf marked j = b := Quotient.out_eq b
  have hr : MarkedPredictiveQuotient.classOf marked (representative (label j)) = b := by
    exact (Quotient.sound ((future_classes (representative (label j)) j).mpr
      (representative_label (label j)))).trans hj
  have hne : label j ≠ a := by
    intro he
    apply hba
    rw [← hr,he]
  have hpos : 0 < K.real {label j} := by
    change 0 < ((ProbabilityTheory.condDistrib target (pastWord (n+1)) (joint : Measure Process) w) {label j}).toReal
    rw [(actual_conditional_distribution n w hw (label j)).1]
    unfold atomPosterior
    rw [hr]
    exact div_pos hb hw
  have hcomp : 0 < K.real ({a}ᶜ) := hpos.trans_le (measureReal_mono (by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact hne))
  have hsum : K.real {a} + K.real ({a}ᶜ) = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := K) (measurableSet_singleton a)
  change K.real {a} < 1
  linarith

/-- Indicator of one of the six actual time-zero classes. -/
def targetIndicator (a : Label) : Process → ℝ :=
  (target ⁻¹' {a}).indicator (fun _ => 1)

/-- Independent whole-process seeds preserve the actual finite-past posterior and its
three-class support. Each class probability stays strictly below one at every positive radius. -/
theorem actual_seeded_support {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (n : ℕ) (a : Label) :
    (fun z : Process × U => ((joint : Measure Process)[targetIndicator a | pastField (n+1)]) z.1)
      =ᵐ[(joint : Measure Process).prod ν]
        ((joint : Measure Process).prod ν)[fun z => targetIndicator a z.1 | enlarged (pastField (n+1))] ∧
    ∀ᵐ z ∂(joint : Measure Process).prod ν,
      (0 < (((joint : Measure Process).prod ν)[fun z => targetIndicator a z.1 |
          enlarged (pastField (n+1))]) z ↔ a.1 = pastWord (n+1) z.1 (Fin.last n)) ∧
      (((joint : Measure Process).prod ν)[fun z => targetIndicator a z.1 |
        enlarged (pastField (n+1))]) z < 1 := by
  have hf : Integrable (targetIndicator a) (joint : Measure Process) := by
    exact (integrable_const (μ := (joint : Measure Process)) (1 : ℝ)).indicator
      (target_measurable (measurableSet_singleton a))
  have hm : pastField (n+1) ≤ (inferInstance : MeasurableSpace Process) := (past_measurable (n+1)).comap_le
  have hbridge := product_condExp (joint : Measure Process) ν hm (targetIndicator a) hf
  have hk := ProbabilityTheory.condDistrib_ae_eq_condExp (μ := (joint : Measure Process))
    (past_measurable (n+1)) target_measurable (measurableSet_singleton a)
  have hkernel : (fun z => ((ProbabilityTheory.condDistrib target (pastWord (n+1))
      (joint : Measure Process) (pastWord (n+1) z)) {a}).toReal) =ᵐ[(joint : Measure Process)]
      (joint : Measure Process)[targetIndicator a | pastField (n+1)] := by
    exact hk
  have hlift := (Measure.quasiMeasurePreserving_fst (μ := (joint : Measure Process)) (ν := ν)).ae hkernel
  have hpos := (Measure.quasiMeasurePreserving_fst (μ := (joint : Measure Process)) (ν := ν)).ae
    (past_positive (n+1))
  refine ⟨hbridge,?_⟩
  filter_upwards [hbridge,hlift,hpos] with z hb hk hp
  rw [← hb,← hk]
  exact ⟨(actual_conditional_distribution n (pastWord (n+1) z.1) hp a).2,
    kernel_lt_one n (pastWord (n+1) z.1) hp a⟩

#print axioms actual_seeded_support

#print axioms actual_conditional_distribution


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.IndependentSeedPosterior
