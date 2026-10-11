/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite disjoint endpoint events bound the emission clipping cost. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeObserverJointLaw
open NativeInstalledFullLaw NativeStoppedTailRegeneration NativePaidHistoryCommonRowRisks
open ConstantSuspensionSeparator
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

def clampEmission (t : ℝ) : ℝ := max (1/3) (min (2/5) t)

theorem clamp_box (t : ℝ) :
    1/3 ≤ clampEmission t ∧ clampEmission t ≤ 2/5 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

private def readPMF (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : PMF Letter :=
  PMF.ofFintype (fun b => if b = 0 then ENNReal.ofReal t else ENNReal.ofReal (1-t)) (by
    rw [Fin.sum_univ_two]
    simp only [Fin.reduceEq,ite_true,ite_false]
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr ht.2)]
    simp)

/-- The observer and every acquired update remain the original ones. -/
def clampedEmitter {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (M : Observer Z) (e : InstalledEmitter M) :
    InstalledEmitter M where
  emit z := match (M.project z).control with
    | .fourth (.active _) =>
      (readPMF (clampEmission (e.emit z (some (.read 0))).toReal)
        ⟨by have h := (clamp_box (e.emit z (some (.read 0))).toReal).1; linarith,
          by have h := (clamp_box (e.emit z (some (.read 0))).toReal).2; linarith⟩).map
          (fun b => some (.read b))
    | _ => e.emit z
  lawful := by
    intro z a ha
    cases hc : (M.project z).control with
    | seed q => simpa only [hc] using e.lawful z a (by simpa only [hc] using ha)
    | early t s => simpa only [hc] using e.lawful z a (by simpa only [hc] using ha)
    | fourth q =>
      cases q with
      | pending b => simpa only [hc] using e.lawful z a (by simpa only [hc] using ha)
      | delivered => simpa only [hc] using e.lawful z a (by simpa only [hc] using ha)
      | active s =>
        simp only [hc] at ha
        obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
        simp [finiteStep,finiteRead,hc]

/-- A union with one disjoint singleton detects clipping beyond either endpoint. -/
theorem finite_event_clipping_budget {A : Type*} [MeasurableSpace A]
    (P R T : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    [IsProbabilityMeasure T] (E G : Set A) (hE : MeasurableSet E)
    (hG : MeasurableSet G) (hd : Disjoint E G) (a b gap : ℝ)
    (hab : a ≤ b) (ha : P.real G = a) (hb : R.real G = b)
    (he : P.real E - R.real E = gap) :
    |T.real G - max a (min b (T.real G))| ≤
      (measurableTotalVariation T P).toReal +
        (measurableTotalVariation T R).toReal - gap := by
  have hp := event_gap T P E hE
  have hr := event_gap T R E hE
  have hpu := event_gap T P (E ∪ G) (hE.union hG)
  have hru := event_gap T R (E ∪ G) (hE.union hG)
  change |T.real E-P.real E| ≤ _ at hp
  change |T.real E-R.real E| ≤ _ at hr
  change |T.real (E ∪ G)-P.real (E ∪ G)| ≤ _ at hpu
  change |T.real (E ∪ G)-R.real (E ∪ G)| ≤ _ at hru
  rw [measureReal_union hd hG,measureReal_union hd hG,ha] at hpu
  rw [measureReal_union hd hG,measureReal_union hd hG,hb] at hru
  have hp' := (abs_le.mp hp).1
  have hr' := (abs_le.mp hr).2
  have hpu' := (abs_le.mp hpu).1
  have hru' := (abs_le.mp hru).2
  by_cases hlo : T.real G ≤ a
  · rw [min_eq_right (hlo.trans hab),max_eq_left hlo,
      abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  · have hlo' := le_of_lt (lt_of_not_ge hlo)
    by_cases hhi : T.real G ≤ b
    · rw [min_eq_right hhi,max_eq_right hlo',sub_self,abs_zero]
      linarith
    · have hhi' := le_of_lt (lt_of_not_ge hhi)
      rw [min_eq_left hhi',max_eq_right hab,abs_of_nonneg (sub_nonneg.mpr hhi')]
      linarith

private theorem source_stop_p (r : unitInterval) :
    (explicitStoppedWordLaw .p r).real {some [0]} = r := by
  rw [Measure.real,explicit_finite_mass,
    if_pos (show ∃ c, WordFamily .p c [0] from ⟨0,0,rfl⟩)]
  norm_num [wordMass,ProbabilityTheory.bernoulliMeasure,ENNReal.toReal_add,
    ENNReal.toReal_mul,unitInterval.coe_symm_eq]

private theorem source_stop_beta (r : unitInterval) :
    (explicitStoppedWordLaw .beta r).real {some [1]} = 1-(r:ℝ) := by
  rw [Measure.real,explicit_finite_mass,
    if_pos (show ∃ c, WordFamily .beta c [1] from ⟨1,Or.inl ⟨rfl,rfl⟩⟩)]
  norm_num [wordMass,ProbabilityTheory.bernoulliMeasure,ENNReal.toReal_add,
    ENNReal.toReal_mul,unitInterval.coe_symm_eq]

private theorem p_budget (T : Measure RawTail) [IsProbabilityMeasure T] :
    |T.real {some [0]} - clampEmission (T.real {some [0]})| ≤
      (measurableTotalVariation T (explicitStoppedWordLaw .p endpointA)).toReal +
      (measurableTotalVariation T (explicitStoppedWordLaw .p endpointB)).toReal -
        2*(1116529/22781250) := by
  haveI := endpoint_probability .p endpointA
  haveI := endpoint_probability .p endpointB
  apply finite_event_clipping_budget _ _ _ RegularTable.pEvent {some [0]}
    (by trivial) (by trivial) _ (1/3) (2/5) (2*(1116529/22781250)) (by norm_num)
  · exact source_stop_p endpointA
  · exact source_stop_p endpointB
  · rw [endpoint_p_event,endpoint_p_event]
    norm_num [endpointA,endpointB]
  · simp [Set.disjoint_singleton_right,RegularTable.pEvent,pWord,loopWord]

private theorem beta_budget (T : Measure RawTail) [IsProbabilityMeasure T] (v : ℝ)
    (hv : T.real {some [1]} = 1-v) :
    |v-clampEmission v| ≤
      (measurableTotalVariation T (explicitStoppedWordLaw .beta endpointA)).toReal +
      (measurableTotalVariation T (explicitStoppedWordLaw .beta endpointB)).toReal -
        2*(239/6750) := by
  haveI := endpoint_probability .beta endpointA
  haveI := endpoint_probability .beta endpointB
  have h := finite_event_clipping_budget (explicitStoppedWordLaw .beta endpointB)
    (explicitStoppedWordLaw .beta endpointA) T RegularTable.betaEventᶜ {some [1]}
    (by trivial) (by trivial)
    (by simp [Set.disjoint_singleton_right,RegularTable.betaEvent])
    (3/5) (2/3) (2*(239/6750)) (by norm_num)
    (by have h := source_stop_beta endpointB; norm_num [endpointB] at h ⊢; exact h)
    (by have h := source_stop_beta endpointA; norm_num [endpointA] at h ⊢; exact h) ?_
  · rw [hv] at h
    have hc : |1-v-max (3/5) (min (2/3) (1-v))| = |v-clampEmission v| := by
      unfold clampEmission
      by_cases hlo : v ≤ 1/3
      · rw [show min (2/5:ℝ) v = v from min_eq_right (by linarith),
          show max (1/3:ℝ) v = 1/3 from max_eq_left hlo,
          show min (2/3:ℝ) (1-v) = 2/3 from min_eq_left (by linarith),
          show max (3/5:ℝ) (2/3) = 2/3 from max_eq_right (by norm_num)]
        rw [abs_of_nonneg (by linarith),abs_of_nonpos (by linarith)]
        ring
      · by_cases hhi : v ≤ 2/5
        · rw [show min (2/5:ℝ) v = v from min_eq_right hhi,
            show max (1/3:ℝ) v = v from max_eq_right (by linarith),
            show min (2/3:ℝ) (1-v) = 1-v from min_eq_right (by linarith),
            show max (3/5:ℝ) (1-v) = 1-v from max_eq_right (by linarith)]
          simp
        · rw [show min (2/5:ℝ) v = 2/5 from min_eq_left (by linarith),
            show max (1/3:ℝ) (2/5) = 2/5 from max_eq_right (by norm_num),
            show min (2/3:ℝ) (1-v) = 1-v from min_eq_right (by linarith),
            show max (3/5:ℝ) (1-v) = 3/5 from max_eq_left (by linarith)]
          rw [abs_of_nonpos (by linarith),abs_of_nonneg (by linarith)]
          ring
    rw [hc] at h
    linarith
  · rw [measureReal_compl (show MeasurableSet RegularTable.betaEvent from trivial),
      measureReal_compl (show MeasurableSet RegularTable.betaEvent from trivial),
      endpoint_beta_event,endpoint_beta_event]
    rw [probReal_univ,probReal_univ]
    norm_num [endpointA,endpointB]

universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

theorem clamp_read_zero (M : Observer Z) (e : InstalledEmitter M) (z : Z)
    (s : ActivePhase) (hz : (M.project z).control = .fourth (.active s)) :
    ((clampedEmitter M e).emit z (some (.read 0))).toReal =
      clampEmission (e.emit z (some (.read 0))).toReal := by
  simp only [clampedEmitter,hz,PMF.map_apply,tsum_fintype,Fin.sum_univ_two,
    PMF.pure_apply,readPMF,PMF.ofFintype_apply]
  simp only [Option.some.injEq,Operation.read.injEq,Fin.reduceEq,ite_true,ite_false,
    mul_one,mul_zero,add_zero]
  rw [ENNReal.toReal_ofReal (by
    have h := (clamp_box (e.emit z (some (.read 0))).toReal).1
    linarith)]

private theorem stop_p (M : Observer Z) (e : InstalledEmitter M) (z : Z)
    (hz : (M.project z).control = .fourth (.active .p)) :
    (rawTailLaw M e .p z).real {some [0]} = (e.emit z (some (.read 0))).toReal := by
  have h := (native_stopped_tail_regeneration M e).1 z hz {some [0]}
  have he : (Option.map (List.cons (1 : Letter))) ⁻¹' {some [0]} = (∅ : Set RawTail) := by
    ext t
    cases t <;> simp
  simpa [he] using h

private theorem stop_beta (M : Observer Z) (e : InstalledEmitter M) (z : Z)
    (hz : (M.project z).control = .fourth (.active .beta)) :
    (rawTailLaw M e .beta z).real {some [1]} = 1-(e.emit z (some (.read 0))).toReal := by
  have h := (native_stopped_tail_regeneration M e).2 z hz {some [1]}
  have he : (Option.map (List.cons (0 : Letter))) ⁻¹' {some [1]} = (∅ : Set RawTail) := by
    ext t
    cases t <;> simp
  simpa [he] using h

/-- The bound is on each original configuration, before either stationary average or TV. -/
theorem native_configuration_clipping_budget (M : Observer Z) (e : InstalledEmitter M) :
    (∀ z : Z, (M.project z).control = .fourth (.active .p) →
      |(e.emit z (some (.read 0))).toReal-
        ((clampedEmitter M e).emit z (some (.read 0))).toReal| ≤
      (measurableTotalVariation (rawTailLaw M e .p z) (explicitStoppedWordLaw .p endpointA)).toReal +
      (measurableTotalVariation (rawTailLaw M e .p z) (explicitStoppedWordLaw .p endpointB)).toReal -
        2*(1116529/22781250)) ∧
    (∀ z : Z, (M.project z).control = .fourth (.active .beta) →
      |(e.emit z (some (.read 0))).toReal-
        ((clampedEmitter M e).emit z (some (.read 0))).toReal| ≤
      (measurableTotalVariation (rawTailLaw M e .beta z)
        (explicitStoppedWordLaw .beta endpointA)).toReal +
      (measurableTotalVariation (rawTailLaw M e .beta z)
        (explicitStoppedWordLaw .beta endpointB)).toReal - 2*(239/6750)) := by
  constructor
  · intro z hz
    rw [clamp_read_zero M e z .p hz]
    simpa only [stop_p M e z hz] using p_budget (rawTailLaw M e .p z)
  · intro z hz
    rw [clamp_read_zero M e z .beta hz]
    exact beta_budget (rawTailLaw M e .beta z) _ (stop_beta M e z hz)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping
