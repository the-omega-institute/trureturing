/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete countable sign-event total variation and normalized two-endpoint CommonFlow stability. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSignedAction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelEndpointIdentification NativeFullResidual
open NativeConditionalControl.Tail FourthSegmentStoppedLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open NativeBorelSignedAction
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNormalizedStability


lemma countable_event_mono {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (μ ν : Measure X) (E : Set X) (hE : MeasurableSet E)
    (h : ∀ x ∈ E, μ {x} ≤ ν {x}) : μ E ≤ ν E := by
  classical
  rw [← Measure.tsum_indicator_apply_singleton μ E hE,
    ← Measure.tsum_indicator_apply_singleton ν E hE]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ E
  · simpa [Set.indicator_of_mem hx] using h x hx
  · simp [Set.indicator_of_notMem hx]

lemma complete_sign_event {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set X) (hS : MeasurableSet S)
    (hpos : ∀ x ∈ S, ν {x} ≤ μ {x})
    (hneg : ∀ x ∉ S, μ {x} ≤ ν {x}) :
    measurableTotalVariation μ ν = ENNReal.ofReal (μ.real S - ν.real S) := by
  have event_bound (E : Set X) (hE : MeasurableSet E) :
      μ.real E - ν.real E ≤ μ.real S - ν.real S := by
    have hp := countable_event_mono ν μ (S \ E) (hS.diff hE) (fun x hx => hpos x hx.1)
    have hn := countable_event_mono μ ν (E \ S) (hE.diff hS) (fun x hx => hneg x hx.2)
    have hp' := ENNReal.toReal_mono (measure_ne_top μ _) hp
    have hn' := ENNReal.toReal_mono (measure_ne_top ν _) hn
    have pE := measureReal_inter_add_sdiff (μ := μ) (s := E) hS
    have qE := measureReal_inter_add_sdiff (μ := ν) (s := E) hS
    have pS := measureReal_inter_add_sdiff (μ := μ) (s := S) hE
    have qS := measureReal_inter_add_sdiff (μ := ν) (s := S) hE
    rw [Set.inter_comm S E] at pS qS
    change ν.real (S \ E) ≤ μ.real (S \ E) at hp'
    change μ.real (E \ S) ≤ ν.real (E \ S) at hn'
    linarith
  apply le_antisymm
  · unfold measurableTotalVariation
    refine iSup_le (fun E => max_le ?_ ?_)
    · rw [← ENNReal.ofReal_toReal (measure_ne_top μ E.val),
        ← ENNReal.ofReal_toReal (measure_ne_top ν E.val),
        ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (event_bound E.val E.property)
    · have hb := event_bound E.valᶜ E.property.compl
      rw [measureReal_compl E.property, measureReal_compl E.property,
        probReal_univ, probReal_univ] at hb
      rw [← ENNReal.ofReal_toReal (measure_ne_top ν E.val),
        ← ENNReal.ofReal_toReal (measure_ne_top μ E.val),
        ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      apply ENNReal.ofReal_le_ofReal
      change ν.real E.val - μ.real E.val ≤ _
      linarith
  · unfold measurableTotalVariation
    apply le_iSup_of_le (⟨S,hS⟩ : {E : Set X // MeasurableSet E})
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ S),
      ← ENNReal.ofReal_toReal (measure_ne_top ν S),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    exact le_max_left _ _

lemma boxed_complete_sign_event {s : ActivePhase} (D : RegularDescriptor s)
    (hD : EndpointBox D) (S : Set (ValidTail s))
    (ha : ∀ t ∈ S, (native s upperRate : Measure _) {t} ≤ (native s lowerRate : Measure _) {t})
    (hb : ∀ t ∉ S, (native s lowerRate : Measure _) {t} ≤ (native s upperRate : Measure _) {t}) :
    measurableTotalVariation (law D) (native s lowerRate : Measure _) =
      ENNReal.ofReal ((native s lowerRate : Measure _).real S - (law D).real S) ∧
    measurableTotalVariation (law D) (native s upperRate : Measure _) =
      ENNReal.ofReal ((law D).real S - (native s upperRate : Measure _).real S) := by
  have box (t : ValidTail s) :
      min ((native s lowerRate : Measure _) {t}) ((native s upperRate : Measure _) {t}) ≤ law D {t} ∧
      law D {t} ≤ max ((native s lowerRate : Measure _) {t}) ((native s upperRate : Measure _) {t}) := by
    simpa only [native_coordinate] using hD t
  constructor
  · rw [measurable_total_variation_comm]
    apply complete_sign_event _ _ S (Set.to_countable _).measurableSet
    · intro t ht
      simpa [max_eq_left (ha t ht)] using (box t).2
    · intro t ht
      simpa [min_eq_left (hb t ht)] using (box t).1
  · apply complete_sign_event _ _ S (Set.to_countable _).measurableSet
    · intro t ht
      simpa [min_eq_right (ha t ht)] using (box t).1
    · intro t ht
      simpa [max_eq_right (hb t ht)] using (box t).2


def Ep : Set (ValidTail .p) := {t | t = pAtom 0 1 ∨ t = pAtom 1 1 ∨ t = pAtom 2 1}
def Eb : Set (ValidTail .beta) := {t | t = betaStop ∨ t = betaAtom 0 1}

lemma native_p_real (b : Bool) (n : ℕ) (i : Letter) :
    (native .p (endpoint b) : Measure (ValidTail .p)).real {pAtom n i} =
      (if i = 0 then (if b then 2/5 else 1/3 : ℝ) else (if b then 9/25 else 4/9 : ℝ)) *
      (if b then 6/25 else 2/9 : ℝ)^n := by
  change ((native .p (endpoint b) : Measure (ValidTail .p)) {pAtom n i}).toReal = _
  rw [(native_atoms _).1]
  cases b <;> by_cases hi : i = 0 <;>
    simp [hi, endpoint, alphaMass, betaMass, lowerRate, upperRate,
      unitInterval.symm, unitInterval.coe_toNNReal, ENNReal.toReal_mul, ENNReal.toReal_pow] <;> norm_num

lemma native_b_real (b : Bool) (n : ℕ) (i : Letter) :
    (native .beta (endpoint b) : Measure (ValidTail .beta)).real {betaAtom n i} =
      (if b then 2/5 else 1/3 : ℝ) *
      ((if i = 0 then (if b then 2/5 else 1/3 : ℝ) else (if b then 9/25 else 4/9 : ℝ)) *
      (if b then 6/25 else 2/9 : ℝ)^n) := by
  change ((native .beta (endpoint b) : Measure (ValidTail .beta)) {betaAtom n i}).toReal = _
  rw [(native_atoms _).2.2.1]
  cases b <;> by_cases hi : i = 0 <;>
    simp [hi, endpoint, alphaMass, betaMass, lowerRate, upperRate,
      unitInterval.symm, unitInterval.coe_toNNReal, ENNReal.toReal_mul, ENNReal.toReal_pow] <;> norm_num <;> ring

lemma power_mass_order (a b x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hab : a ≤ b) (hxy : x ≤ y) (n : ℕ) : a*x^n ≤ b*y^n := by
  exact mul_le_mul hab (pow_le_pow_left₀ hx hxy n) (pow_nonneg hx n) (ha.trans hab)

lemma p_marker_one_order (n : ℕ) :
    (if n ≤ 2 then (9/25 : ℝ)*(6/25 : ℝ)^n ≤ (4/9 : ℝ)*(2/9 : ℝ)^n
    else (4/9 : ℝ)*(2/9 : ℝ)^n ≤ (9/25 : ℝ)*(6/25 : ℝ)^n) := by
  split_ifs with hn
  · interval_cases n <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3+k := ⟨n-3, by omega⟩
    simp only [pow_add]
    calc
      _ = ((4/9 : ℝ)*(2/9 : ℝ)^3)*(2/9 : ℝ)^k := by ring
      _ ≤ ((9/25 : ℝ)*(6/25 : ℝ)^3)*(6/25 : ℝ)^k :=
        power_mass_order _ _ _ _ (by positivity) (by norm_num) (by norm_num) (by norm_num) k
      _ = _ := by ring

lemma b_marker_one_order (n : ℕ) :
    (if n = 0 then (2/5 : ℝ)*((9/25 : ℝ)*(6/25 : ℝ)^n) ≤ (1/3 : ℝ)*((4/9 : ℝ)*(2/9 : ℝ)^n)
    else (1/3 : ℝ)*((4/9 : ℝ)*(2/9 : ℝ)^n) ≤ (2/5 : ℝ)*((9/25 : ℝ)*(6/25 : ℝ)^n)) := by
  split_ifs with hn
  · subst n; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = 1+k := ⟨n-1, by omega⟩
    simp only [pow_add]
    calc
      _ = ((1/3 : ℝ)*(4/9 : ℝ)*(2/9 : ℝ))*(2/9 : ℝ)^k := by ring
      _ ≤ ((2/5 : ℝ)*(9/25 : ℝ)*(6/25 : ℝ))*(6/25 : ℝ)^k :=
        power_mass_order _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) k
      _ = _ := by ring

lemma p_signs :
    (∀ t ∈ Ep, (native .p upperRate : Measure (ValidTail .p)) {t} ≤ (native .p lowerRate : Measure (ValidTail .p)) {t}) ∧
    (∀ t ∉ Ep, (native .p lowerRate : Measure (ValidTail .p)) {t} ≤ (native .p upperRate : Measure (ValidTail .p)) {t}) := by
  have marker0 (n : ℕ) : (native .p lowerRate : Measure (ValidTail .p)) {pAtom n 0} ≤
      (native .p upperRate : Measure (ValidTail .p)) {pAtom n 0} := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (native .p (endpoint false) : Measure (ValidTail .p)).real _ ≤ (native .p (endpoint true) : Measure (ValidTail .p)).real _
    rw [native_p_real, native_p_real]
    simp only [Fin.reduceEq, Bool.false_eq_true, if_true, if_false]
    exact power_mass_order _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) n
  have marker1 (n : ℕ) := p_marker_one_order n
  constructor
  · intro t ht
    rcases ht with rfl | rfl | rfl <;>
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp <;>
      change (native .p (endpoint true) : Measure (ValidTail .p)).real _ ≤ (native .p (endpoint false) : Measure (ValidTail .p)).real _ <;>
      rw [native_p_real, native_p_real] <;> norm_num
  · rintro ⟨t,ht⟩ hnot
    cases t with
    | none =>
        change (native .p lowerRate : Measure _) {infinity .p} ≤ (native .p upperRate : Measure _) {infinity .p}
        rw [(native_atoms lowerRate).2.2.2 .p, (native_atoms upperRate).2.2.2 .p]
    | some w =>
      obtain ⟨i,n,rfl⟩ := ht
      fin_cases i
      · exact marker0 n
      · have hn : ¬ n ≤ 2 := by
          intro hn; interval_cases n <;> exact hnot (by simp [Ep, pAtom])
        have h := marker1 n
        simp only [hn, if_false] at h
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
        change (native .p (endpoint false) : Measure (ValidTail .p)).real _ ≤ (native .p (endpoint true) : Measure (ValidTail .p)).real _
        change (native .p (endpoint false) : Measure (ValidTail .p)).real {pAtom n 1} ≤
          (native .p (endpoint true) : Measure (ValidTail .p)).real {pAtom n 1}
        simpa only [native_p_real, Fin.reduceEq, Bool.false_eq_true, if_false, if_true] using h

lemma b_signs :
    (∀ t ∈ Eb, (native .beta upperRate : Measure (ValidTail .beta)) {t} ≤ (native .beta lowerRate : Measure (ValidTail .beta)) {t}) ∧
    (∀ t ∉ Eb, (native .beta lowerRate : Measure (ValidTail .beta)) {t} ≤ (native .beta upperRate : Measure (ValidTail .beta)) {t}) := by
  have marker0 (n : ℕ) : (native .beta lowerRate : Measure (ValidTail .beta)) {betaAtom n 0} ≤
      (native .beta upperRate : Measure (ValidTail .beta)) {betaAtom n 0} := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (native .beta (endpoint false) : Measure (ValidTail .beta)).real _ ≤ (native .beta (endpoint true) : Measure (ValidTail .beta)).real _
    rw [native_b_real, native_b_real]
    simp only [Fin.reduceEq, Bool.false_eq_true, if_true, if_false]
    calc
      _ = (1/9 : ℝ)*(2/9 : ℝ)^n := by ring
      _ ≤ (4/25 : ℝ)*(6/25 : ℝ)^n :=
        power_mass_order _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) n
      _ = _ := by ring
  constructor
  · intro t ht
    rcases ht with rfl | rfl
    · rw [(native_atoms _).2.1, (native_atoms _).2.1]
      apply (ENNReal.toReal_le_toReal (by simp [betaMass]) (by simp [betaMass])).mp
      norm_num [betaMass, lowerRate, upperRate, unitInterval.symm, unitInterval.coe_toNNReal]
    · apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change (native .beta (endpoint true) : Measure (ValidTail .beta)).real _ ≤ (native .beta (endpoint false) : Measure (ValidTail .beta)).real _
      rw [native_b_real, native_b_real]; norm_num
  · rintro ⟨t,ht⟩ hnot
    cases t with
    | none =>
        change (native .beta lowerRate : Measure _) {infinity .beta} ≤ (native .beta upperRate : Measure _) {infinity .beta}
        rw [(native_atoms lowerRate).2.2.2 .beta, (native_atoms upperRate).2.2.2 .beta]
    | some w =>
      obtain ⟨i,hi⟩ := ht
      rcases hi with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
      · exact False.elim (hnot (by simp [Eb, betaStop]))
      · fin_cases i
        · exact marker0 n
        · have hn : n ≠ 0 := by intro he; subst n; exact hnot (by simp [Eb, betaAtom])
          have h := b_marker_one_order n
          simp only [hn, if_false] at h
          apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
          change (native .beta (endpoint false) : Measure (ValidTail .beta)).real _ ≤ (native .beta (endpoint true) : Measure (ValidTail .beta)).real _
          change (native .beta (endpoint false) : Measure (ValidTail .beta)).real {betaAtom n 1} ≤
            (native .beta (endpoint true) : Measure (ValidTail .beta)).real {betaAtom n 1}
          simpa only [native_b_real, Fin.reduceEq, Bool.false_eq_true, if_false, if_true] using h

lemma complete_p_TV (Q : PDescriptor) (hQ : EndpointBox Q) :
    measurableTotalVariation (law Q) (native .p lowerRate : Measure (ValidTail .p)) =
      ENNReal.ofReal ((native .p lowerRate : Measure (ValidTail .p)).real Ep - (law Q).real Ep) ∧
    measurableTotalVariation (law Q) (native .p upperRate : Measure (ValidTail .p)) =
      ENNReal.ofReal ((law Q).real Ep - (native .p upperRate : Measure (ValidTail .p)).real Ep) :=
  boxed_complete_sign_event Q hQ Ep p_signs.1 p_signs.2

lemma complete_b_TV (W : BDescriptor) (hW : EndpointBox W) :
    measurableTotalVariation (law W) (native .beta lowerRate : Measure (ValidTail .beta)) =
      ENNReal.ofReal ((native .beta lowerRate : Measure (ValidTail .beta)).real Eb - (law W).real Eb) ∧
    measurableTotalVariation (law W) (native .beta upperRate : Measure (ValidTail .beta)) =
      ENNReal.ofReal ((law W).real Eb - (native .beta upperRate : Measure (ValidTail .beta)).real Eb) :=
  boxed_complete_sign_event W hW Eb b_signs.1 b_signs.2




def fullLoss (s : ActivePhase) (b : Bool) (D : RegularDescriptor s) : ℝ :=
  (measurableTotalVariation (law D) (native s (endpoint b) : Measure (ValidTail s))).toReal

lemma p_event_real (μ : Measure (ValidTail .p)) [IsFiniteMeasure μ] :
    μ.real Ep = μ.real {pAtom 0 1} + μ.real {pAtom 1 1} + μ.real {pAtom 2 1} := by
  classical
  have he : Ep = (({pAtom 0 1, pAtom 1 1, pAtom 2 1} : Finset (ValidTail .p)) : Set (ValidTail .p)) := by
    ext t; simp [Ep]
  rw [he, ← sum_measureReal_singleton]
  rw [Finset.sum_insert (by simp [pAtom,Subtype.mk.injEq,pWord,loopWord]),
    Finset.sum_insert (by simp [pAtom,Subtype.mk.injEq,pWord,loopWord]),Finset.sum_singleton]
  ring

lemma b_event_real (μ : Measure (ValidTail .beta)) [IsFiniteMeasure μ] :
    μ.real Eb = μ.real {betaStop} + μ.real {betaAtom 0 1} := by
  classical
  have he : Eb = (({betaStop, betaAtom 0 1} : Finset (ValidTail .beta)) : Set (ValidTail .beta)) := by
    ext t; simp [Eb]
  rw [he, ← sum_measureReal_singleton]
  have hne : betaStop ≠ betaAtom 0 1 := by
    intro h
    have he := congrArg (fun t : ValidTail .beta => t.val) h
    simp [betaStop,betaAtom,pWord,loopWord] at he
  rw [Finset.sum_insert (by simpa using hne),Finset.sum_singleton]

lemma p_loss_formula (Q : PDescriptor) (hQ : EndpointBox Q) (b : Bool) :
    fullLoss .p b Q = defect b Q - late b 1 Q - late b 2 Q := by
  have hb := complete_p_TV Q hQ
  have box (t : ValidTail .p) :
      min ((native .p lowerRate : Measure _) {t}) ((native .p upperRate : Measure _) {t}) ≤ law Q {t} ∧
      law Q {t} ≤ max ((native .p lowerRate : Measure _) {t}) ((native .p upperRate : Measure _) {t}) := by
    simpa only [native_coordinate] using hQ t
  have hlo : (law Q).real Ep ≤ (native .p lowerRate : Measure (ValidTail .p)).real Ep := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply countable_event_mono _ _ Ep (Set.to_countable _).measurableSet
    intro t ht
    simpa [max_eq_left (p_signs.1 t ht)] using (box t).2
  have hhi : (native .p upperRate : Measure (ValidTail .p)).real Ep ≤ (law Q).real Ep := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply countable_event_mono _ _ Ep (Set.to_countable _).measurableSet
    intro t ht
    simpa [min_eq_right (p_signs.1 t ht)] using (box t).1
  cases b
  · unfold fullLoss
    change (measurableTotalVariation (law Q) (native .p lowerRate : Measure _)).toReal = _
    rw [hb.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hlo), p_event_real, p_event_real]
    change (native .p (endpoint false) : Measure (ValidTail .p)).real {pAtom 0 1} +
      (native .p (endpoint false) : Measure (ValidTail .p)).real {pAtom 1 1} +
      (native .p (endpoint false) : Measure (ValidTail .p)).real {pAtom 2 1} - _ = _
    simp only [native_p_real, Fin.reduceEq, Bool.false_eq_true, if_false, if_true]
    unfold defect late g coordinate
    norm_num [signR,cR,zR,Measure.real]
    ring
  · unfold fullLoss
    change (measurableTotalVariation (law Q) (native .p upperRate : Measure _)).toReal = _
    rw [hb.2, ENNReal.toReal_ofReal (sub_nonneg.mpr hhi), p_event_real, p_event_real]
    change _ - ((native .p (endpoint true) : Measure (ValidTail .p)).real {pAtom 0 1} +
      (native .p (endpoint true) : Measure (ValidTail .p)).real {pAtom 1 1} +
      (native .p (endpoint true) : Measure (ValidTail .p)).real {pAtom 2 1}) = _
    simp only [native_p_real, Fin.reduceEq, if_false, if_true]
    unfold defect late g coordinate
    norm_num [signR,cR,zR,Measure.real]
    ring

lemma pointwise_p_loss_bound (F : CommonFlow) (b : Bool) :
    (fun Q => fullLoss .p b Q) ≤ᵐ[F.nuP]
      (fun Q => (1+zR b+zR b^2)*defect b Q +
        (1+zR b)*action F (defect b) Q + realIterate F (defect b) 2 Q) := by
  have hV := variation_control F b
  have hLV := ae_action_mono F ((bounded_variation F b).mul_const (-cR b))
    ((bounded_defect b).mul_const (zR b)) hV
  have hm1 : (fun Q => cR b * action F (variation F b) Q) =
      (fun Q => -(action F (fun Q => -cR b*variation F b Q) Q)) := by
    funext Q; rw [action_mul]; ring
  filter_upwards [F.boxP, first_defect_identity F b, second_defect_identity F b, hV,hLV]
    with Q hbox h1 h2 hv hlv
  rw [p_loss_formula Q hbox b]
  rw [action_mul,action_mul] at hlv
  have hz : 0 ≤ zR b := by cases b <;> norm_num [zR]
  have hvz := mul_le_mul_of_nonneg_left hv hz
  linarith


lemma b_loss_event (W : BDescriptor) (hW : EndpointBox W) (b : Bool) :
    fullLoss .beta b W = signR b * ((native .beta (endpoint b) : Measure (ValidTail .beta)).real Eb - (law W).real Eb) := by
  have hb := complete_b_TV W hW
  have box (t : ValidTail .beta) :
      min ((native .beta lowerRate : Measure _) {t}) ((native .beta upperRate : Measure _) {t}) ≤ law W {t} ∧
      law W {t} ≤ max ((native .beta lowerRate : Measure _) {t}) ((native .beta upperRate : Measure _) {t}) := by
    simpa only [native_coordinate] using hW t
  have hlo : (law W).real Eb ≤ (native .beta lowerRate : Measure (ValidTail .beta)).real Eb := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply countable_event_mono _ _ Eb (Set.to_countable _).measurableSet
    intro t ht
    simpa [max_eq_left (b_signs.1 t ht)] using (box t).2
  have hhi : (native .beta upperRate : Measure (ValidTail .beta)).real Eb ≤ (law W).real Eb := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply countable_event_mono _ _ Eb (Set.to_countable _).measurableSet
    intro t ht
    simpa [min_eq_right (b_signs.1 t ht)] using (box t).1
  cases b
  · unfold fullLoss
    change (measurableTotalVariation (law W) (native .beta lowerRate : Measure _)).toReal = _
    rw [hb.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hlo)]
    simp [signR,endpoint]
  · unfold fullLoss
    change (measurableTotalVariation (law W) (native .beta upperRate : Measure _)).toReal = _
    rw [hb.2,ENNReal.toReal_ofReal (sub_nonneg.mpr hhi)]
    simp [signR,endpoint]

lemma b_stop_real (W : BDescriptor) : (law W).real {betaStop} = 1-(v W).toReal := by
  have hv : 1-v W = law W {betaStop} := ENNReal.sub_sub_cancel (by simp) prob_le_one
  rw [← one_sub_v_real, Measure.real, hv]

lemma real_A_zero (F : CommonFlow) : ∀ᵐ W ∂F.nuB,
    (law W).real {betaAtom 0 1} = (v W).toReal * (∫ Q, (g Q).toReal ∂F.A W) := by
  filter_upwards [original_A_zero F] with W hW
  change (law W {betaAtom 0 1}).toReal = _
  change (law W {betaAtom 0 1}).toReal = _
  rw [hW,ENNReal.toReal_mul]
  change (v W).toReal*(∫⁻ Q, g Q ∂F.A W).toReal = _
  rw [← integral_toReal measurable_g.aemeasurable
    (Eventually.of_forall (fun Q => (measure_ne_top (law Q) _).lt_top))]

lemma native_b_event (b : Bool) :
    (native .beta (endpoint b) : Measure (ValidTail .beta)).real Eb = 1-rR b+rR b*cR b := by
  rw [b_event_real, native_b_real]
  change ((native .beta (endpoint b) : Measure _) {betaStop}).toReal + _ = _
  rw [(native_atoms _).2.1]
  cases b <;> norm_num [endpoint, betaMass, lowerRate, upperRate, unitInterval.symm,
    unitInterval.coe_toNNReal, cR, rR]

lemma suspended_loss_formula (F : CommonFlow) (b : Bool) :
    (fun W => fullLoss .beta b W) =ᵐ[F.nuB]
      (fun W => (1-cR b)*emissionDefectB b W +
        (v W).toReal * (∫ Q, defect b Q ∂F.A W)) := by
  filter_upwards [F.boxB, real_A_zero F] with W hbox hA
  rw [b_loss_event W hbox b,native_b_event,b_event_real,b_stop_real,hA]
  unfold defect emissionDefectB g
  rw [integral_const_mul, integral_sub (integrable_const (cR b)) ((bounded_coordinate 0 1).integrable _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma bounded_product {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Bounded f) (hg : Bounded g) : Bounded (fun x => f x*g x) := by
  obtain ⟨mf,M,hM,bf⟩ := hf
  obtain ⟨mg,N,hN,bg⟩ := hg
  refine ⟨mf.mul mg,M*N,mul_nonneg hM hN,?_⟩
  intro x
  rw [norm_mul]
  exact mul_le_mul (bf x) (bg x) (norm_nonneg _) hM

lemma p_loss_integrable (F : CommonFlow) (b : Bool) : Integrable (fullLoss .p b) F.nuP := by
  have hbound := ((bounded_defect b).sub (bounded_late b 1)).sub (bounded_late b 2)
  apply (hbound.integrable F.nuP).congr
  filter_upwards [F.boxP] with Q hQ
  exact (p_loss_formula Q hQ b).symm

def MR (b : Bool) : ℝ := 1+zR b+zR b^2+(1+zR b)*(4/15)+(4/15)^2

lemma integrated_p_loss (F : CommonFlow) (b : Bool) :
    (∫ Q, fullLoss .p b Q ∂F.nuP) ≤ MR b * (∫ Q, defect b Q ∂F.nuP) := by
  have h0 := ((bounded_defect b).mul_const (1+zR b+zR b^2)).integrable F.nuP
  have h1 := (((bounded_defect b).action F).mul_const (1+zR b)).integrable F.nuP
  have h2 := ((bounded_defect b).realIterate F 2).integrable F.nuP
  have hint := integral_mono_ae (p_loss_integrable F b) ((h0.add h1).add h2) (pointwise_p_loss_bound F b)
  have hadd1 := integral_add h0 h1
  have hadd2 := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at hadd1 hadd2 hint
  rw [hadd2,hadd1, integral_const_mul,integral_const_mul] at hint
  have hA := (integrated_action_bounds F (bounded_defect b) (defect_nonneg F b)).2
  have hA2 := (integrated_iterate_bounds F (bounded_defect b) (defect_nonneg F b) 2).2
  have hz : 0 ≤ 1+zR b := by cases b <;> norm_num [zR]
  have hA' := mul_le_mul_of_nonneg_left hA hz
  calc
    _ ≤ _ := hint
    _ ≤ (1+zR b+zR b^2)*(∫ Q, defect b Q ∂F.nuP) +
        (1+zR b)*((4/15 : ℝ)*(∫ Q, defect b Q ∂F.nuP)) +
        (4/15 : ℝ)^2*(∫ Q, defect b Q ∂F.nuP) :=
      add_le_add (add_le_add le_rfl hA') hA2
    _ = _ := by unfold MR; ring

lemma integrated_b_loss (F : CommonFlow) (b : Bool) :
    (∫ W, fullLoss .beta b W ∂F.nuB) ≤ MR b * (∫ Q, defect b Q ∂F.nuP) := by
  have hAf := Measure.ae_ae_of_ae_comp (κ := F.A) ((margin_A F).symm ▸ defect_nonneg F b)
  have hApos : ∀ᵐ W ∂F.nuB, 0 ≤ ∫ Q, defect b Q ∂F.A W := by
    filter_upwards [hAf] with W hW
    exact integral_nonneg_of_ae hW
  have hp : (fun W => (v W).toReal*(∫ Q, defect b Q ∂F.A W)) ≤ᵐ[F.nuB]
      (fun W => (2/5 : ℝ)*(∫ Q, defect b Q ∂F.A W)) := by
    filter_upwards [hApos] with W hW
    exact mul_le_mul_of_nonneg_right (v_real_bounds W).2 hW
  have hY : (1-rR b)*(∫ W, emissionDefectB b W ∂F.nuB) ≤ ∫ Q, defect b Q ∂F.nuP := by
    have hy := ((bounded_emissionB b).kernel F.B).mul_const (1-rR b)
    have hi := integral_mono_ae (hy.integrable F.nuP) ((bounded_defect b).integrable F.nuP)
      ((defect_controls F b).mono (fun _ h => h.2))
    rw [integral_const_mul,kernel_transport F.B F.nuP F.nuB (margin_B F) (bounded_emissionB b)] at hi
    exact hi
  have hprod := bounded_product bounded_v ((bounded_defect b).kernel F.A)
  have hm := integral_mono_ae (hprod.integrable F.nuB)
    ((((bounded_defect b).kernel F.A).mul_const (2/5)).integrable F.nuB) hp
  rw [integral_const_mul,kernel_transport F.A F.nuB F.nuP (margin_A F) (bounded_defect b)] at hm
  have hloss := integral_congr_ae (suspended_loss_formula F b)
  rw [integral_add (((bounded_emissionB b).mul_const (1-cR b)).integrable F.nuB)
      (hprod.integrable F.nuB), integral_const_mul] at hloss
  have hr : 0 < 1-rR b := by cases b <;> norm_num [rR]
  have hc : 0 ≤ 1-cR b := by cases b <;> norm_num [cR]
  have hy := mul_le_mul_of_nonneg_left hY (div_nonneg hc hr.le)
  have hyeq : ((1-cR b)/(1-rR b))*((1-rR b)*(∫ W, emissionDefectB b W ∂F.nuB)) =
      (1-cR b)*(∫ W, emissionDefectB b W ∂F.nuB) := by field_simp
  rw [hyeq] at hy
  have hphi : 0 ≤ ∫ Q, defect b Q ∂F.nuP := integral_nonneg_of_ae (defect_nonneg F b)
  have hcoef : (1-cR b)/(1-rR b)+(2/5 : ℝ) ≤ MR b := by
    cases b <;> norm_num [cR,rR,MR,zR]
  have hcphi := mul_le_mul_of_nonneg_right hcoef hphi
  calc
    _ = _ := hloss
    _ ≤ ((1-cR b)/(1-rR b))*(∫ Q, defect b Q ∂F.nuP) +
        (2/5 : ℝ)*(∫ Q, defect b Q ∂F.nuP) := add_le_add hy hm
    _ = ((1-cR b)/(1-rR b)+(2/5 : ℝ))*(∫ Q, defect b Q ∂F.nuP) := by ring
    _ ≤ _ := hcphi


def meanCoordinate (F : CommonFlow) (n : ℕ) : ℝ := ∫ Q, (coordinate n 1 Q).toReal ∂F.nuP
def slack (F : CommonFlow) (b : Bool) (n : ℕ) : ℝ :=
  signR b*(meanCoordinate F n-cR b*zR b^n)
def completeLoss (F : CommonFlow) (b : Bool) : ℝ :=
  max (∫ Q, fullLoss .p b Q ∂F.nuP) (∫ W, fullLoss .beta b W ∂F.nuB)
def HR (b : Bool) : ℝ := if b then 20723912/5859375 else 9839648/2657205

lemma integral_late (F : CommonFlow) (b : Bool) (n : ℕ) :
    (∫ Q, late b n Q ∂F.nuP) = slack F b n := by
  unfold late slack meanCoordinate
  rw [integral_const_mul, integral_sub ((bounded_coordinate n 1).integrable _)
    (integrable_const (cR b*zR b^n))]
  simp

lemma complete_loss_bound (F : CommonFlow) (b : Bool) :
    completeLoss F b ≤ MR b*(∫ Q, defect b Q ∂F.nuP) :=
  max_le (integrated_p_loss F b) (integrated_b_loss F b)

lemma normalized_stability (F : CommonFlow) (b : Bool) (n : ℕ) (hn : 4 ≤ n) :
    completeLoss F b ≤ HR b*(slack F b n/(cR b*zR b^n)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  have hi := integrated_three_step F b k
  rw [integral_late] at hi
  have hden : 0 < cR b*zR b^(k+4) := by cases b <;> unfold cR zR <;> positivity
  have hm : 0 ≤ MR b*cR b*(125 : ℝ) := by cases b <;> norm_num [MR,cR,zR]
  have hconst : MR b*cR b*(125 : ℝ)*(zR b^3+(4/15 : ℝ)*zR b^2+(4/15 : ℝ)^2*zR b) = HR b := by
    cases b <;> norm_num [MR,cR,zR,HR]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  calc
    completeLoss F b*(cR b*zR b^(k+4)) ≤
        (MR b*(∫ Q, defect b Q ∂F.nuP))*(cR b*zR b^(k+4)) :=
      mul_le_mul_of_nonneg_right (complete_loss_bound F b) hden.le
    _ = (MR b*cR b*125)*((1/5 : ℝ)^3*zR b^(k+4)*(∫ Q, defect b Q ∂F.nuP)) := by ring
    _ ≤ (MR b*cR b*125)*((zR b^3+(4/15 : ℝ)*zR b^2+(4/15 : ℝ)^2*zR b)*slack F b (k+4)) :=
      mul_le_mul_of_nonneg_left hi hm
    _ = HR b*slack F b (k+4) := by rw [← mul_assoc,hconst]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNormalizedStability
