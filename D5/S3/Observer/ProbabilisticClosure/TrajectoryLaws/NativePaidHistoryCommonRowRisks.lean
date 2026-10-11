/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One common native stationary pair satisfies all original configuration and complete-law risks. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowLimits
import D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Classical Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open NativeObserverJointLaw NativeInstalledFullLaw NativeFullResidual
open NativePaidHistoryCommonRow NativePaidHistoryCommonRowLimits
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance : DecidableEq Z := Classical.decEq Z

theorem probability_tv_le_one {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    measurableTotalVariation P Q ≤ 1 := by
  unfold measurableTotalVariation
  refine iSup_le fun E => max_le ?_ ?_
  · exact tsub_le_self.trans ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  · exact tsub_le_self.trans ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)

theorem probability_tv_finite {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    measurableTotalVariation P Q ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probability_tv_le_one P Q)

private theorem real_tv_triangle {A : Type*} [MeasurableSpace A]
    (P Q T : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure T] :
    (measurableTotalVariation P T).toReal ≤
      (measurableTotalVariation P Q).toReal+(measurableTotalVariation Q T).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨probability_tv_finite P Q, probability_tv_finite Q T⟩)
    (measurable_total_variation_triangle P Q T)
  simpa only [ENNReal.toReal_add (probability_tv_finite P Q)
    (probability_tv_finite Q T)] using h

theorem event_gap {A : Type*} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set A) (hE : MeasurableSet E) :
    |(P E).toReal-(Q E).toReal| ≤ (measurableTotalVariation P Q).toReal := by
  have hP : P E ≠ ∞ := measure_ne_top P E
  have hQ : Q E ≠ ∞ := measure_ne_top Q E
  have h := ENNReal.toReal_mono (probability_tv_finite P Q)
    (le_iSup (fun F : {F : Set A // MeasurableSet F} =>
      max (P F.val-Q F.val) (Q F.val-P F.val)) ⟨E,hE⟩)
  rw [ENNReal.toReal_max (ne_top_of_le_ne_top hP tsub_le_self)
    (ne_top_of_le_ne_top hQ tsub_le_self)] at h
  by_cases hpq : Q E ≤ P E
  · rw [ENNReal.toReal_sub_of_le hpq hP] at h
    have hr := (ENNReal.toReal_le_toReal hQ hP).mpr hpq
    rw [abs_of_nonneg (sub_nonneg.mpr hr)]
    exact (le_max_left _ _).trans h
  · have hpq' := le_of_not_ge hpq
    rw [ENNReal.toReal_sub_of_le hpq' hQ] at h
    have hr := (ENNReal.toReal_le_toReal hP hQ).mpr hpq'
    rw [abs_of_nonpos (sub_nonpos.mpr hr), neg_sub]
    exact (le_max_right _ _).trans h

theorem risk_finite (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) : installedRisk M e μ s ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  refine iSup_le fun H => ?_
  haveI := ((native_history_risk_transport M μ s (fun _ z => tailLaw M e s z)).1 H).2.1
  calc
    _ ≤ ∑ z, row M H.val.1 z * 1 := Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (probability_tv_le_one (fullLaw M e z) _) zero_le
    _ = 1 := by simpa only [mul_one, tsum_fintype] using (row M H.val.1).tsum_coe

private theorem law_risk_finite (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) : installedLawRisk M e μ s ≠ ∞ := by
  have h := (native_paid_window_control M e μ 0 0 0 s).2.2.2.2.2.2.2.2.2.1
  exact ne_top_of_le_ne_top (risk_finite M e μ s) h

/-- Configuration-before-TV remains affine in the real probability row. -/
def configurationCost (M : Observer Z) (e : InstalledEmitter M)
    (k : Depth) (s : ActivePhase) (v : Z → ℝ) : ℝ :=
  ∑ z, v z*(measurableTotalVariation (tailLaw M e s z) (pureTail k s)).toReal

/-- Each measurable complete-tail event retains both directed law-risk comparisons. -/
def eventMass (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase)
    (E : Set (ValidTail s)) (v : Z → ℝ) : ℝ :=
  ∑ z, v z*(tailLaw M e s z E).toReal

private theorem mixture_probability (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (η : PMF Z) : IsProbabilityMeasure (tailMixture M e s η) := by
  constructor
  simp only [tailMixture, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  simpa only [tsum_fintype] using η.tsum_coe

private theorem mixture_event_real (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (η : PMF Z) (E : Set (ValidTail s)) :
    (tailMixture M e s η E).toReal = eventMass M e s E (fun z => (η z).toReal) := by
  simp only [tailMixture, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    eventMass]
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top (η.apply_ne_top z)
    (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

private theorem history_pure_bounds (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (k : Depth) (s : ActivePhase) (H : PhaseHistory s) :
    let δ := (measurableTotalVariation (rawTarget μ H.val.1 H.val.2 s) (pureTail k s)).toReal
    configurationCost M e k s (fun z => (row M H.val.1 z).toReal) ≤
      (installedRisk M e μ s).toReal+δ ∧
    ∀ E : Set (ValidTail s), MeasurableSet E →
      |eventMass M e s E (fun z => (row M H.val.1 z).toReal)-(pureTail k s E).toReal| ≤
        (installedLawRisk M e μ s).toReal+δ := by
  dsimp only
  haveI := ((native_history_risk_transport M μ s (fun _ z => tailLaw M e s z)).1 H).1
  haveI := mixture_probability M e s (row M H.val.1)
  have hc : (∑ z, row M H.val.1 z * measurableTotalVariation (tailLaw M e s z)
      (rawTarget μ H.val.1 H.val.2 s)) ≤ installedRisk M e μ s := by
    rw [(installed_full_law M e).2.2.2.2.2 μ s]
    exact le_iSup (fun G : PhaseHistory s => ∑ z, row M G.val.1 z *
      measurableTotalVariation (tailLaw M e s z) (rawTarget μ G.val.1 G.val.2 s)) H
  have hl : measurableTotalVariation (tailMixture M e s (row M H.val.1))
      (rawTarget μ H.val.1 H.val.2 s) ≤ installedLawRisk M e μ s := by
    rw [← (native_paid_window_control M e μ 0 0 0 s).2.2.2.2.2.2.2.2.1]
    exact le_iSup (fun G : PhaseHistory s => measurableTotalVariation
      (tailMixture M e s (row M G.val.1)) (rawTarget μ G.val.1 G.val.2 s)) H
  have hcr := ENNReal.toReal_mono (risk_finite M e μ s) hc
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
    ((row M H.val.1).apply_ne_top z) (probability_tv_finite _ _))] at hcr
  simp only [ENNReal.toReal_mul] at hcr
  constructor
  · calc
      _ ≤ ∑ z, (row M H.val.1 z).toReal *
          ((measurableTotalVariation (tailLaw M e s z) (rawTarget μ H.val.1 H.val.2 s)).toReal+
            (measurableTotalVariation (rawTarget μ H.val.1 H.val.2 s) (pureTail k s)).toReal) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (real_tv_triangle _ _ _)
          ENNReal.toReal_nonneg
      _ = (∑ z, (row M H.val.1 z).toReal *
          (measurableTotalVariation (tailLaw M e s z) (rawTarget μ H.val.1 H.val.2 s)).toReal)+
            (measurableTotalVariation (rawTarget μ H.val.1 H.val.2 s) (pureTail k s)).toReal := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, (show ∑ z, (row M H.val.1 z).toReal = 1 from by
          simpa only [D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass] using
            D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass_sum (Output := fun _ : Nat => Z) (i := 0)
              (row M H.val.1)), one_mul]
      _ ≤ _ := add_le_add hcr (le_refl _)
  · intro E hE
    rw [← mixture_event_real]
    exact (event_gap _ _ E hE).trans ((real_tv_triangle _ _ _).trans
      (add_le_add (ENNReal.toReal_mono (law_risk_finite M e μ s) hl) (le_refl _)))


private def costLinear (c : Z → ℝ) : (Z → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ z, v z*c z
  map_add' x y := by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Pi.smul_apply, mul_assoc, ← Finset.mul_sum]

private theorem average_affine (w : ℕ) (hw : 0 < w) (f : ℕ → ℝ) (d : ℝ) :
    (w:ℝ)⁻¹*(∑ a ∈ Finset.range w, f a)+d =
      (w:ℝ)⁻¹*(∑ a ∈ Finset.range w, (f a+d)) := by
  have hw' : (w:ℝ) ≠ 0 := (Nat.cast_pos.mpr hw).ne'
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_add]
  rw [← mul_assoc, inv_mul_cancel₀ hw', one_mul]

private theorem average_bound (w : ℕ) (hw : 0 < w) (f : ℕ → ℝ) (b : ℝ)
    (h : ∀ a, a < w → f a ≤ b) : (w:ℝ)⁻¹*∑ a ∈ Finset.range w, f a ≤ b := by
  calc
    _ ≤ (w:ℝ)⁻¹*∑ _a ∈ Finset.range w, b := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a ha => h a (Finset.mem_range.mp ha))
      (inv_nonneg.mpr (Nat.cast_nonneg w))
    _ = b := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
      rw [inv_mul_cancel₀ (Nat.cast_pos.mpr hw).ne', one_mul]

private theorem actual_average_bound (M : Observer Z) (w : ℕ) (hw : 0 < w)
    (k : Depth) (j : ℕ) (s : ActivePhase) (c : Z → ℝ) (d b : ℝ)
    (h : ∀ u v, u < w → v < w →
      (∑ z, (row M (windowHistory (windowCount w (rate k) u)
        (windowCount w (1-(rate k:ℝ)) v) j s) z).toReal*c z)+d ≤ b) :
    (∑ z, returnedAverage M w k j s z*c z)+d ≤ b := by
  change costLinear c (returnedAverage M w k j s)+d ≤ b
  rw [returned_average_actual]
  simp only [map_smul, map_sum, smul_eq_mul]
  rw [average_affine w hw]
  apply average_bound w hw
  intro u hu
  rw [average_affine w hw]
  exact average_bound w hw _ b (fun v hv => h u v hu hv)

/-- The joint risk region uses each original supremum in its own order. -/
def riskRegion (M : Observer Z) (e : InstalledEmitter M) (μ : PMF Depth)
    (s : ActivePhase) : Set (Z → ℝ) := {v | ∀ k : Depth, μ k ≠ 0 →
      configurationCost M e k s v ≤ (installedRisk M e μ s).toReal ∧
      ∀ E : Set (ValidTail s), MeasurableSet E →
        |eventMass M e s E v-(pureTail k s E).toReal| ≤ (installedLawRisk M e μ s).toReal}

private theorem risk_region_closed (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) : IsClosed (riskRegion M e μ s) := by
  have he : riskRegion M e μ s = ⋂ k : Depth, ⋂ _hk : μ k ≠ 0,
      {v | configurationCost M e k s v ≤ (installedRisk M e μ s).toReal} ∩
      ⋂ E : Set (ValidTail s), ⋂ _hE : MeasurableSet E,
        {v | |eventMass M e s E v-(pureTail k s E).toReal| ≤ (installedLawRisk M e μ s).toReal} := by
    ext v; simp only [riskRegion, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [he]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro hk
  apply IsClosed.inter
  · exact isClosed_le (by unfold configurationCost; fun_prop) continuous_const
  · apply isClosed_iInter
    intro E
    apply isClosed_iInter
    intro hE
    exact isClosed_le (by unfold eventMass; fun_prop) continuous_const

private theorem risk_region_convex (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) : Convex ℝ (riskRegion M e μ s) := by
  intro x hx y hy a b ha hb hab
  intro k hk
  have hcost : configurationCost M e k s (a • x+b • y) =
      a*configurationCost M e k s x+b*configurationCost M e k s y := by
    simp only [configurationCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  constructor
  · rw [hcost]
    calc
      _ ≤ a*(installedRisk M e μ s).toReal+b*(installedRisk M e μ s).toReal :=
        add_le_add (mul_le_mul_of_nonneg_left (hx k hk).1 ha)
          (mul_le_mul_of_nonneg_left (hy k hk).1 hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  · intro E hE
    have he : eventMass M e s E (a • x+b • y)-(pureTail k s E).toReal =
        a*(eventMass M e s E x-(pureTail k s E).toReal)+
          b*(eventMass M e s E y-(pureTail k s E).toReal) := by
      have hm : eventMass M e s E (a • x+b • y) =
          a*eventMass M e s E x+b*eventMass M e s E y := by
        simp only [eventMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hm]
      calc
        _ = a*eventMass M e s E x+b*eventMass M e s E y-(a+b)*(pureTail k s E).toReal := by rw [hab, one_mul]
        _ = _ := by ring
    rw [he]
    calc
      _ ≤ |a*(eventMass M e s E x-(pureTail k s E).toReal)|+
          |b*(eventMass M e s E y-(pureTail k s E).toReal)| := abs_add_le _ _
      _ = a*|eventMass M e s E x-(pureTail k s E).toReal|+
          b*|eventMass M e s E y-(pureTail k s E).toReal| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a*(installedLawRisk M e μ s).toReal+b*(installedLawRisk M e μ s).toReal :=
        add_le_add (mul_le_mul_of_nonneg_left ((hx k hk).2 E hE) ha)
          (mul_le_mul_of_nonneg_left ((hy k hk).2 E hE) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- Every fixed actual return of the common window limit obeys both original risk orders
simultaneously at every supported depth of the same countable prior. -/
theorem native_orbit_original_risks (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (eta : Z → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ k : Depth, Tendsto (fun n => windowAverage M (φ n+1) k) atTop (𝓝 eta)) :
    ∀ j : ℕ, ∀ s : ActivePhase,
      eta ᵥ* (returnMatrix M^j*phaseMatrix M s) ∈ riskRegion M e μ s := by
  intro j s k hk
  have hw : Tendsto (fun n => φ n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hc : Continuous (fun v : Z → ℝ => v ᵥ* (returnMatrix M^j*phaseMatrix M s)) :=
    continuous_id.matrix_vecMul continuous_const
  have hl := (hc.tendsto eta).comp (hlim k)
  have linear_limit (c : Z → ℝ) (d b : ℝ)
      (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, 0 < w ∧
        ∀ u v, u < w → v < w →
          (∑ z, (row M (windowHistory (windowCount w (rate k) u)
            (windowCount w (1-(rate k:ℝ)) v) j s) z).toReal*c z)+d ≤ b+ε) :
      (∑ z, (eta ᵥ* (returnMatrix M^j*phaseMatrix M s)) z*c z)+d ≤ b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcont : Continuous (fun v : Z → ℝ => (∑ z, v z*c z)+d) := by fun_prop
    apply le_of_tendsto_of_tendsto ((hcont.tendsto _).comp hl) tendsto_const_nhds
    filter_upwards [hw.eventually (h ε hε)] with n hn
    exact actual_average_bound M _ hn.1 k j s c d (b+ε) hn.2
  constructor
  · suffices h : (∑ z, (eta ᵥ* (returnMatrix M^j*phaseMatrix M s)) z*
        (measurableTotalVariation (tailLaw M e s z) (pureTail k s)).toReal)+0 ≤
        (installedRisk M e μ s).toReal by simpa only [configurationCost, add_zero] using h
    apply linear_limit _ 0 _
    intro ε hε
    filter_upwards [native_countable_target_concentration μ k hk j s ε hε] with w hw'
    refine ⟨by omega, fun u v hu hv => ?_⟩
    have h := (history_pure_bounds M e μ k s
      (windowPhaseHistory (windowCount w (rate k) u) (windowCount w (1-(rate k:ℝ)) v) j s)).1
    convert h.trans (add_le_add (le_refl _) (hw'.2 u v hu hv).le) using 1 <;>
      first | rfl | simp only [configurationCost, windowPhaseHistory, add_zero]
  · intro E hE
    apply abs_le.mpr
    constructor
    · have h : -(eventMass M e s E (eta ᵥ* (returnMatrix M^j*phaseMatrix M s))-
          (pureTail k s E).toReal) ≤ (installedLawRisk M e μ s).toReal := by
        suffices h : (∑ z, (eta ᵥ* (returnMatrix M^j*phaseMatrix M s)) z*
            -(tailLaw M e s z E).toReal)+(pureTail k s E).toReal ≤
            (installedLawRisk M e μ s).toReal by
          simpa only [eventMass, mul_neg, Finset.sum_neg_distrib, neg_sub,
            sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using h
        apply linear_limit (fun z => -(tailLaw M e s z E).toReal) (pureTail k s E).toReal _
        intro ε hε
        filter_upwards [native_countable_target_concentration μ k hk j s ε hε] with w hw'
        refine ⟨by omega, fun u v hu hv => ?_⟩
        have hb := (history_pure_bounds M e μ k s
          (windowPhaseHistory (windowCount w (rate k) u) (windowCount w (1-(rate k:ℝ)) v) j s)).2 E hE
        have hn := (neg_le_abs _).trans (hb.trans (add_le_add (le_refl _) (hw'.2 u v hu hv).le))
        convert hn using 1 <;> try rfl
        simp only [eventMass, mul_neg, Finset.sum_neg_distrib, windowPhaseHistory]
        ring
      linarith
    · apply linear_limit _ (-(pureTail k s E).toReal) _
      intro ε hε
      filter_upwards [native_countable_target_concentration μ k hk j s ε hε] with w hw'
      refine ⟨by omega, fun u v hu hv => ?_⟩
      have hb := (history_pure_bounds M e μ k s
        (windowPhaseHistory (windowCount w (rate k) u) (windowCount w (1-(rate k:ℝ)) v) j s)).2 E hE
      exact (le_abs_self _).trans (hb.trans (add_le_add (le_refl _) (hw'.2 u v hu hv).le))

#print axioms native_orbit_original_risks

private def probabilityRow (v : Z → ℝ) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1) : PMF Z :=
  PMF.ofFintype (fun z => ENNReal.ofReal (v z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hv z), hs, ENNReal.ofReal_one])

private theorem probability_row_real (v : Z → ℝ) (hv : ∀ z, 0 ≤ v z)
    (hs : ∑ z, v z = 1) (z : Z) : (probabilityRow v hv hs z).toReal = v z :=
  ENNReal.toReal_ofReal (hv z)

private theorem configuration_bound (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (k : Depth) (s : ActivePhase) (η : PMF Z)
    (h : configurationCost M e k s (fun z => (η z).toReal) ≤ (installedRisk M e μ s).toReal) :
    (∑ z, η z*measurableTotalVariation (tailLaw M e s z) (pureTail k s)) ≤ installedRisk M e μ s := by
  have hf : (∑ z, η z*measurableTotalVariation (tailLaw M e s z) (pureTail k s)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun z _ => ENNReal.mul_ne_top (η.apply_ne_top z)
      (probability_tv_finite _ _)
  apply (ENNReal.toReal_le_toReal hf (risk_finite M e μ s)).mp
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top (η.apply_ne_top z)
    (probability_tv_finite _ _))]
  simpa only [ENNReal.toReal_mul, configurationCost] using h

private theorem law_bound (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (k : Depth) (s : ActivePhase) (η : PMF Z)
    (h : ∀ E : Set (ValidTail s), MeasurableSet E →
      |eventMass M e s E (fun z => (η z).toReal)-(pureTail k s E).toReal| ≤
        (installedLawRisk M e μ s).toReal) :
    measurableTotalVariation (tailMixture M e s η) (pureTail k s) ≤ installedLawRisk M e μ s := by
  haveI := mixture_probability M e s η
  unfold measurableTotalVariation
  refine iSup_le fun E => max_le ?_ ?_
  · apply (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (measure_ne_top _ _) tsub_le_self) (law_risk_finite M e μ s)).mp
    by_cases hpq : pureTail k s E.val ≤ tailMixture M e s η E.val
    · rw [ENNReal.toReal_sub_of_le hpq (measure_ne_top _ _), mixture_event_real]
      exact (le_abs_self _).trans (h E.val E.property)
    · rw [tsub_eq_zero_of_le (le_of_not_ge hpq)]
      exact ENNReal.toReal_nonneg
  · apply (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (measure_ne_top _ _) tsub_le_self) (law_risk_finite M e μ s)).mp
    by_cases hpq : tailMixture M e s η E.val ≤ pureTail k s E.val
    · rw [ENNReal.toReal_sub_of_le hpq (measure_ne_top _ _), mixture_event_real]
      have hb := (neg_le_abs _).trans (h E.val E.property)
      simpa only [neg_sub] using hb
    · rw [tsub_eq_zero_of_le (le_of_not_ge hpq)]
      exact ENNReal.toReal_nonneg

/-- One pair of actual probability rows precedes the quantifier over all supported depths.
Both phase configuration bounds and both phase complete-law bounds retain their original RHS. -/
theorem native_common_stationary_four_risks (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) :
    ∃ pi tau : PMF Z,
      pi.bind (M.update (.read 1)) = tau ∧ tau.bind (M.update (.read 0)) = pi ∧
      (∀ z ∈ pi.support, ∃ m t j : ℕ, 0 < row M (windowHistory m t j .p) z) ∧
      (∀ z ∈ tau.support, ∃ m t j : ℕ, 0 < row M (windowHistory m t j .beta) z) ∧
      (∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support) ∧
      (∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support) ∧
      (∀ k : Depth, μ k ≠ 0 →
        (∑ x, pi x*measurableTotalVariation (tailLaw M e .p x) (pureTail k .p)) ≤ installedRisk M e μ .p ∧
        (∑ y, tau y*measurableTotalVariation (tailLaw M e .beta y) (pureTail k .beta)) ≤ installedRisk M e μ .beta ∧
        measurableTotalVariation (tailMixture M e .p pi) (pureTail k .p) ≤ installedLawRisk M e μ .p ∧
        measurableTotalVariation (tailMixture M e .beta tau) (pureTail k .beta) ≤ installedLawRisk M e μ .beta) := by
  obtain ⟨p,t,eta,φ,hφ,hlim,hp0,hp1,ht0,ht1,hstat,hforward,hback,hpreach,htreach,hpclose,htclose,htransfer⟩ :=
    native_common_stationary_rows M
  let pi := probabilityRow p hp0 hp1
  let tau := probabilityRow t ht0 ht1
  have hpr : (fun z => (pi z).toReal) = p := funext (probability_row_real p hp0 hp1)
  have htr : (fun z => (tau z).toReal) = t := funext (probability_row_real t ht0 ht1)
  have hbind (v : Z → ℝ) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
      (η : PMF Z) (op : Operation)
      (he : v ᵥ* acquiredMatrix M op = fun z => (η z).toReal) :
      (probabilityRow v hv hs).bind (M.update op) = η := by
    ext z
    apply (ENNReal.toReal_eq_toReal_iff' (((probabilityRow v hv hs).bind _).apply_ne_top z) (η.apply_ne_top z)).mp
    rw [bind_real]
    simp only [probability_row_real]
    exact congrFun he z
  have hps (z : Z) : z ∈ pi.support ↔ 0 < p z := by
    simp only [pi, probabilityRow, PMF.mem_support_iff, PMF.ofFintype_apply, ENNReal.ofReal_ne_zero_iff]
  have hts (z : Z) : z ∈ tau.support ↔ 0 < t z := by
    simp only [tau, probabilityRow, PMF.mem_support_iff, PMF.ofFintype_apply, ENNReal.ofReal_ne_zero_iff]
  have hforward' : pi.bind (M.update (.read 1)) = tau :=
    hbind p hp0 hp1 tau _ (hforward.trans htr.symm)
  have hback' : tau.bind (M.update (.read 0)) = pi :=
    hbind t ht0 ht1 pi _ (hback.trans hpr.symm)
  have hreg := htransfer (riskRegion M e μ) (risk_region_closed M e μ)
    (risk_region_convex M e μ) (native_orbit_original_risks M e μ eta φ hφ hlim)
  refine ⟨pi,tau,hforward',hback',?_,?_,?_,?_,?_⟩
  · intro z hz; exact hpreach z ((hps z).mp hz)
  · intro z hz; exact htreach z ((hts z).mp hz)
  · intro x hx y hy
    apply (hts y).mpr
    apply hpclose x y ((hps x).mp hx)
    exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hy)
      ((M.update (.read 1) x).apply_ne_top y)
  · intro y hy x hx
    apply (hps x).mpr
    apply htclose y x ((hts y).mp hy)
    exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hx)
      ((M.update (.read 0) y).apply_ne_top x)
  · intro k hk
    have hp := hreg.1 k hk
    have ht := hreg.2 k hk
    refine ⟨configuration_bound M e μ k .p pi ?_, configuration_bound M e μ k .beta tau ?_,
      law_bound M e μ k .p pi ?_, law_bound M e μ k .beta tau ?_⟩
    · rw [hpr]; exact hp.1
    · rw [htr]; exact ht.1
    · rw [hpr]; exact hp.2
    · rw [htr]; exact ht.2

#print axioms native_common_stationary_four_risks

/-- The phase selector never changes the common pair when the supported depth changes. -/
def phaseRow (pi tau : PMF Z) : ActivePhase → PMF Z
  | .p => pi
  | .beta => tau

/-- Native common-row implication from the original installed finite observer and its original
countable prior. No exposure, concentration, stationary row or risk conclusion is a premise. -/
theorem native_complete_common_rows (M : Observer Z) (e : InstalledEmitter M) (μ : PMF Depth) :
    ∃ pi tau : PMF Z,
      pi.bind (M.update (.read 1)) = tau ∧ tau.bind (M.update (.read 0)) = pi ∧
      (∀ k : Depth, μ k ≠ 0 → ∀ s : ActivePhase,
        (∑ z, phaseRow pi tau s z*D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
          (tailLaw M e s z) (pureTail k s)) ≤ installedRisk M e μ s ∧
        D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
          (tailMixture M e s (phaseRow pi tau s)) (pureTail k s) ≤ installedLawRisk M e μ s) ∧
      (∀ s : ActivePhase, ∀ z ∈ (phaseRow pi tau s).support, ∃ m t j : ℕ,
        0 < row M (windowHistory m t j s) z ∧
        0 < normalizer μ (windowHistory m t j s) ∧
        M.project z = heldFields s ∧
        fullLaw M e z = (tailLaw M e s z).map (fullRenderer (windowState m t j s) s)) ∧
      (∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support) ∧
      (∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support) ∧
      (∃ q : Z → Z, ∃ hq : ∀ z, M.project (q z) = M.project z,
        (∀ z, retained M pi tau (q z)) ∧
        (∀ z, retained M pi tau z → q z = z) ∧
        (∀ op z y, y ∈ ((clippedObserver M q hq).update op z).support → retained M pi tau y) ∧
        (∀ x ∈ pi.support, (clippedObserver M q hq).update (.read 1) x = M.update (.read 1) x) ∧
        (∀ y ∈ tau.support, (clippedObserver M q hq).update (.read 0) y = M.update (.read 0) y) ∧
        (∀ z, z ∈ pi.support ∨ z ∈ tau.support →
          markedLaw (clippedObserver M q hq) (clippedEmitter M e q hq) (z,none) = markedLaw M e (z,none) ∧
          fullLaw (clippedObserver M q hq) (clippedEmitter M e q hq) z = fullLaw M e z ∧
          ∀ s : ActivePhase, tailLaw (clippedObserver M q hq) (clippedEmitter M e q hq) s z = tailLaw M e s z)) := by
  obtain ⟨pi,tau,hforward,hback,hpreach,htreach,hB,hA,hrisk⟩ :=
    native_common_stationary_four_risks M e μ
  have hreach (s : ActivePhase) (z : Z) (hz : z ∈ (phaseRow pi tau s).support) :
      ∃ m t j : ℕ, 0 < row M (windowHistory m t j s) z := by
    cases s
    · exact hpreach z hz
    · exact htreach z hz
  have hf (s : ActivePhase) (z : Z) (hz : z ∈ (phaseRow pi tau s).support) :
      M.project z = heldFields s := by
    obtain ⟨m,t,j,h⟩ := hreach s z hz
    exact (actual_row_refines M _ _ (windowPhaseHistory m t j s).property.1).1 z h.ne'
  refine ⟨pi,tau,hforward,hback,?_,?_,hB,hA,?_⟩
  · intro k hk s
    have h := hrisk k hk
    cases s
    · exact ⟨h.1,h.2.2.1⟩
    · exact ⟨h.2.1,h.2.2.2⟩
  · intro s z hz
    obtain ⟨m,t,j,h⟩ := hreach s z hz
    have hp := native_paid_window_control M e μ m t j s
    have hlabel := hp.2.2.2.2.2.1 z h.ne'
    exact ⟨m,t,j,h,hp.2.2.2.2.1.1,hlabel.1,hlabel.2⟩
  · exact native_support_clipping M e pi tau (hf .p) (hf .beta) hB hA

#print axioms native_complete_common_rows
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
