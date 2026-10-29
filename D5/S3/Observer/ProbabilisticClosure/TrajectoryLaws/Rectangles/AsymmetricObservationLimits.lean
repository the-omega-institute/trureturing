/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual asymmetric erased-bit conditionals converge in both ordered half-line limits. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing

/-! Asymmetric finite windows and both ordered half-line limits under a single visible law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Filter
open scoped Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.AsymmetricObservationLimits

abbrev Visible := ℤ → Bool

/-- Chronological observations with independently chosen left and right lengths. -/
def observation (l r : ℕ) (z : Visible) := (leftWord l z, rightWord r z)

/-- Actual conditional probability under the supplied single visible law. -/
def mean {E : Type*} [MeasurableSpace E] (μ : Measure Visible)
    [IsProbabilityMeasure μ] (o : Visible → E) : Visible → ℝ :=
  bitPredictor μ (fun z => z 0) o ∘ o

/-- Almost-sure and mean-square convergence; the latter is convergence in L². -/
def MeanSquareLimit (μ : Measure Visible) (f : ℕ → Visible → ℝ) (g : Visible → ℝ) : Prop :=
  (∀ᵐ z ∂μ, Tendsto (fun n => f n z) atTop (𝓝 (g z))) ∧
    (∀ n, MemLp (f n) 2 μ) ∧ MemLp g 2 μ ∧
    Tendsto (fun n => ∫ z, (f n z - g z)^2 ∂μ) atTop (𝓝 0)

private abbrev leftField (n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (leftWord n) inferInstance
private abbrev rightField (n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (rightWord n) inferInstance

private theorem pair_field {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (a : Visible → E) (b : Visible → F) :
    MeasurableSpace.comap (fun z => (a z,b z)) inferInstance =
      MeasurableSpace.comap a inferInstance ⊔ MeasurableSpace.comap b inferInstance := by
  change MeasurableSpace.comap (fun z => (a z,b z))
    (MeasurableSpace.prod inferInstance inferInstance) = _
  rw [MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

private theorem left_mono : Monotone leftField := by
  apply monotone_nat_of_le_succ
  intro n
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun w : Fin (n+1) → Bool => fun i : Fin n => w i.succ) (by fun_prop)
  funext z i
  dsimp [leftWord]
  apply congrArg z
  push_cast
  omega

private theorem right_mono : Monotone rightField := by
  apply monotone_nat_of_le_succ
  intro n
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (fun w : Fin (n+1) → Bool => fun i : Fin n => w i.castSucc) (by fun_prop) rfl

private theorem left_sup : (⨆ n, leftField n) = MeasurableSpace.comap before inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : ℕ → Bool => fun i : Fin n => w (n-1-i.val)) (by fun_prop)
    funext z i
    dsimp [leftWord,before]
    apply congrArg z
    have hi := i.isLt
    omega
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ n, leftField n) inferInstance
        (fun z => before z n) := by
      have h : Measurable[leftField (n+1)] (fun z => leftWord (n+1) z 0) :=
        (measurable_pi_apply 0).comp (show Measurable[leftField (n+1)] (leftWord (n+1)) from Measurable.of_comap_le le_rfl)
      convert h.mono (le_iSup leftField (n+1)) le_rfl using 1
      funext z
      dsimp [leftWord,before]
      congr 1
    letI : MeasurableSpace Visible := ⨆ n, leftField n
    exact (Measurable.of_eval hm).comap_le

private theorem right_sup : (⨆ n, rightField n) = MeasurableSpace.comap after inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : ℕ → Bool => fun i : Fin n => w i.val) (by fun_prop) rfl
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ n, rightField n) inferInstance
        (fun z => after z n) := by
      have h : Measurable[rightField (n+1)] (fun z => rightWord (n+1) z (Fin.last n)) :=
        (measurable_pi_apply (Fin.last n)).comp (show Measurable[rightField (n+1)] (rightWord (n+1)) from Measurable.of_comap_le le_rfl)
      exact h.mono (le_iSup rightField (n+1)) le_rfl
    letI : MeasurableSpace Visible := ⨆ n, rightField n
    exact (Measurable.of_eval hm).comap_le

private theorem mean_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure Visible) [IsProbabilityMeasure μ] (o : Visible → E) (z : Visible) :
    0 ≤ mean μ o z ∧ mean μ o z ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

private theorem observation_limit {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)]
    {F : Type*} [MeasurableSpace F] (μ : Measure Visible) [IsProbabilityMeasure μ]
    (o : ∀ n, Visible → E n) (v : Visible → F) (ho : ∀ n, Measurable (o n))
    (hv : Measurable v)
    (hmono : Monotone (fun n => MeasurableSpace.comap (o n) inferInstance))
    (hsup : (⨆ n, MeasurableSpace.comap (o n) inferInstance) =
      MeasurableSpace.comap v inferInstance) :
    MeanSquareLimit μ (fun n => mean μ (o n)) (mean μ v) := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Visible) :=
    ⟨fun n => MeasurableSpace.comap (o n) inferInstance,hmono,fun n => (ho n).comap_le⟩
  have hp (n : ℕ) := bitPredictor_condExp μ (fun z : Visible => z 0) (o n)
    (measurable_pi_apply 0) (ho n)
  have hq := bitPredictor_condExp μ (fun z : Visible => z 0) v
    (measurable_pi_apply 0) hv
  have hc := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) erasedBit
  have ha : ∀ᵐ z ∂μ, Tendsto (fun n => mean μ (o n) z) atTop (𝓝 (mean μ v z)) := by
    have hall := ae_all_iff.mpr hp
    filter_upwards [hc,hall,hq] with z hz hpz hqz
    change Tendsto (fun n => μ[erasedBit | MeasurableSpace.comap (o n) inferInstance] z)
      atTop (𝓝 (μ[erasedBit | ⨆ n, MeasurableSpace.comap (o n) inferInstance] z)) at hz
    change mean μ v z = μ[erasedBit | MeasurableSpace.comap v inferInstance] z at hqz
    rw [hsup, ← hqz] at hz
    exact hz.congr (fun n => (hpz n).symm)
  refine ⟨ha,?_,?_,?_⟩
  · intro n
    exact memLp_of_bounded (Filter.Eventually.of_forall (mean_bounds μ (o n)))
      ((bitPredictor_measurable μ _ _).comp (ho n)).aestronglyMeasurable 2
  · exact memLp_of_bounded (Filter.Eventually.of_forall (mean_bounds μ v))
      ((bitPredictor_measurable μ _ _).comp hv).aestronglyMeasurable 2
  have hd := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n z => (mean μ (o n) z-mean μ v z)^2) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (((bitPredictor_measurable μ _ _).comp (ho n)).sub
      ((bitPredictor_measurable μ _ _).comp hv)).pow_const 2 |>.aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall fun z => by
      obtain ⟨ha,hb⟩ := mean_bounds μ (o n) z
      obtain ⟨hc,hd⟩ := mean_bounds μ v z
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hprod := mul_nonneg (show 0 ≤ 1-(mean μ (o n) z-mean μ v z) by linarith)
        (show 0 ≤ 1+(mean μ (o n) z-mean μ v z) by linarith)
      nlinarith)
    (ha.mono fun z hz => by simpa using (hz.sub (tendsto_const_nhds (x := mean μ v z))).pow 2)
  simpa using hd

/-- Both ordered completions use actual conditional distributions under one law.
The finite-side length may be zero; the opposite complete half-line is retained. -/
theorem ordered_half_line_limits (μ : Measure Visible) [IsProbabilityMeasure μ] (j : ℕ) :
    (∀ n : ℕ, MeanSquareLimit μ (fun k => mean μ (observation k n))
      (mean μ (rightObservation n))) ∧
    (∀ n : ℕ, MeanSquareLimit μ (fun k => mean μ (observation n k))
      (mean μ (leftObservation n))) ∧
    MeanSquareLimit μ (fun n => mean μ (rightObservation n)) (mean μ exterior) ∧
    MeanSquareLimit μ (fun n => mean μ (leftObservation n)) (mean μ exterior) ∧
    MeanSquareLimit μ (fun n => mean μ (observation j n)) (mean μ (leftObservation j)) ∧
    MeanSquareLimit μ (fun n => mean μ (observation n j)) (mean μ (rightObservation j)) := by
  have hfield (l r : ℕ) : MeasurableSpace.comap (observation l r) inferInstance =
      leftField l ⊔ rightField r := pair_field _ _
  have hL (n : ℕ) : MeasurableSpace.comap (leftObservation n) inferInstance =
      leftField n ⊔ MeasurableSpace.comap after inferInstance := pair_field _ _
  have hR (n : ℕ) : MeasurableSpace.comap (rightObservation n) inferInstance =
      MeasurableSpace.comap before inferInstance ⊔ rightField n := pair_field _ _
  have hE : MeasurableSpace.comap exterior inferInstance =
      MeasurableSpace.comap before inferInstance ⊔ MeasurableSpace.comap after inferInstance :=
    pair_field _ _
  have hfiniteL (n : ℕ) := observation_limit μ (fun k => observation k n) (rightObservation n)
    (fun k => by unfold observation leftWord rightWord; fun_prop)
    (by unfold rightObservation before rightWord; fun_prop)
    (by intro a b hab; simp only [hfield]; exact sup_le_sup (left_mono hab) le_rfl)
    (by simp only [hfield,hR,iSup_sup_eq,left_sup,iSup_const])
  have hfiniteR (n : ℕ) := observation_limit μ (fun k => observation n k) (leftObservation n)
    (fun k => by unfold observation leftWord rightWord; fun_prop)
    (by unfold leftObservation after leftWord; fun_prop)
    (by intro a b hab; simp only [hfield]; exact sup_le_sup le_rfl (right_mono hab))
    (by simp only [hfield,hL,iSup_sup_eq,right_sup,iSup_const])
  refine ⟨hfiniteL,hfiniteR,?_,?_,hfiniteR j,hfiniteL j⟩
  · exact observation_limit μ rightObservation exterior
      (fun n => by unfold rightObservation before rightWord; fun_prop)
      (by unfold exterior before after; fun_prop)
      (by intro a b hab; simp only [hR]; exact sup_le_sup le_rfl (right_mono hab))
      (by simp only [hR,hE,iSup_sup_eq,right_sup,iSup_const])
  · exact observation_limit μ leftObservation exterior
      (fun n => by unfold leftObservation after leftWord; fun_prop)
      (by unfold exterior before after; fun_prop)
      (by intro a b hab; simp only [hL]; exact sup_le_sup (left_mono hab) le_rfl)
      (by simp only [hL,hE,iSup_sup_eq,left_sup,iSup_const])

open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw

private theorem record_fiber (l r : ℕ) (z : Visible) :
    record (List.ofFn (leftWord l z)) (List.ofFn (rightWord r z)) =
      observation l r ⁻¹' {observation l r z} := by
  ext y
  change y ∈ record (List.ofFn (leftWord l z)) (List.ofFn (rightWord r z)) ↔
    observation l r y = observation l r z
  simp only [record,block,Set.mem_inter_iff,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hl,hr⟩
    apply Prod.ext
    · funext i
      have hi := hl (Fin.cast (by simp : (List.ofFn (leftWord l z)).length = l).symm i)
      simpa [List.get_ofFn,leftWord,observation] using hi
    · funext i
      have hi := hr (Fin.cast (by simp : (List.ofFn (rightWord r z)).length = r).symm i)
      simpa [List.get_ofFn,rightWord,observation,add_comm] using hi
  · intro he
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    constructor
    · intro i
      have hi := congrFun hl (Fin.cast (by simp : (List.ofFn (leftWord l z)).length = l) i)
      simpa [List.get_ofFn,leftWord,observation] using hi
    · intro i
      have hi := congrFun hr (Fin.cast (by simp : (List.ofFn (rightWord r z)).length = r) i)
      simpa [List.get_ofFn,rightWord,observation,add_comm] using hi

private theorem finite_ratio (μ : Measure Visible) [IsProbabilityMeasure μ] (l r : ℕ) :
    ∀ᵐ z ∂μ,
      0 < μ.real (record (List.ofFn (leftWord l z)) (List.ofFn (rightWord r z))) ∧
      mean μ (observation l r) z =
        recordPosterior μ (List.ofFn (leftWord l z)) (List.ofFn (rightWord r z)) := by
  let o := observation l r
  have ho : Measurable o := by unfold o observation leftWord rightWord; fun_prop
  have hnull : ∀ᵐ z ∂μ, ∀ e, μ (o ⁻¹' {e}) = 0 → o z ≠ e := by
    apply ae_all_iff.mpr
    intro e
    by_cases he : μ (o ⁻¹' {e}) = 0
    · have hn : ∀ᵐ z ∂μ, z ∉ o ⁻¹' {e} := by
        rw [ae_iff]
        convert he using 1
        congr 1
        ext a
        simp
      exact hn.mono fun z hz _ => hz
    · exact Filter.Eventually.of_forall fun z hz => (he hz).elim
  filter_upwards [hnull] with z hz
  have hp : μ (o ⁻¹' {o z}) ≠ 0 := fun h => hz (o z) h rfl
  have hpos : 0 < μ.real (o ⁻¹' {o z}) := ENNReal.toReal_pos hp (measure_ne_top _ _)
  rw [record_fiber]
  refine ⟨hpos,?_⟩
  have hpmap : μ.map o {o z} ≠ 0 := by
    rwa [Measure.map_apply ho (measurableSet_singleton _)]
  have hk := condDistrib_apply_of_ne_zero (μ := μ) ho
    (measurable_pi_apply (0 : ℤ)) (o z) hpmap {true}
  rw [Measure.map_apply ho (measurableSet_singleton _),
    Measure.map_apply (ho.prodMk (measurable_pi_apply (0 : ℤ)))
      ((measurableSet_singleton _).prod (measurableSet_singleton true))] at hk
  have hs : (fun z : Visible => (o z,z 0)) ⁻¹' ({o z} ×ˢ {true}) =
      (o ⁻¹' {o z}) ∩ {z | z 0 = true} := rfl
  rw [hs] at hk
  have hkreal := congrArg ENNReal.toReal hk
  simpa only [mean,Function.comp_apply,bitPredictor,recordPosterior,record_fiber,
    measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm] using hkreal

private theorem left_append (k j : ℕ) (z : Visible) :
    List.ofFn (leftWord (k+j) z) =
      List.ofFn (fun i : Fin k => z (-((k+j : ℕ) : ℤ)+i)) ++ List.ofFn (leftWord j z) := by
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext i
  dsimp [leftWord]
  apply congrArg z
  push_cast
  omega

private theorem right_append (j k : ℕ) (z : Visible) :
    List.ofFn (rightWord (j+k) z) =
      List.ofFn (rightWord j z) ++ List.ofFn (fun i : Fin k => z (j+i+1)) := by
  rw [List.ofFn_add]
  congr 1

/-- Original full blocks ending at -1; the uncounted prefix is the remainder modulo b. -/
def leftCount (w : List Bool) (b j : ℕ) (z : Visible) : ℕ :=
  originalSuccessCount w b (j/b) ((List.ofFn (leftWord j z)).drop (j%b))

/-- Original full blocks starting at 1. -/
def rightCount (w : List Bool) (b j : ℕ) (z : Visible) : ℕ :=
  originalSuccessCount w b (j/b) (List.ofFn (rightWord j z))

open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages

/-- The actual original-cylinder finite comparisons pass through both ordered half-line
limits, on one common null-set convention for all retained lengths. -/
theorem same_law_counted_half_line_smoothing
    {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (hc : HasOriginalCylinders J θ) (w : List Bool) (hw : w ≠ [])
    (R : Rectangle (product θ w)) :
    let μ := J.map Prod.snd
    let b := w.length + Fintype.card H
    let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
    ∀ᵐ z ∂μ, ∀ j : ℕ,
      |mean μ exterior z-mean μ (leftObservation j) z| ≤ ρ ^ leftCount w b j z ∧
      |mean μ exterior z-mean μ (rightObservation j) z| ≤ ρ ^ rightCount w b j z := by
  dsimp only
  let μ := J.map Prod.snd
  let b := w.length + Fintype.card H
  let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
  have hfinite := finite_record_smoothing_by_original_success_count θ J hc w hw R
  have hLF (k j n : ℕ) : ∀ᵐ z ∂μ,
      |mean μ (observation (k+j) n) z-mean μ (observation j n) z| ≤
        ρ ^ leftCount w b j z := by
    filter_upwards [finite_ratio μ (k+j) n,finite_ratio μ j n] with z hz1 hz2
    have h := hfinite.1
      (List.ofFn (fun i : Fin k => z (-((k+j : ℕ) : ℤ)+i)))
      (List.ofFn (leftWord j z)) (List.ofFn (rightWord n z))
      (by rw [← left_append k j z]; exact hz1.1) hz2.1
    rw [← left_append k j z] at h
    rw [hz1.2,hz2.2]
    simpa only [List.length_ofFn,μ,ρ,b,leftCount,rightCount] using h
  have hRF (k j n : ℕ) : ∀ᵐ z ∂μ,
      |mean μ (observation n (j+k)) z-mean μ (observation n j) z| ≤
        ρ ^ rightCount w b j z := by
    filter_upwards [finite_ratio μ n (j+k),finite_ratio μ n j] with z hz1 hz2
    have h := hfinite.2 (List.ofFn (leftWord n z)) (List.ofFn (rightWord j z))
      (List.ofFn (fun i : Fin k => z (j+i+1)))
      (by rw [← right_append j k z]; exact hz1.1) hz2.1
    rw [← right_append j k z] at h
    rw [hz1.2,hz2.2]
    simpa only [List.length_ofFn,μ,ρ,b,leftCount,rightCount] using h
  have hshift (j : ℕ) : Tendsto (fun k : ℕ => k+j) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    exact eventually_atTop.mpr ⟨a,fun k hk => by omega⟩
  have hL1 (j n : ℕ) : ∀ᵐ z ∂μ,
      |mean μ (rightObservation n) z-mean μ (observation j n) z| ≤
        ρ ^ leftCount w b j z := by
    have hlim := ((ordered_half_line_limits μ j).1 n).1
    filter_upwards [hlim,ae_all_iff.mpr (fun k => hLF k j n)] with z hz hb
    apply le_of_tendsto (((hz.comp (hshift j)).sub
      (tendsto_const_nhds (x := mean μ (observation j n) z))).abs)
    exact Filter.Eventually.of_forall hb
  have hR1 (j n : ℕ) : ∀ᵐ z ∂μ,
      |mean μ (leftObservation n) z-mean μ (observation n j) z| ≤
        ρ ^ rightCount w b j z := by
    have hlim := ((ordered_half_line_limits μ j).2.1 n).1
    filter_upwards [hlim,ae_all_iff.mpr (fun k => hRF k j n)] with z hz hb
    have hlim' : Tendsto (fun k => mean μ (observation n (j+k)) z)
        atTop (𝓝 (mean μ (leftObservation n) z)) := by
      simpa only [Function.comp_def,Nat.add_comm] using hz.comp (hshift j)
    exact le_of_tendsto ((hlim'.sub
      (tendsto_const_nhds (x := mean μ (observation n j) z))).abs)
      (Filter.Eventually.of_forall hb)
  apply ae_all_iff.mpr
  intro j
  obtain ⟨_,_,hfullR,hfullL,hcutL,hcutR⟩ := ordered_half_line_limits μ j
  filter_upwards [hfullR.1,hfullL.1,hcutL.1,hcutR.1,
    ae_all_iff.mpr (hL1 j),ae_all_iff.mpr (hR1 j)] with z hfR hfL hcL hcR hbL hbR
  exact ⟨le_of_tendsto ((hfR.sub hcL).abs) (Filter.Eventually.of_forall hbL),
    le_of_tendsto ((hfL.sub hcR).abs) (Filter.Eventually.of_forall hbR)⟩

#print axioms same_law_counted_half_line_smoothing

#print axioms ordered_half_line_limits
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.AsymmetricObservationLimits
