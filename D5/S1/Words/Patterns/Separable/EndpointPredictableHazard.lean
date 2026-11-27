/- GID: D5/S1/Words/Patterns/Separable/EndpointPredictableHazard
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointPredictableHazard
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Probability.Martingale.BorelCantelli]
   utility: none
   digest: Strict-past actual endpoint hazard and recurring shifted hits under divergent accumulation. -/

import D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
import Mathlib.Probability.Martingale.BorelCantelli

namespace D5.S1.Words.Patterns.Separable.EndpointPredictableHazard

open ActualCycles ActualCycleLaw EndpointCycleHazard EndpointCanonicalCycle EndpointFirstCycleHitLimit
open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

private def prefixDiscrepancy {k : ℕ} (p : UnboundedTuple k) : ℤ :=
  ∑ i : Fin k, discrepancyDelta (Prefix.nth p i).2

def hitAt (e : ℤ) (k : ℕ) : Set Stream :=
  {ω | hit (ω k).2 (e + streamDiscrepancy k ω)}

private theorem extend_box (k : ℕ) (f : ℕ → Set MarkedCycle) (A : Set MarkedCycle) :
    Set.pi (Finset.range (k + 1) : Set ℕ) (Function.update f k A) =
      Set.pi (Finset.range k : Set ℕ) f ∩ {ω | ω k ∈ A} := by
  rw [Finset.range_add_one, Finset.coe_insert, Set.insert_pi, Function.update_self, Set.inter_comm]
  congr 1
  apply Set.pi_congr rfl
  intro i hi
  rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi))]


/-- Actual finite-prefix factorization for an arbitrary test on the next mark. -/
private theorem prefix_next_measure {k : ℕ} (p : UnboundedTuple k) (A : Set MarkedCycle) :
    streamMeasure (Prefix.cylinder p ∩ {ω | ω k ∈ A}) =
      streamMeasure (Prefix.cylinder p) * cyclePMF.toMeasure A := by
  rw [Prefix.box, ← extend_box]
  change (Measure.infinitePi (fun _ : ℕ => cyclePMF.toMeasure)) _ =
    (Measure.infinitePi (fun _ : ℕ => cyclePMF.toMeasure)) _ * _
  rw [Measure.infinitePi_pi (fun _ : ℕ => cyclePMF.toMeasure) (fun _ _ => trivial),
      Measure.infinitePi_pi (fun _ : ℕ => cyclePMF.toMeasure) (fun _ _ => trivial)]
  rw [Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi))]
  · rw [Function.update_self]

/-- The actual next hit has the stated conditional hazard on every past cylinder.
The unnormalized identity remains valid even for a null cylinder. -/
private theorem predictable_hazard_on_prefix {k : ℕ} (p : UnboundedTuple k) (e : ℤ) :
    streamMeasure (Prefix.cylinder p ∩ hitAt e k) =
      streamMeasure (Prefix.cylinder p) * nextHazard (e + prefixDiscrepancy p) := by
  have eq : Prefix.cylinder p ∩ hitAt e k =
      Prefix.cylinder p ∩ {ω | ω k ∈ {c : MarkedCycle | hit c.2 (e + prefixDiscrepancy p)}} := by
    ext ω
    simp only [Set.mem_inter_iff, hitAt, Set.mem_ofPred_eq]
    have same (h : ω ∈ Prefix.cylinder p) :
        streamDiscrepancy k ω = prefixDiscrepancy p := by
      unfold streamDiscrepancy prefixDiscrepancy
      apply Finset.sum_congr rfl
      intro i _
      rw [show ω i.val = Prefix.nth p i from h i]
    exact ⟨fun ⟨h, hh⟩ => ⟨h, congrArg (e + ·) (same h) ▸ hh⟩,
      fun ⟨h, hh⟩ => ⟨h, congrArg (e + ·) (same h).symm ▸ hh⟩⟩
  rw [eq]
  exact prefix_next_measure p {c : MarkedCycle | hit c.2 (e + prefixDiscrepancy p)}



private def pastCoordinates (k : ℕ) (ω : Stream) (i : Fin k) : MarkedCycle := ω i.val

abbrev pastSigma (k : ℕ) : MeasurableSpace Stream :=
  MeasurableSpace.comap (pastCoordinates k) inferInstance

private theorem measurable_pastCoordinates (k : ℕ) : Measurable (pastCoordinates k) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply i.val

private theorem measurable_hazard_past (e : ℤ) (k : ℕ) :
    @Measurable Stream ℝ≥0∞ (pastSigma k) inferInstance
      (fun ω => nextHazard (e + streamDiscrepancy k ω)) := by
  let f : (Fin k → MarkedCycle) → ℝ≥0∞ :=
    fun x => nextHazard (e + ∑ i : Fin k, discrepancyDelta (x i).2)
  exact (measurable_of_countable f).comp (comap_measurable (pastCoordinates k))

private theorem measurableSet_hitAt (e : ℤ) (k : ℕ) : MeasurableSet (hitAt e k) := by
  let f : Stream → (Fin (k + 1) → MarkedCycle) := pastCoordinates (k + 1)
  let A : Set (Fin (k + 1) → MarkedCycle) :=
    {x | hit (x (Fin.last k)).2 (e + ∑ i : Fin k, discrepancyDelta (x i.castSucc).2)}
  change MeasurableSet (f ⁻¹' A)
  exact (A.to_countable.measurableSet).preimage
    (measurable_pastCoordinates (k + 1))

private theorem cylinder_eq_pastFiber {k : ℕ} (p : UnboundedTuple k) :
    Prefix.cylinder p = pastCoordinates k ⁻¹' {Prefix.nth p} := by
  ext ω
  change (∀ i : Fin k, ω i.val = Prefix.nth p i) ↔
    pastCoordinates k ω ∈ ({Prefix.nth p} : Set (Fin k → MarkedCycle))
  rw [Set.mem_singleton_iff]
  exact ⟨funext, fun h i => congrFun h i⟩

/-- The exact strict-past test, without any division by atom mass. -/
private theorem predictable_hazard_on_past_event (e : ℤ) (k : ℕ) (s : Set Stream)
    (hs : MeasurableSet[pastSigma k] s) :
    streamMeasure (s ∩ hitAt e k) =
      ∫⁻ ω in s, nextHazard (e + streamDiscrepancy k ω) ∂streamMeasure := by
  obtain ⟨t, _, ht⟩ := MeasurableSpace.measurableSet_comap.mp (by simpa only [pastSigma] using hs)
  let A : t → Set Stream := fun x => pastCoordinates k ⁻¹' {(x : Fin k → MarkedCycle)}
  have hA : ∀ x, MeasurableSet (A x) := fun x =>
    (measurableSet_singleton (x : Fin k → MarkedCycle)).preimage
      (measurable_pastCoordinates k)
  have hdisj : Pairwise (fun x y => Disjoint (A x) (A y)) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    intro ω hx hy
    apply hxy
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hy)
  have hunion : s = ⋃ x, A x := by
    rw [← ht]
    ext ω
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨⟨pastCoordinates k ω, h⟩, rfl⟩
    · intro h
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
      change pastCoordinates k ω ∈ t
      rw [Set.mem_singleton_iff.mp hx]
      exact x.property
  have hhitunion : s ∩ hitAt e k = ⋃ x, A x ∩ hitAt e k := by
    rw [hunion, Set.iUnion_inter]
  have hhitdisj : Pairwise (fun x y => Disjoint (A x ∩ hitAt e k) (A y ∩ hitAt e k)) :=
    fun _ _ hxy => (hdisj hxy).mono Set.inter_subset_left Set.inter_subset_left
  rw [hhitunion, measure_iUnion hhitdisj (fun x => (hA x).inter (measurableSet_hitAt e k))]
  conv_rhs => rw [hunion, lintegral_iUnion hA hdisj]
  apply tsum_congr
  intro x
  obtain ⟨p, hcoords⟩ := (actual_countable_cycle_law.2.2.1 k).2 x
  have hmass := predictable_hazard_on_prefix p e
  rw [cylinder_eq_pastFiber, hcoords] at hmass
  change streamMeasure (A x ∩ hitAt e k) =
    ∫⁻ ω in A x, nextHazard (e + streamDiscrepancy k ω) ∂streamMeasure
  rw [hmass]
  have heq : Set.EqOn (fun ω => nextHazard (e + streamDiscrepancy k ω))
      (fun _ => nextHazard (e + prefixDiscrepancy p)) (A x) := by
    intro ω hω
    have hx : pastCoordinates k ω = Prefix.nth p :=
      (Set.mem_singleton_iff.mp hω).trans hcoords.symm
    apply congrArg (fun z : ℤ => nextHazard (e + z))
    unfold streamDiscrepancy prefixDiscrepancy
    apply Finset.sum_congr rfl
    intro i _
    rw [show ω i.val = Prefix.nth p i from congrFun hx i]
  rw [setLIntegral_congr_fun (hA x) heq, setLIntegral_const, mul_comm]


/-- The predictable hazard integrates as the indicator of the next actual hit. -/
private theorem predictable_hazard_integral_eq_indicator (e : ℤ) (k : ℕ) (s : Set Stream)
    (hs : MeasurableSet[pastSigma k] s) :
    (∫⁻ ω in s, nextHazard (e + streamDiscrepancy k ω) ∂streamMeasure) =
      ∫⁻ ω in s, (hitAt e k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂streamMeasure := by
  rw [lintegral_indicator (measurableSet_hitAt e k), setLIntegral_one,
    Measure.restrict_apply (measurableSet_hitAt e k), Set.inter_comm,
    predictable_hazard_on_past_event e k s hs]

/-- Turn the strict-past ENNReal testing identity into the real conditional
expectation used by Lévy's generalized Borel–Cantelli lemma. -/
private theorem hazard_toReal_ae_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A : Set Ω) (hA : @MeasurableSet Ω mΩ A) (q : Ω → ℝ≥0∞)
    (hq : ∀ ω, q ω ≤ 1) (hqM : @Measurable Ω ℝ≥0∞ m _ q)
    (htest : ∀ s : Set Ω, MeasurableSet[m] s →
      (∫⁻ ω in s, q ω ∂μ) =
       ∫⁻ ω in s, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) :
    (fun ω => (q ω).toReal) =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m] := by
  have hqtop (ω : Ω) : q ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hq ω)
  let f : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : @Measurable Ω ℝ≥0∞ mΩ _ f := measurable_const.indicator hA
  have hftop (ω : Ω) : f ω ≠ ∞ := by
    by_cases h : ω ∈ A <;> simp [f, h]
  have hrealA : (fun ω => (f ω).toReal) = A.indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [f, h]
  have hqGlobal : @Measurable Ω ℝ≥0∞ mΩ _ q := hqM.mono hm le_rfl
  have hiA : Integrable (A.indicator (1 : Ω → ℝ)) μ := (integrable_const (1:ℝ)).indicator hA
  have hiq : Integrable (fun ω => (q ω).toReal) μ := by
    apply (integrable_toReal_iff (μ := μ) hqGlobal.aemeasurable (ae_of_all _ hqtop)).2
    apply ne_of_lt
    calc
      (∫⁻ ω, q ω ∂μ) ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_mono hq
      _ < ∞ := by simp [measure_lt_top]
  have hmeas : @Measurable Ω ℝ m _ (fun ω => (q ω).toReal) := ENNReal.measurable_toReal.comp hqM
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hiA
    (fun _ _ _ => hiq.integrableOn) (fun s hs _ => ?_) hmeas.stronglyMeasurable.aestronglyMeasurable
  rw [← hrealA, integral_toReal hqGlobal.aemeasurable (ae_of_all _ fun x => (lt_top_iff_ne_top).2 (hqtop x)),
    integral_toReal hf.aemeasurable (ae_of_all _ fun x => (lt_top_iff_ne_top).2 (hftop x))]
  exact congrArg ENNReal.toReal (htest s hs)

/-- A divergent ENNReal series of probabilities has real partial sums
tending to positive infinity. This avoids totalized real infinite sums. -/
private theorem real_partial_sums_tendsto_of_ennreal_tsum_top
    (q : ℕ → ℝ≥0∞) (hq : ∀ k, q k ≤ 1) (hdiv : ∑' k, q k = ∞) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (q k).toReal) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => ENNReal.toReal_nonneg)).mp
  intro hs
  have he (k : ℕ) : ((q k).toNNReal : ℝ≥0∞) = q k :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hq k))
  have hs' : Summable (fun k => ((q k).toNNReal : ℝ)) := hs
  have ht := ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hs'
  simp_rw [he] at ht
  exact ht hdiv

/-- The events are indexed by the upcoming cycle k, and are measurable in
strict past k+1 (the past after revealing that cycle). No independence needed. -/
private theorem ae_recurring_hits_of_divergent_hazard {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ)
    (hit : ℕ → Set Ω) (q : ℕ → Ω → ℝ≥0∞)
    (hadapt : ∀ k, MeasurableSet[ℱ (k+1)] (hit k))
    (hq : ∀ k ω, q k ω ≤ 1)
    (hqm : ∀ k, @Measurable Ω ℝ≥0∞ (ℱ k) _ (q k))
    (htest : ∀ k s, MeasurableSet[ℱ k] s →
      (∫⁻ ω in s, q k ω ∂μ) =
      ∫⁻ ω in s, (hit k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ)
    (hdiv : ∀ᵐ ω ∂μ, ∑' k, q k ω = ∞) :
    ∀ᵐ ω ∂μ, ω ∈ limsup hit atTop := by
  let s : ℕ → Set Ω
    | 0 => ∅
    | k+1 => hit k
  have hS (n : ℕ) : MeasurableSet[ℱ n] (s n) := by
    cases n with
    | zero =>
      let _ : MeasurableSpace Ω := ℱ 0
      exact MeasurableSet.empty
    | succ n => exact hadapt n
  have he (k : ℕ) : (fun ω => (q k ω).toReal) =ᵐ[μ]
      μ[(s (k+1)).indicator (1 : Ω → ℝ) | ℱ k] :=
    hazard_toReal_ae_condExp μ (ℱ.le k) (hit k) (ℱ.le (k+1) _ (hadapt k)) (q k)
      (hq k) (hqm k) (htest k)
  have heall := ae_all_iff.mpr he
  have hl := ae_mem_limsup_atTop_iff (ℱ := ℱ) μ hS
  filter_upwards [hdiv, heall, hl] with ω hd hw hl'
  have ht : Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k+1)).indicator (1 : Ω → ℝ) | ℱ k]) ω) atTop atTop := by
    have ht' := real_partial_sums_tendsto_of_ennreal_tsum_top (fun k => q k ω)
      (fun k => hq k ω) hd
    have hh : (fun n => ∑ k ∈ Finset.range n, (q k ω).toReal) =
        fun n => ∑ k ∈ Finset.range n, (μ[(s (k+1)).indicator (1 : Ω → ℝ) | ℱ k]) ω :=
      funext fun n => Finset.sum_congr rfl (fun k _ => hw k)
    rwa [hh] at ht'
  have hm := hl'.2 ht
  rwa [← limsup_nat_add s 1] at hm

/-- At index k the first k marks, and not the upcoming mark k, are visible. -/
private def actualStrictPast : Filtration ℕ (inferInstance : MeasurableSpace Stream) where
  seq := pastSigma
  mono' := by
    intro j k hjk
    let cut : (Fin k → MarkedCycle) → (Fin j → MarkedCycle) :=
      fun v i => v (Fin.castLE hjk i)
    have hcut : Measurable cut := measurable_pi_iff.2 fun i =>
      measurable_pi_apply (Fin.castLE hjk i)
    exact MeasurableSpace.comap_le_comap_of_eq_comp cut hcut rfl
  le' k := (measurable_pi_iff.2 fun i : Fin k => measurable_pi_apply i.val).comap_le

private theorem actual_hitAt_adapted (e : ℤ) (k : ℕ) :
    MeasurableSet[actualStrictPast (k+1)] (hitAt e k) := by
  let A : Set (Fin (k+1) → MarkedCycle) :=
    {x | hit (x (Fin.last k)).2 (e + ∑ i : Fin k, discrepancyDelta (x i.castSucc).2)}
  exact MeasurableSpace.measurableSet_comap.mpr ⟨A, A.to_countable.measurableSet, rfl⟩

private theorem actual_q_le_one (z : ℤ) : nextHazard z ≤ 1 := by
  unfold nextHazard
  exact prob_le_one

/-- Conditional Borel–Cantelli on the actual cycle stream: divergent accumulated
hazard forces arbitrarily late shifted actual hits. No assumption of independent
hit events and no transfer to finite permutations are made. -/
private theorem actual_ae_recurring_hits_of_hazard (e : ℤ)
    (hdiv : ∀ᵐ ω ∂streamMeasure, ∑' k, nextHazard (e + streamDiscrepancy k ω) = ∞) :
    ∀ᵐ ω ∂streamMeasure, ∀ N : ℕ, ∃ k ≥ N, hit (ω k).2 (e + streamDiscrepancy k ω) := by
  have hlim := ae_recurring_hits_of_divergent_hazard streamMeasure actualStrictPast (hitAt e)
    (fun k ω => nextHazard (e + streamDiscrepancy k ω))
    (actual_hitAt_adapted e) (fun _ _ => actual_q_le_one _)
    (measurable_hazard_past e) (predictable_hazard_integral_eq_indicator e) hdiv
  filter_upwards [hlim] with ω hω
  exact frequently_atTop.mp (mem_limsup_iff_frequently_mem.mp hω)

/-- The actual marked-cycle hit has the next-cycle hazard as its strict-past
conditional probability. If the actual hazard sums diverge almost surely, hits
recur arbitrarily late. Neither conclusion assumes independent hit events. -/
theorem actual_predictable_hazard_and_recurrence (e : ℤ) :
    (∀ (k : ℕ) (s : Set Stream), MeasurableSet[pastSigma k] s →
      streamMeasure (s ∩ hitAt e k) =
        ∫⁻ ω in s, nextHazard (e + streamDiscrepancy k ω) ∂streamMeasure) ∧
    ((∀ᵐ ω ∂streamMeasure, ∑' k, nextHazard (e + streamDiscrepancy k ω) = ∞) →
      ∀ᵐ ω ∂streamMeasure, ∀ N : ℕ, ∃ k ≥ N, ω ∈ hitAt e k) :=
  ⟨predictable_hazard_on_past_event e, actual_ae_recurring_hits_of_hazard e⟩

#print axioms actual_predictable_hazard_and_recurrence

end D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
