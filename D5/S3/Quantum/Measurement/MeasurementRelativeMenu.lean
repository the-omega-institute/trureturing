/- GID: D5/S3/Quantum/Measurement/MeasurementRelativeMenu
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/MeasurementRelativeMenu
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Input-independent measurable control and the actual-menu channel error. -/

import D5.S3.Quantum.Measurement.FirstReadReduction
import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Data.List.OfFn

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder NNReal ENNReal

namespace D5.S3.Quantum.Measurement.MeasurementRelativeMenu

open D5.S3.Quantum.Measurement.ActualModeProtocol
open D5.S3.Quantum.Measurement.FirstReadReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.TotalVariation.Metric

/-- The common measurable space of actually selected waits, read outcomes and Stop. -/
abbrev Record := List (ℝ≥0 ⊕ Option Mode)

local instance : MeasurableSpace (Option Mode) := ⊤

local instance : MeasurableSingletonClass (Option Mode) := ⟨fun _ => trivial⟩

local instance : MeasurableSingletonClass (ℝ≥0 ⊕ Option Mode) where
  measurableSet_singleton x := by
    cases x with
    | inl t => simpa using (measurableSet_singleton t).inl_image (β := Option Mode)
    | inr s => simpa using (measurableSet_singleton s).inr_image (α := ℝ≥0)

local instance : MeasurableSingletonClass (Σ n, Fin n → (ℝ≥0 ⊕ Option Mode)) where
  measurableSet_singleton x := by
    rcases x with ⟨n, f⟩
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro m
    change MeasurableSet ((Sigma.mk (β := fun k : ℕ => Fin k → ℝ≥0 ⊕ Option Mode) m) ⁻¹' {⟨n, f⟩})
    by_cases h : m = n
    · subst m
      have he : (Sigma.mk (β := fun k : ℕ => Fin k → ℝ≥0 ⊕ Option Mode) n) ⁻¹'
          {⟨n, f⟩} = {f} := by
        ext g
        exact sigma_mk_injective.eq_iff
      rw [he]
      exact measurableSet_singleton f
    · have he : (Sigma.mk (β := fun k : ℕ => Fin k → ℝ≥0 ⊕ Option Mode) m) ⁻¹' {⟨n, f⟩} = ∅ := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hg
        exact h (congrArg Sigma.fst hg)
      rw [he]
      exact MeasurableSet.empty

/-- Finite records carry the disjoint-union measurable structure of their
length-indexed tuples, with Borel waiting times and discrete read/Stop labels. -/
instance recordMeasurableSpace : MeasurableSpace Record :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

instance recordMeasurableSingleton : MeasurableSingletonClass Record where
  measurableSet_singleton x := by
    have h : Measurable (List.equivSigmaTuple : Record → Σ n, Fin n → (ℝ≥0 ⊕ Option Mode)) :=
      measurable_iff_comap_le.mpr le_rfl
    have he : List.equivSigmaTuple ⁻¹' {List.equivSigmaTuple x} = {x} := by
      ext y
      exact List.equivSigmaTuple.injective.eq_iff
    rw [← he]
    exact (measurableSet_singleton (List.equivSigmaTuple x)).preimage h

/-- The specified Hamiltonian together with its Hermitian certificate. -/
def actualGenerator : {K : Matrix Mode Mode ℂ // K.IsHermitian} :=
  ⟨generator, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [generator, Matrix.conjTranspose_apply]⟩

/-- A finite-depth strategy driven by an input-independent classical resource.
The resource can have arbitrary measurable support. The same seed law and
policy are used for both inputs; the law field asserts measurability only,
not normalization, factorization, or a total-variation bound. -/
structure RandomizedProtocol where
  Seed : Type
  measurableSeed : MeasurableSpace Seed
  seedLaw : @Measure Seed measurableSeed
  probability : @IsProbabilityMeasure Seed measurableSeed seedLaw
  depth : ℕ
  policy : Seed → Protocol Mode depth
  measurable_law : ∀ ρ : DensityState Mode,
    @Measurable Seed (Measure Record) measurableSeed inferInstance
      (fun ω => (recordLaw actualGenerator.1 actualGenerator.2 (policy ω) ρ).toMeasure)

/-- The retained history measure includes the actual controls but does not expose
unread classical randomness or a hidden Kraus label. -/
def historyMeasure (π : RandomizedProtocol) (ρ : DensityState Mode) : Measure Record :=
  @Measure.bind π.Seed Record π.measurableSeed inferInstance π.seedLaw
    (fun ω => (recordLaw actualGenerator.1 actualGenerator.2 (π.policy ω) ρ).toMeasure)

/-- The two suprema of the measurement-relative error: first over canonical
density inputs, then over all finite-depth measurable randomized strategies.
Only the initial input is replaced; the strategy receives no channel flag. -/
def channelError (T : QuantumChannel Mode Mode) : ℝ≥0∞ :=
  ⨆ ρ : DensityState Mode, ⨆ π : RandomizedProtocol,
    measurableTotalVariation (historyMeasure π ρ) (historyMeasure π (T.mapState ρ))

/-- One actual first-read effect; this does not add a control to the menu. -/
def firstEffect (t : ℝ≥0) (s : Mode) : Matrix Mode Mode ℂ :=
  let U := VisibleAdaptiveRecordLaw.actualWait actualGenerator.1 t
  Uᴴ * projector s * U

/-- Events are classical postprocessing of the full five-result read. -/
def eventEffect (t : ℝ≥0) (J : Finset Mode) : Matrix Mode Mode ℂ :=
  ∑ s ∈ J, firstEffect t s

/-- The deterministic specialization of the same double-supremum error. -/
def deterministicChannelError (T : QuantumChannel Mode Mode) : ℝ≥0∞ :=
  ⨆ ρ : DensityState Mode, deterministicDistance actualGenerator.1 ρ (T.mapState ρ)

private theorem record_injective {n : ℕ} (π : Protocol Mode n) :
    Function.Injective π.record := by
  induction π with
  | stop =>
      change Function.Injective (fun _ : Unit => [Sum.inr (none : Option Mode)])
      exact fun _ _ _ => Subsingleton.elim _ _
  | wait t next ih =>
      intro x y h
      exact ih (List.cons.inj h).2
  | read next ih =>
      rintro ⟨s, x⟩ ⟨t, y⟩ h
      have hs : s = t := Option.some.inj (Sum.inr.inj (List.cons.inj h).1)
      subst t
      exact congrArg (Sigma.mk s) (ih s (List.cons.inj h).2)

open Classical in
private theorem recordLaw_apply {n : ℕ} (π : Protocol Mode n) (ρ : DensityState Mode)
    (E : Set Record) (hE : MeasurableSet E) :
    (recordLaw actualGenerator.1 actualGenerator.2 π ρ).toMeasure E =
      ENNReal.ofReal (∑ h ∈ Finset.univ.filter (fun h => π.record h ∈ E),
        historyWeight actualGenerator.1 π (CStarMatrix.ofMatrix.symm ρ.1) h) := by
  classical
  letI : MeasurableSpace π.History := ⊤
  have hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  rw [recordLaw, PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hE,
    PMF.toMeasure_apply_fintype]
  simp only [historyLaw, PMF.ofFintype_apply, Set.indicator_apply, Set.mem_preimage,
    Finset.sum_filter]
  symm
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp
  · intro h _
    split_ifs
    · exact historyWeight_nonnegative _ _ _ hρ _
    · rfl

private theorem max_gap_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (ENNReal.ofReal a - ENNReal.ofReal b) (ENNReal.ofReal b - ENNReal.ofReal a) =
      ENNReal.ofReal |a - b| := by
  rw [← ENNReal.ofReal_sub _ hb, ← ENNReal.ofReal_sub _ ha, ← ENNReal.ofReal_max]
  congr 1
  rw [abs_eq_max_neg, neg_sub]

/-- Passing from a tree's finite leaf law to its complete measurable record
loses no total variation, because the record keeps every read and Stop. -/
theorem recordLaw_totalVariation {n : ℕ} (π : Protocol Mode n) (ρ σ : DensityState Mode) :
    measurableTotalVariation
      (recordLaw actualGenerator.1 actualGenerator.2 π ρ).toMeasure
      (recordLaw actualGenerator.1 actualGenerator.2 π σ).toMeasure =
    ENNReal.ofReal (historyTV actualGenerator.1 π
      (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1)) := by
  classical
  let p := historyWeight actualGenerator.1 π (CStarMatrix.ofMatrix.symm ρ.1)
  let q := historyWeight actualGenerator.1 π (CStarMatrix.ofMatrix.symm σ.1)
  have hp : ∀ h, 0 ≤ p h := fun h => historyWeight_nonnegative _ _ _
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)) h
  have hq : ∀ h, 0 ≤ q h := fun h => historyWeight_nonnegative _ _ _
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)) h
  have hm : ∑ h, p h = ∑ h, q h := by
    dsimp [p, q]
    rw [historyWeight_mass _ actualGenerator.2, historyWeight_mass _ actualGenerator.2]
    change (Matrix.trace ρ.1).re = (Matrix.trace σ.1).re
    rw [ρ.2.2, σ.2.2]
  have he := total_variation_eq_sup_event_gap p q hm
  have hgap (E : Set Record) (hE : MeasurableSet E) :
      max ((recordLaw actualGenerator.1 actualGenerator.2 π ρ).toMeasure E -
          (recordLaw actualGenerator.1 actualGenerator.2 π σ).toMeasure E)
        ((recordLaw actualGenerator.1 actualGenerator.2 π σ).toMeasure E -
          (recordLaw actualGenerator.1 actualGenerator.2 π ρ).toMeasure E) =
      ENNReal.ofReal |(∑ h ∈ Finset.univ.filter (fun h => π.record h ∈ E), p h) -
        ∑ h ∈ Finset.univ.filter (fun h => π.record h ∈ E), q h| := by
    rw [recordLaw_apply π ρ E hE, recordLaw_apply π σ E hE]
    exact max_gap_ofReal (Finset.sum_nonneg fun h _ => hp h)
      (Finset.sum_nonneg fun h _ => hq h)
  apply le_antisymm
  · refine iSup_le fun E => ?_
    rw [hgap E.1 E.2]
    exact ENNReal.ofReal_le_ofReal (he.2 ⟨_, rfl⟩)
  · obtain ⟨A, hA⟩ := he.1
    let E : Set Record := π.record '' (A : Set π.History)
    have hE : MeasurableSet E := (A.finite_toSet.image π.record).measurableSet
    have hf : Finset.univ.filter (fun h => π.record h ∈ E) = A := by
      ext h
      simp [E, (record_injective π).mem_set_image]
    refine le_iSup_of_le (⟨E, hE⟩ : {E : Set Record // MeasurableSet E}) ?_
    rw [hgap E hE, hf]
    exact ENNReal.ofReal_le_ofReal hA.symm.le

/-- Every seed-driven history measure is a probability measure. Normalization
is derived from the actual branch recursion, not assumed of the output law. -/
theorem historyMeasure_probability (π : RandomizedProtocol) (ρ : DensityState Mode) :
    IsProbabilityMeasure (historyMeasure π ρ) := by
  letI := π.measurableSeed
  letI := π.probability
  constructor
  rw [historyMeasure, Measure.bind_apply MeasurableSet.univ (π.measurable_law ρ).aemeasurable]
  simp

private theorem historyMeasure_bound (π : RandomizedProtocol) (ρ σ : DensityState Mode) :
    measurableTotalVariation (historyMeasure π ρ) (historyMeasure π σ) ≤
      deterministicDistance actualGenerator.1 ρ σ := by
  letI := π.measurableSeed
  letI := π.probability
  let f := fun ω => (recordLaw actualGenerator.1 actualGenerator.2 (π.policy ω) ρ).toMeasure
  let g := fun ω => (recordLaw actualGenerator.1 actualGenerator.2 (π.policy ω) σ).toMeasure
  let c := deterministicDistance actualGenerator.1 ρ σ
  have hfg (ω : π.Seed) : measurableTotalVariation (f ω) (g ω) ≤ c := by
    rw [recordLaw_totalVariation]
    exact le_iSup_of_le π.depth (le_iSup
      (fun p : Protocol Mode π.depth => ENNReal.ofReal (historyTV actualGenerator.1 p
        (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1))) (π.policy ω))
  have hd (E : Set Record) (hE : MeasurableSet E) :
      (∫⁻ ω, f ω E ∂π.seedLaw) - (∫⁻ ω, g ω E ∂π.seedLaw) ≤ c ∧
      (∫⁻ ω, g ω E ∂π.seedLaw) - (∫⁻ ω, f ω E ∂π.seedLaw) ≤ c := by
    have hf := (Measure.measurable_coe hE).comp (π.measurable_law ρ)
    have hg := (Measure.measurable_coe hE).comp (π.measurable_law σ)
    have hpoint (ω : π.Seed) :
        max (f ω E - g ω E) (g ω E - f ω E) ≤ c :=
      (le_iSup (fun E : {E : Set Record // MeasurableSet E} =>
        max (f ω E.1 - g ω E.1) (g ω E.1 - f ω E.1)) ⟨E, hE⟩).trans (hfg ω)
    constructor
    · refine (lintegral_sub_le _ _ hg).trans ?_
      calc (∫⁻ ω, f ω E - g ω E ∂π.seedLaw) ≤ ∫⁻ _ω : π.Seed, c ∂π.seedLaw :=
            lintegral_mono fun ω => (le_max_left _ _).trans (hpoint ω)
        _ = c := by simp
    · refine (lintegral_sub_le _ _ hf).trans ?_
      calc (∫⁻ ω, g ω E - f ω E ∂π.seedLaw) ≤ ∫⁻ _ω : π.Seed, c ∂π.seedLaw :=
            lintegral_mono fun ω => (le_max_right _ _).trans (hpoint ω)
        _ = c := by simp
  refine iSup_le fun E => ?_
  rw [historyMeasure, historyMeasure,
    Measure.bind_apply E.2 (π.measurable_law ρ).aemeasurable,
    Measure.bind_apply E.2 (π.measurable_law σ).aemeasurable]
  exact max_le (hd E.1 E.2).1 (hd E.1 E.2).2

/-- A deterministic finite tree is an actual randomized strategy with a constant
unit seed; it introduces no extra control or input-dependent side information. -/
def deterministicProtocol {n : ℕ} (π : Protocol Mode n) : RandomizedProtocol where
  Seed := Unit
  measurableSeed := inferInstance
  seedLaw := Measure.dirac ()
  probability := inferInstance
  depth := n
  policy := fun _ => π
  measurable_law := fun _ => measurable_const

/-- The first-read identity includes arbitrary measurable input-independent
random control and every finite adaptive depth. -/
theorem randomized_distance_eq_first_read (ρ σ : DensityState Mode) :
    (⨆ π : RandomizedProtocol, measurableTotalVariation
      (historyMeasure π ρ) (historyMeasure π σ)) =
    ⨆ t : ℝ≥0, ENNReal.ofReal (firstReadTV actualGenerator.1 t
      (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1)) := by
  rw [← deterministic_distance_eq_first_read _ actualGenerator.2]
  apply le_antisymm
  · exact iSup_le fun π => historyMeasure_bound π ρ σ
  · refine iSup_le fun n => iSup_le fun π => ?_
    refine le_iSup_of_le (deterministicProtocol π) ?_
    simp only [historyMeasure, deterministicProtocol, Measure.bind_const,
      measure_univ, one_smul]
    rw [recordLaw_totalVariation]

private theorem event_pairing (t : ℝ≥0) (J : Finset Mode) (X : Matrix Mode Mode ℂ) :
    (Matrix.trace (eventEffect t J * X)).re =
      ∑ s ∈ J, firstReadProbability actualGenerator.1 t X s := by
  have hsingle (s : Mode) : Matrix.trace (firstEffect t s * X) =
      waitState actualGenerator.1 t X s s := by
    let U := VisibleAdaptiveRecordLaw.actualWait actualGenerator.1 t
    change Matrix.trace ((Uᴴ * projector s * U) * X) = (U * X * Uᴴ) s s
    calc
      Matrix.trace ((Uᴴ * projector s * U) * X) =
          Matrix.trace ((projector s * U * X) * Uᴴ) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (projector s * (U * X * Uᴴ)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp [projector, Matrix.trace_single_mul]
  simp only [eventEffect, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum,
    hsingle, firstReadProbability]

private theorem firstReadTV_event (t : ℝ≥0) (ρ σ : DensityState Mode) :
    IsGreatest (Set.range fun J : Finset Mode =>
      |(Matrix.trace (eventEffect t J * (CStarMatrix.ofMatrix.symm ρ.1 -
        CStarMatrix.ofMatrix.symm σ.1))).re|)
      (firstReadTV actualGenerator.1 t (CStarMatrix.ofMatrix.symm ρ.1)
        (CStarMatrix.ofMatrix.symm σ.1)) := by
  have hm : (∑ s, firstReadProbability actualGenerator.1 t
      (CStarMatrix.ofMatrix.symm ρ.1) s) =
      ∑ s, firstReadProbability actualGenerator.1 t (CStarMatrix.ofMatrix.symm σ.1) s := by
    simp only [firstReadProbability, ← Complex.re_sum]
    change (Matrix.trace (waitState actualGenerator.1 t
      (CStarMatrix.ofMatrix.symm ρ.1))).re =
      (Matrix.trace (waitState actualGenerator.1 t (CStarMatrix.ofMatrix.symm σ.1))).re
    rw [waitState_trace _ actualGenerator.2, waitState_trace _ actualGenerator.2]
    change (Matrix.trace ρ.1).re = (Matrix.trace σ.1).re
    rw [ρ.2.2, σ.2.2]
  have he := total_variation_eq_sup_event_gap
    (firstReadProbability actualGenerator.1 t (CStarMatrix.ofMatrix.symm ρ.1))
    (firstReadProbability actualGenerator.1 t (CStarMatrix.ofMatrix.symm σ.1)) hm
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, event_pairing,
    firstReadTV] using he

private theorem channelError_le_one (T : QuantumChannel Mode Mode) : channelError T ≤ 1 := by
  refine iSup_le fun ρ => iSup_le fun π => iSup_le fun E => ?_
  letI := historyMeasure_probability π ρ
  letI := historyMeasure_probability π (T.mapState ρ)
  exact max_le ((tsub_le_self).trans prob_le_one)
    ((tsub_le_self).trans prob_le_one)

/-- The actual-menu channel error is bounded by one and is exactly the
supremum of absolute first-read event expectations. Events remain classical
postprocessing of the complete rank-one read, rather than new instruments. -/
theorem channel_error_eq_event_expectation (T : QuantumChannel Mode Mode) :
    channelError T ≤ 1 ∧ channelError T =
      ⨆ t : ℝ≥0, ⨆ J : Finset Mode, ⨆ ρ : DensityState Mode,
        ENNReal.ofReal |(Matrix.trace (eventEffect t J *
          (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm (T.mapState ρ).1))).re| := by
  refine ⟨channelError_le_one T, ?_⟩
  unfold channelError
  simp_rw [randomized_distance_eq_first_read]
  rw [iSup_comm]
  apply iSup_congr
  intro t
  rw [iSup_comm]
  apply iSup_congr
  intro ρ
  have he := firstReadTV_event t ρ (T.mapState ρ)
  apply le_antisymm
  · obtain ⟨J, hJ⟩ := he.1
    exact le_iSup_of_le J (ENNReal.ofReal_le_ofReal hJ.symm.le)
  · exact iSup_le fun J => ENNReal.ofReal_le_ofReal (he.2 ⟨J, rfl⟩)

#print axioms randomized_distance_eq_first_read
#print axioms channel_error_eq_event_expectation

end D5.S3.Quantum.Measurement.MeasurementRelativeMenu
