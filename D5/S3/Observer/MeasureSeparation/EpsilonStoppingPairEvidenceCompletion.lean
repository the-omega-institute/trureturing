/- GID: D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define stopping and evidence; close classification under a named dichotomy. -/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Distributions.Uniform

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib searches for probability Hellinger distance and Kakutani
     dichotomy found only the unrelated Hellinger--Toeplitz and
     Riesz--Markov--Kakutani theorems; no product-measure dichotomy was found.
   * Repository inspection found the finite-real `bhattacharyya` and
     `hellingerSq`; the latter uses `H^2 = 2 * (1 - rho)` for normalized laws.
     They do not define affinity for arbitrary measures, so no second
     measure-level implementation is introduced here.
   * `CountableSingularPartition` was inspected. Its public theorem requires a
     probability law at every natural index, so it cannot directly reindex an
     arbitrary finite family. The same canonical Mathlib refinement theorem,
     `exists_subordinate_pairwise_disjoint`, is reused below for finite indices.
   * Exact Mathlib hits `PMF.tsum_coe`, `ENNReal.log_zero`,
     `ENNReal.tsum_const_eq_top_of_ne_zero`, and `Nat.find_eq_zero` discharge
     the stopping-time and degenerate-case audits.
   * Principle 250.1 is not a closed proposition: "still confusable" and the
     actual adaptive decision tree have no definitions in the source section.
     It remains programmatic rather than being replaced by a vacuous theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace D5.S3.Observer.MeasureSeparation.EpsilonStoppingPairEvidenceCompletion

universe u v w z

/-- The posterior probability of error under a MAP decision. The supremum
agrees with the maximum on every finite nonempty state type. -/
def posteriorError {State : Type u} (posterior : PMF State) : ENNReal :=
  1 - ⨆ state, posterior state

/-- The first natural time at which posterior error is at most `epsilon`.
`top` records that the threshold set is empty, rather than identifying the
empty infimum with time zero. -/
noncomputable def epsilonStoppingTime {State : Type u} (epsilon : ENNReal)
    (posterior : Nat → PMF State) : WithTop Nat := by
  classical
  exact if h : ∃ time, posteriorError (posterior time) ≤ epsilon then
      (Nat.find h : WithTop Nat)
    else
      ⊤

/-- An abstract affinity on arbitrary measures. Hellinger affinity is an
intended instance; this module does not construct its measure-level integral.
The repository's finite `bhattacharyya` is the corresponding discrete model. -/
def MeasureAffinity (Output : Type v) [MeasurableSpace Output] :=
  Measure Output → Measure Output → ENNReal

/-- Open-loop pair evidence in the repository convention
`H^2 = 2 * (1 - rho)`. The experiment sequence is fixed before outputs arrive. -/
def openLoopPairEvidence {State : Type u} {Experiment : Type v}
    {Output : Type w} [MeasurableSpace Output]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (experiment : Nat → Experiment) (x y : State) : ENNReal :=
  ∑' time,
    2 * (1 - affinity (kernel (experiment time) x) (kernel (experiment time) y))

/-- Every selected coordinate has mutually absolutely continuous local laws
for each distinct state pair. -/
def OpenLoopLocallyEquivalent {State : Type u} {Experiment : Type v}
    {Output : Type w} [MeasurableSpace Output]
    (kernel : Experiment → State → Measure Output)
    (experiment : Nat → Experiment) : Prop :=
  ∀ time x y, x ≠ y →
    kernel (experiment time) x ≪ kernel (experiment time) y ∧
      kernel (experiment time) y ≪ kernel (experiment time) x

/-- The explicit missing Kakutani bridge. It packages only the implication
from local equivalence and divergent abstract evidence to singular transcript
laws; no product-measure dichotomy is claimed or constructed in this module. -/
def OpenLoopEvidenceDichotomy {State : Type u} {Experiment : Type v}
    {Output : Type w} {Transcript : Type z}
    [MeasurableSpace Output] [MeasurableSpace Transcript]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (experiment : Nat → Experiment)
    (transcriptLaw : State → Measure Transcript) : Prop :=
  OpenLoopLocallyEquivalent kernel experiment →
    (∀ x y, x ≠ y → openLoopPairEvidence affinity kernel experiment x y = ⊤) →
      Pairwise fun x y ↦ transcriptLaw x ⟂ₘ transcriptLaw y

/-- A common zero-error classifier represented by measurable, pairwise
disjoint decision regions. A null remainder may be left unclassified. -/
def HasCommonZeroErrorClassifier {State : Type u} {Transcript : Type v}
    [MeasurableSpace Transcript] (transcriptLaw : State → Measure Transcript) : Prop :=
  ∃ decisionRegion : State → Set Transcript,
    (∀ x, MeasurableSet (decisionRegion x)) ∧
      Pairwise (Disjoint on decisionRegion) ∧
        ∀ x, transcriptLaw x (decisionRegion x)ᶜ = 0

/-- Extended nonnegative negative log. At zero affinity this is `top`; values
above one are truncated to zero, while intended normalized affinities lie in
the unit interval. -/
def negativeLogAffinity (rho : ENNReal) : ENNReal :=
  (-ENNReal.log rho).toENNReal

/-- The next-step conditional affinity chosen from the common history. -/
def conditionalAffinity {State : Type u} {Experiment : Type v}
    {Output : Type w} {History : Type z} [MeasurableSpace Output]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (policy : Nat → History → Experiment)
    (x y : State) (time : Nat) (history : History) : ENNReal :=
  affinity (kernel (policy time history) x) (kernel (policy time history) y)

/-- The predictable evidence accumulated before time `n` along the realized
common-history process. -/
def predictableEvidenceProcess {State : Type u} {Experiment : Type v}
    {Output : Type w} {History : Type z} [MeasurableSpace Output]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (policy : Nat → History → Experiment)
    (history : Nat → History) (x y : State) (n : Nat) : ENNReal :=
  ∑ time ∈ Finset.range n,
    negativeLogAffinity
      (conditionalAffinity affinity kernel policy x y time (history time))

/-- The stopping time is infinite exactly when no natural time reaches the
error threshold. This is the explicit empty-threshold-set behavior. -/
theorem epsilon_stopping_time_eq_top_iff {State : Type u} (epsilon : ENNReal)
    (posterior : Nat → PMF State) :
    epsilonStoppingTime epsilon posterior = ⊤ ↔
      ∀ time, ¬posteriorError (posterior time) ≤ epsilon := by
  classical
  simp [epsilonStoppingTime]

#print axioms epsilon_stopping_time_eq_top_iff

/-- Reaching the threshold at time zero makes the stopping time zero. -/
theorem epsilon_stopping_time_eq_zero_of_initial {State : Type u}
    (epsilon : ENNReal) (posterior : Nat → PMF State)
    (initial : posteriorError (posterior 0) ≤ epsilon) :
    epsilonStoppingTime epsilon posterior = 0 := by
  classical
  rw [epsilonStoppingTime, dif_pos ⟨0, initial⟩]
  exact congrArg (fun time : Nat ↦ (time : WithTop Nat))
    ((Nat.find_eq_zero _).2 initial)

#print axioms epsilon_stopping_time_eq_zero_of_initial

/-- Threshold one always stops immediately. -/
theorem epsilon_one_stops_immediately {State : Type u}
    (posterior : Nat → PMF State) :
    epsilonStoppingTime 1 posterior = 0 := by
  apply epsilon_stopping_time_eq_zero_of_initial
  exact tsub_le_self

#print axioms epsilon_one_stops_immediately

/-- Every posterior on the singleton state type has zero MAP error. -/
theorem posterior_error_singleton (posterior : PMF Unit) :
    posteriorError posterior = 0 := by
  have posterior_one : posterior () = 1 := by
    simpa using posterior.tsum_coe
  simp [posteriorError, posterior_one]

#print axioms posterior_error_singleton

/-- A singleton-state posterior process stops at time zero for every threshold. -/
theorem singleton_state_stops_immediately (epsilon : ENNReal)
    (posterior : Nat → PMF Unit) :
    epsilonStoppingTime epsilon posterior = 0 := by
  apply epsilon_stopping_time_eq_zero_of_initial
  simp [posterior_error_singleton]

#print axioms singleton_state_stops_immediately

/-- The empty state type admits no posterior probability mass function. -/
theorem empty_state_has_no_posterior : IsEmpty (PMF Empty) := by
  constructor
  intro posterior
  have impossible : (0 : ENNReal) = 1 := calc
    0 = ∑' state : Empty, posterior state := by simp
    _ = 1 := posterior.tsum_coe
  exact zero_ne_one impossible

#print axioms empty_state_has_no_posterior

/-- At zero threshold, the constant fair Boolean posterior never stops. -/
theorem zero_threshold_may_never_stop :
    epsilonStoppingTime 0 (fun _ : Nat ↦ PMF.uniformOfFintype Bool) = ⊤ := by
  rw [epsilon_stopping_time_eq_top_iff]
  intro time
  simp [posteriorError, PMF.uniformOfFintype_apply]

#print axioms zero_threshold_may_never_stop

/-- On a singleton state type there are no distinct pairs, so the divergent
pair-evidence condition is vacuous. -/
theorem singleton_pair_evidence_condition_vacuous
    {Experiment : Type v} {Output : Type w} [MeasurableSpace Output]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → Unit → Measure Output)
    (experiment : Nat → Experiment) :
    ∀ x y : Unit, x ≠ y →
      openLoopPairEvidence affinity kernel experiment x y = ⊤ := by
  intro x y different
  exact (different (Subsingleton.elim x y)).elim

#print axioms singleton_pair_evidence_condition_vacuous

/-- Finite pairwise singular laws have a common family of measurable,
pairwise disjoint conull decision regions. -/
theorem finite_pairwise_singular_common_zero_error_classifier
    {State : Type u} {Transcript : Type v} [Finite State]
    [MeasurableSpace Transcript] (transcriptLaw : State → Measure Transcript)
    (singular : Pairwise fun x y ↦ transcriptLaw x ⟂ₘ transcriptLaw y) :
    HasCommonZeroErrorClassifier transcriptLaw := by
  classical
  letI : Fintype State := Fintype.ofFinite State
  let separator : State → State → Set Transcript := fun x y ↦
    if h : x = y then univ else (singular h).nullSetᶜ
  let rawSupport : State → Set Transcript := fun x ↦ ⋂ y, separator x y
  let mixture : Measure Transcript := ∑ x, transcriptLaw x
  have separator_measurable (x y : State) : MeasurableSet (separator x y) := by
    by_cases h : x = y
    · simp [separator, h]
    · simp [separator, h, (singular h).measurableSet_nullSet]
  have separator_conull (x y : State) : transcriptLaw x (separator x y)ᶜ = 0 := by
    by_cases h : x = y
    · simp [separator, h]
    · rw [show separator x y = (singular h).nullSetᶜ by simp [separator, h],
        compl_compl]
      exact (singular h).measure_nullSet
  have separator_null (x y : State) (h : x ≠ y) :
      transcriptLaw y (separator x y) = 0 := by
    rw [show separator x y = (singular h).nullSetᶜ by simp [separator, h]]
    exact (singular h).measure_compl_nullSet
  have raw_measurable (x : State) : MeasurableSet (rawSupport x) := by
    exact MeasurableSet.iInter fun y ↦ separator_measurable x y
  have raw_conull (x : State) : transcriptLaw x (rawSupport x)ᶜ = 0 := by
    have each (y : State) : ∀ᵐ transcript ∂transcriptLaw x, transcript ∈ separator x y :=
      mem_ae_iff.mpr (separator_conull x y)
    have all :
        ∀ᵐ transcript ∂transcriptLaw x,
          ∀ y ∈ (Finset.univ : Finset State), transcript ∈ separator x y :=
      (Filter.eventually_all_finset Finset.univ).2 fun y _ ↦ each y
    apply mem_ae_iff.mp
    filter_upwards [all] with transcript htranscript
    simp only [rawSupport, mem_iInter]
    exact fun y ↦ htranscript y (Finset.mem_univ y)
  have raw_null (x y : State) (h : x ≠ y) :
      transcriptLaw y (rawSupport x) = 0 := by
    exact measure_mono_null (iInter_subset (fun z ↦ separator x z) y)
      (separator_null x y h)
  have law_absolutely_continuous (x : State) : transcriptLaw x ≪ mixture := by
    have law_le : transcriptLaw x ≤ ∑ y : State, transcriptLaw y :=
      Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ x)
    exact law_le.absolutelyContinuous
  have raw_ae_disjoint : Pairwise (AEDisjoint mixture on rawSupport) := by
    intro x y hxy
    change mixture (rawSupport x ∩ rawSupport y) = 0
    simp only [mixture, Measure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hzx : z = x
    · subst z
      exact measure_mono_null inter_subset_right (raw_null y x hxy.symm)
    · exact measure_mono_null inter_subset_left (raw_null x z (Ne.symm hzx))
  obtain ⟨support, _support_sub, raw_ae_support, support_measurable,
      support_disjoint⟩ :=
    exists_subordinate_pairwise_disjoint
      (fun x ↦ (raw_measurable x).nullMeasurableSet) raw_ae_disjoint
  refine ⟨support, support_measurable, support_disjoint, ?_⟩
  intro x
  have raw_full : ∀ᵐ transcript ∂transcriptLaw x, transcript ∈ rawSupport x :=
    mem_ae_iff.mpr (raw_conull x)
  have transferred := (law_absolutely_continuous x).ae_le (raw_ae_support x)
  have support_full : ∀ᵐ transcript ∂transcriptLaw x, transcript ∈ support x := by
    filter_upwards [raw_full, transferred] with transcript hraw htransfer
    exact htransfer.mp hraw
  exact mem_ae_iff.mp support_full

#print axioms finite_pairwise_singular_common_zero_error_classifier

/-- Open-loop finite-state completion, conditional on the explicitly named
Kakutani evidence-to-singularity bridge absent from pinned Mathlib. -/
theorem open_loop_finite_state_completion
    {State : Type u} {Experiment : Type v} {Output : Type w}
    {Transcript : Type z} [Finite State]
    [MeasurableSpace Output] [MeasurableSpace Transcript]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (experiment : Nat → Experiment)
    (transcriptLaw : State → Measure Transcript)
    (localEquivalent : OpenLoopLocallyEquivalent kernel experiment)
    (evidenceDiverges :
      ∀ x y, x ≠ y → openLoopPairEvidence affinity kernel experiment x y = ⊤)
    (hDichotomy :
      OpenLoopEvidenceDichotomy affinity kernel experiment transcriptLaw) :
    (Pairwise fun x y ↦ transcriptLaw x ⟂ₘ transcriptLaw y) ∧
      HasCommonZeroErrorClassifier transcriptLaw := by
  have singular := hDichotomy localEquivalent evidenceDiverges
  exact ⟨singular,
    finite_pairwise_singular_common_zero_error_classifier transcriptLaw singular⟩

#print axioms open_loop_finite_state_completion

/-- The explicit dichotomy premise is necessary for an abstract affinity:
constant zero affinity makes evidence diverge even when every local and global
law is the same Dirac probability measure. -/
theorem evidence_dichotomy_is_necessary :
    ∃ (affinity : MeasureAffinity Unit)
      (kernel : Unit → Bool → Measure Unit)
      (experiment : Nat → Unit)
      (transcriptLaw : Bool → Measure Unit),
      OpenLoopLocallyEquivalent kernel experiment ∧
        (∀ x y, x ≠ y →
          openLoopPairEvidence affinity kernel experiment x y = ⊤) ∧
        ¬Pairwise fun x y ↦ transcriptLaw x ⟂ₘ transcriptLaw y := by
  let affinity : MeasureAffinity Unit := fun _ _ ↦ 0
  let kernel : Unit → Bool → Measure Unit := fun _ _ ↦ Measure.dirac ()
  let experiment : Nat → Unit := fun _ ↦ ()
  let transcriptLaw : Bool → Measure Unit := fun _ ↦ Measure.dirac ()
  refine ⟨affinity, kernel, experiment, transcriptLaw, ?_, ?_, ?_⟩
  · intro time x y different
    exact ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
  · intro x y different
    simp only [openLoopPairEvidence, affinity, tsub_zero, mul_one]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
  · intro pairwiseSingular
    have selfSingular := pairwiseSingular Bool.false_ne_true
    change (Measure.dirac () : Measure Unit) ⟂ₘ Measure.dirac () at selfSingular
    rw [Measure.MutuallySingular.self_iff] at selfSingular
    exact Measure.dirac_ne_zero selfSingular

#print axioms evidence_dichotomy_is_necessary

/-- Zero affinity contributes infinite negative-log evidence. -/
theorem negative_log_affinity_zero : negativeLogAffinity 0 = ⊤ := by
  simp [negativeLogAffinity]

#print axioms negative_log_affinity_zero

/-- The predictable evidence process starts at zero. -/
theorem predictable_evidence_zero
    {State : Type u} {Experiment : Type v} {Output : Type w}
    {History : Type z} [MeasurableSpace Output]
    (affinity : MeasureAffinity Output)
    (kernel : Experiment → State → Measure Output)
    (policy : Nat → History → Experiment)
    (history : Nat → History) (x y : State) :
    predictableEvidenceProcess affinity kernel policy history x y 0 = 0 := by
  simp [predictableEvidenceProcess]

#print axioms predictable_evidence_zero

end D5.S3.Observer.MeasureSeparation.EpsilonStoppingPairEvidenceCompletion
