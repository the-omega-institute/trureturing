/- Transient semantically distinct and boundary checks. -/
import D5.S3.Topology.Measures.AtlasObservationCheck
import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

/-! Exact task applications; all declarations in this module are transient evidence. -/
set_option pp.universes true
noncomputable section
open Classical
open MeasureTheory Set
open scoped BigOperators
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open AtlasFiniteSignedCheck AtlasObservationCheck
namespace AtlasBoundaryCheck

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := by infer_instance
local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
local instance : BorelSpace Bool := ⟨by simp [borel_eq_top_of_discrete]⟩

def diagonalWeights (x : Bool × Bool) : ℝ := if x.1 = x.2 then 1/2 else 0
def oppositeWeights (x : Bool × Bool) : ℝ := if x.1 ≠ x.2 then 1/2 else 0

def diagonalLaw : ProbabilityMeasure (Bool × Bool) := lawOfMass
  ⟨diagonalWeights, by rintro ⟨a,b⟩; cases a <;> cases b <;> norm_num [diagonalWeights],
    by norm_num [diagonalWeights, Fintype.sum_prod_type]⟩
def oppositeLaw : ProbabilityMeasure (Bool × Bool) := lawOfMass
  ⟨oppositeWeights, by rintro ⟨a,b⟩; cases a <;> cases b <;> norm_num [oppositeWeights],
    by norm_num [oppositeWeights, Fintype.sum_prod_type]⟩

-- Two actual actions read the two correlated coordinates, from the same initial state.
def action (a : Bool) (x : Bool × Bool) : Bool × Bool :=
  if a then (x.2,x.2) else (x.1,x.1)
abbrev Words := {w : List Bool // w.length ≤ 1}
local instance : Fintype Words := (List.finite_length_le Bool 1).fintype
def response (x : Bool × Bool) (w : Words) : Bool := (runWord action w.val x).1
def wFirst : Words := ⟨[false], by decide⟩
def wSecond : Words := ⟨[true], by decide⟩

lemma diagonal_mass : massVector diagonalLaw = diagonalWeights := massVector_lawOfMass _
lemma opposite_mass : massVector oppositeLaw = oppositeWeights := massVector_lawOfMass _

-- Every bounded-word individual marginal agrees, including the empty word.
theorem same_all_individual_marginals (w : Words) :
    diagonalLaw.map (fun x => response x w) = oppositeLaw.map (fun x => response x w) := by
  apply massVector_injective
  rw [massVector_map, massVector_map, diagonal_mass, opposite_mass]
  funext b
  have hw := w.property
  rcases w with ⟨w,hw⟩
  cases w with
  | nil => cases b <;> norm_num [response, runWord,
      D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass,
      diagonalWeights, oppositeWeights, Fintype.sum_prod_type]
  | cons a w =>
    cases w with
    | cons a' w => simp at hw
    | nil => cases a <;> cases b <;> norm_num [response, runWord, action,
        D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass,
        diagonalWeights, oppositeWeights, Fintype.sum_prod_type]

lemma law_event (μ : ProbabilityMeasure (Bool × Bool)) (A : Set (Bool × Bool)) :
    (μ : Measure (Bool × Bool)).real A = ∑ x ∈ (Set.toFinite A).toFinset, massVector μ x := by
  simpa only [massVector, Set.Finite.coe_toFinset] using
    (sum_measureReal_singleton (μ := (μ : Measure (Bool × Bool))) (Set.toFinite A).toFinset).symm

-- The JOINT table detects perfect correlation versus perfect anticorrelation.
theorem joint_response_TV_one :
    totalVariation (massVector (diagonalLaw.map response))
      (massVector (oppositeLaw.map response)) = 1 := by
  classical
  let A : Finset (Words → Bool) := Finset.univ.filter (fun t => t wFirst = t wSecond)
  have pre : response ⁻¹' (A : Set (Words → Bool)) = {x : Bool × Bool | x.1 = x.2} := by
    ext x
    simp [A, response, wFirst, wSecond, runWord, action]
  have hm : Measurable response := measurable_of_countable response
  have hA : MeasurableSet (A : Set (Words → Bool)) := (Set.toFinite _).measurableSet
  have hd : (diagonalLaw.map response : Measure (Words → Bool)).real A = 1 := by
    rw [ProbabilityMeasure.toMeasure_map, map_measureReal_apply hm hA, pre, law_event, diagonal_mass]
    change (∑ x ∈ (Set.toFinite {x : Bool × Bool | x.1 = x.2}).toFinset, diagonalWeights x) = 1
    norm_num [Set.Finite.toFinset_ofPred, Finset.sum_filter, diagonalWeights, Fintype.sum_prod_type]
  have ha : (oppositeLaw.map response : Measure (Words → Bool)).real A = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, map_measureReal_apply hm hA, pre, law_event, opposite_mass]
    change (∑ x ∈ (Set.toFinite {x : Bool × Bool | x.1 = x.2}).toFinset, oppositeWeights x) = 0
    norm_num [Set.Finite.toFinset_ofPred, Finset.sum_filter, oppositeWeights, Fintype.sum_prod_type]
  apply le_antisymm
  · exact total_variation_le_one _ _ (massVector_mem_simplex _) (massVector_mem_simplex _)
  · have h := (actual_event_maximum (diagonalLaw.map response) (oppositeLaw.map response)).2
      (Set.mem_range_self A)
    simpa only [hd, ha, sub_zero, abs_one] using h

-- A concrete exact compact-factorization telescope for the correlated law test.
theorem exact_check_1 :
    let q : ℕ → (Bool × Bool) → (Bool × Bool) := fun _ => id
    let p : ℕ → (Bool × Bool) → (Bool × Bool) := fun _ => id
    ∃ N, ∃ g : (Bool × Bool) → (Words → Bool),
      (∀ x, g (q N x) = response x) ∧
      (diagonalLaw : Measure (Bool × Bool)).map response =
        ((diagonalLaw : Measure (Bool × Bool)).map (q N)).map g := by
  have basis : IsTopologicalBasis {U : Set (Bool × Bool) | ∃ n : ℕ, ∃ z : Bool × Bool,
      U = (id : (Bool × Bool) → (Bool × Bool)) ⁻¹' {z}} := by
    convert isTopologicalBasis_singletons (Bool × Bool) using 1
    ext U
    simp
  obtain ⟨N,g,hg,hlaw,_,_⟩ := whole_response_law
    (q := fun _ => id) (p := fun _ => id) (fun _ => continuous_id)
    (fun _ => Function.surjective_id) (fun _ _ => rfl) basis action
    (fun _ => continuous_of_discreteTopology) Prod.fst continuous_fst 1
  exact ⟨N,g,hg,hlaw _⟩

section History
open D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

def records : AppendOnlyOps (List Bool) Bool where
  append r b := r ++ [b]
  IsPrefix := List.IsPrefix
  prefix_append r b := List.prefix_append r [b]
def observer : RecordedObserver Unit (List Bool) Bool Bool records where
  q1 _ := true
  controlledUpdate _ := ()
  q2 r := r.isEmpty
abbrev Hist := ObserverHistory Unit (List Bool) Bool Bool records observer
def evolution := generatedHistoryEvolution records observer
def first : Hist := .initial ((), [])
def second : Hist := .next first false
local instance : MeasurableSpace Hist := ⊤
local instance : MeasurableSingletonClass Hist := by infer_instance

def firstLaw : ProbabilityMeasure Hist := ⟨Measure.dirac first, inferInstance⟩
def secondLaw : ProbabilityMeasure Hist := ⟨Measure.dirac second, inferInstance⟩

theorem generated_certificate :
    evolution.observe (evolution.advance first false) = step records observer (evolution.observe first) false ∧
    evolution.endpoint first = evolution.endpoint second ∧
    evolution.recordImage first ≠ evolution.recordImage second ∧
    ¬Setoid.ker (observer.q2 ∘ evolution.recordImage) first second := by
  refine ⟨evolution.observe_advance _ _, rfl, by decide, ?_⟩
  have h := state_record_readout_distinguishability (StateOutput := Unit)
    records observer evolution first second () [] [true] ⟨rfl,rfl,rfl,rfl,by decide⟩
  exact h.2.mpr (by decide)

theorem generated_endpoint_record_laws :
    totalVariation (massVector (firstLaw.map evolution.endpoint))
      (massVector (secondLaw.map evolution.endpoint)) = 0 ∧
    totalVariation (massVector (firstLaw.map (observer.q2 ∘ evolution.recordImage)))
      (massVector (secondLaw.map (observer.q2 ∘ evolution.recordImage))) = 1 := by
  have hend : firstLaw.map evolution.endpoint = secondLaw.map evolution.endpoint := by
    apply Subtype.ext
    simp [firstLaw, secondLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_dirac]
    rfl
  constructor
  · rw [hend]; simp [totalVariation]
  · norm_num [totalVariation, massVector, measureReal_def, firstLaw, secondLaw,
      ProbabilityMeasure.toMeasure_map, Measure.map_dirac,
      evolution, generatedHistoryEvolution, HistoryEvolution.recordImage,
      finalState, ObserverHistory.fold, first, second, step, records, observer]

-- Unequal actual generated records still give TV0 under the allowed constant readout.
theorem nonseparating_output_boundary :
    evolution.recordImage first ≠ evolution.recordImage second ∧
    totalVariation (massVector (firstLaw.map ((fun _ : List Bool => true) ∘ evolution.recordImage)))
      (massVector (secondLaw.map ((fun _ : List Bool => true) ∘ evolution.recordImage))) = 0 := by
  refine ⟨generated_certificate.2.2.1, ?_⟩
  have h : firstLaw.map ((fun _ : List Bool => true) ∘ evolution.recordImage) = secondLaw.map ((fun _ : List Bool => true) ∘ evolution.recordImage) := by
    apply Subtype.ext
    simp [firstLaw, secondLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_dirac]
  rw [h]
  simp [totalVariation]
end History

section Circular
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

-- Exact application, with an arbitrary factored readout consumer.
theorem factored_untouched_readout {α Z : Type*} [DecidableEq α]
    {xs : List α} {C D : Cycle α} (h : DeleteWalk xs C D)
    (p : α → Bool) (untouched : ∀ x ∈ xs, p x = false) (readout : Cycle α → Z) :
    readout (restrict p C) = readout (restrict p D) :=
  congrArg readout (restrict_walk h p untouched)

theorem exact_check_2 {α : Type*} [DecidableEq α] {xs : List α} {C : Cycle α}
    (h : DeleteWalk xs C C.reverse) (hn : C.Nodup) :
    C.toFinset.card ≤ xs.toFinset.card + 2 := negative_walk_support_bound h hn

theorem exact_check_3 {α : Type*} [DecidableEq α] {A : Finset α} (hA : 4 ≤ A.card)
    {C D : Cycle α} (hC : C.Nodup) (hD : D.Nodup) (sC : C.toFinset = A) (sD : D.toFinset = A)
    (deck : ∀ x ∈ A, delete x C = delete x D) : C = D := reconstruct hA hC hD sC sD deck

theorem exact_check_4 : jointKernel (deletionReadout (Finset.univ : Finset (Fin 4))) =
    diagonal (SupportedCircle (Finset.univ : Finset (Fin 4))) :=
  (deletion_joint_kernel_iff _ (by decide)).mpr (by decide)

-- Actual rotation-quotient obstruction: private source theorem reused through its public consumer.
theorem three_label_joint_boundary :
    jointKernel (deletionReadout (Finset.univ : Finset (Fin 3))) ≠
      diagonal (SupportedCircle (Finset.univ : Finset (Fin 3))) := by
  intro h
  have hf := (deletion_joint_kernel_iff (Finset.univ : Finset (Fin 3)) (by decide)).mp h
  norm_num at hf

-- One omitted label, one source, two genuinely different legal successors.
-- Thus the incidence relation is not already a deterministic update function.
theorem deletion_incidence_not_deterministic :
    let C : Cycle (Fin 3) := ([0,1,2] : List (Fin 3))
    let D : Cycle (Fin 3) := ([0,2,1] : List (Fin 3))
    C ≠ D ∧ DeleteWalk [0] C C ∧ DeleteWalk [0] C D := by
  dsimp only
  have hne : ([0,1,2] : Cycle (Fin 3)) ≠ ([0,2,1] : Cycle (Fin 3)) := by
    intro h
    have e := D5.S3.Combinatorics.CircularWords.CyclicInsertionGap.anchored_coe_injective
      (by decide : ([0,1,2] : List (Fin 3)).Nodup) h
    have : (1 : Fin 3) = 2 := (List.cons.inj e).1
    exact (by decide : (1 : Fin 3) ≠ 2) this
  refine ⟨hne, .cons rfl (.nil _), .cons ?_ (.nil _)⟩
  change (([1,2] : List (Fin 3)) : Cycle (Fin 3)) = ([2,1] : List (Fin 3))
  exact Cycle.coe_eq_coe.mpr ⟨1, by decide⟩
end Circular

#check @same_all_individual_marginals
#check @joint_response_TV_one
#check @generated_certificate
#check @generated_endpoint_record_laws
#check @nonseparating_output_boundary
#check @factored_untouched_readout
#check @three_label_joint_boundary
#check @deletion_incidence_not_deterministic
#print axioms same_all_individual_marginals
#print axioms joint_response_TV_one
#print axioms generated_certificate
#print axioms generated_endpoint_record_laws
#print axioms nonseparating_output_boundary
#print axioms factored_untouched_readout
#print axioms three_label_joint_boundary
#print axioms deletion_incidence_not_deterministic
#check @diagonalWeights
#print axioms diagonalWeights
#check @oppositeWeights
#print axioms oppositeWeights
#check @diagonalLaw
#print axioms diagonalLaw
#check @oppositeLaw
#print axioms oppositeLaw
#check @action
#print axioms action
#check @response
#print axioms response
#check @wFirst
#print axioms wFirst
#check @wSecond
#print axioms wSecond
#check @diagonal_mass
#print axioms diagonal_mass
#check @opposite_mass
#print axioms opposite_mass
#check @law_event
#print axioms law_event
#check @exact_check_1
#print axioms exact_check_1
#check @records
#print axioms records
#check @observer
#print axioms observer
#check @evolution
#print axioms evolution
#check @first
#print axioms first
#check @second
#print axioms second
#check @firstLaw
#print axioms firstLaw
#check @secondLaw
#print axioms secondLaw
#check @exact_check_2
#print axioms exact_check_2
#check @exact_check_3
#print axioms exact_check_3
#check @exact_check_4
#print axioms exact_check_4

#check @Words
#check @Hist

#print axioms Words
#print axioms Hist

end AtlasBoundaryCheck
