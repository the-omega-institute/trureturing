/- GID: D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expanding observations induce a quotient tower and stable compatible threads. -/

import D5.S3.ConceptDynamics.RefinementFactorization.InterventionFamilyKernelMonotonicity
import D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open, its `coverage_gids` and receipt lists are
     empty, and no formalization receipt exists. Its bound section-43 neighbor
     treats closure and reopening; the section-45 neighbor has no receipt.
   * The exact repository theorem `intervention_family_kernel_monotonicity`
     proves that enlarging an operation family shrinks its joint-readout kernel.
     The existing `RefinementSystem` and `InverseThread` package an abstract
     inverse system and its compatible threads, but assume the restriction maps;
     they are reused here after those maps are constructed from the quotients.
   * `RelativeIdentityRefinement` gives the universal property of one such
     quotient map. Pinned Mathlib's thinner exact primitive `Setoid.map_of_le`
     constructs the canonical map, and `monotone_nat_of_le_succ` extends the
     source's adjacent inclusions to arbitrary levels. Searches found no existing
     identity-and-composition package for this observation quotient tower.
   * Searches of the other pinned Lean packages found no matching construction.
     `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.StableObservationInverseLimit

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.RefinementFactorization.InterventionFamilyKernelMonotonicity
open D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion

universe uOperation uState uObservation

/-- An operation family expands when every stage is included in its successor. -/
def IsIncreasing {Operation : Type uOperation}
    (operationFamily : Nat -> Set Operation) : Prop :=
  forall level, operationFamily level <= operationFamily (level + 1)

/-- The joint readout supplied by all operations admitted at one level. -/
def operationReadout
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation) (level : Nat) :
    State -> (operation : operationFamily level) -> Observation :=
  jointReadout (fun operation : operationFamily level => observe operation.1)

/-- Operational equivalence at one level: all currently admitted observations agree. -/
abbrev operationSetoid
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation) (level : Nat) : Setoid State :=
  Setoid.ker (operationReadout operationFamily observe level)

/-- The stage object is the quotient by operational equivalence at that level. -/
abbrev ObservationStage
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation) (level : Nat) :=
  Quotient (operationSetoid operationFamily observe level)

/-- Adjacent inclusion makes the whole natural-number-indexed family monotone. -/
theorem operation_family_monotone
    {Operation : Type uOperation} (operationFamily : Nat -> Set Operation)
    (increasing : IsIncreasing operationFamily) : Monotone operationFamily := by
  exact monotone_nat_of_le_succ increasing

/-- Equality under every operation at a finer level implies equality at every
coarser level. This is the relation inclusion `sim_m <= sim_n` for `n <= m`. -/
theorem operation_setoid_antitone_le
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) {coarse fine : Nat}
    (levels : coarse <= fine) :
    operationSetoid operationFamily observe fine <=
      operationSetoid operationFamily observe coarse := by
  simpa only [operationSetoid, operationReadout] using
    intervention_family_kernel_monotonicity observe
      ((operation_family_monotone operationFamily increasing) levels)

/-- The canonical restriction from a finer observational quotient to a coarser one. -/
def restrictLE
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) {coarse fine : Nat}
    (levels : coarse <= fine) :
    ObservationStage operationFamily observe fine ->
      ObservationStage operationFamily observe coarse :=
  Setoid.map_of_le
    (operation_setoid_antitone_le operationFamily observe increasing levels)

/-- The source's adjacent restriction map `r_(n+1,n)`. -/
def restrictAdjacent
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) (level : Nat) :
    ObservationStage operationFamily observe (level + 1) ->
      ObservationStage operationFamily observe level :=
  restrictLE operationFamily observe increasing (Nat.le_succ level)

@[simp] theorem restrictLE_mk
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) {coarse fine : Nat}
    (levels : coarse <= fine) (state : State) :
    restrictLE operationFamily observe increasing levels
        (Quotient.mk'' state : ObservationStage operationFamily observe fine) =
      (Quotient.mk'' state : ObservationStage operationFamily observe coarse) := by
  rfl

@[simp] theorem restrictAdjacent_mk
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) (level : Nat) (state : State) :
    restrictAdjacent operationFamily observe increasing level
        (Quotient.mk'' state : ObservationStage operationFamily observe (level + 1)) =
      (Quotient.mk'' state : ObservationStage operationFamily observe level) := by
  rfl

/-- The adjacent restriction is independent of representatives because finer
operational equivalence is contained in coarser operational equivalence. -/
theorem restrictAdjacent_well_defined
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) (level : Nat)
    {left right : State}
    (equivalent : operationSetoid operationFamily observe (level + 1) left right) :
    restrictAdjacent operationFamily observe increasing level
        (Quotient.mk'' left : ObservationStage operationFamily observe (level + 1)) =
      restrictAdjacent operationFamily observe increasing level
        (Quotient.mk'' right : ObservationStage operationFamily observe (level + 1)) := by
  apply Quotient.sound
  exact operation_setoid_antitone_le operationFamily observe increasing
    (Nat.le_succ level) equivalent

/-- Restriction over a reflexive level inequality is the identity. -/
theorem restrictLE_refl
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) (level : Nat) :
    restrictLE operationFamily observe increasing (le_refl level) = id := by
  funext stage
  refine Quotient.inductionOn' stage ?_
  intro state
  rfl

/-- Restricting through an intermediate level equals direct restriction. -/
theorem restrictLE_trans
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily)
    {coarse middle fine : Nat} (first : coarse <= middle)
    (second : middle <= fine) :
    restrictLE operationFamily observe increasing (first.trans second) =
      restrictLE operationFamily observe increasing first ∘
        restrictLE operationFamily observe increasing second := by
  funext stage
  refine Quotient.inductionOn' stage ?_
  intro state
  rfl

/-- The quotient stages and their adjacent restrictions form a refinement system. -/
def observationRefinementSystem
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) : RefinementSystem State where
  Coordinate := ObservationStage operationFamily observe
  readout := fun _ state => Quotient.mk'' state
  restrict := restrictAdjacent operationFamily observe increasing
  compatible := by
    intro level state
    rfl

/-- Stable scientific objects are the compatible inverse-limit threads of the
observational quotient system. -/
abbrev StableObservationSpace
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) :=
  InverseThread (observationRefinementSystem operationFamily observe increasing)

/-- Expanding operation families yield decreasing operational equivalences,
well-defined quotient restrictions, functorial restriction along level order,
and a stable space whose elements satisfy every adjacent compatibility law. -/
theorem stable_observation_inverse_limit_laws
    {Operation : Type uOperation} {State : Type uState}
    {Observation : Type uObservation}
    (operationFamily : Nat -> Set Operation)
    (observe : Operation -> State -> Observation)
    (increasing : IsIncreasing operationFamily) :
    (forall level,
      operationSetoid operationFamily observe (level + 1) <=
        operationSetoid operationFamily observe level) /\
      (forall level (state : State),
        restrictAdjacent operationFamily observe increasing level
            (Quotient.mk'' state :
              ObservationStage operationFamily observe (level + 1)) =
          (Quotient.mk'' state : ObservationStage operationFamily observe level)) /\
      (forall level (left right : State),
        operationSetoid operationFamily observe (level + 1) left right ->
          restrictAdjacent operationFamily observe increasing level
              (Quotient.mk'' left :
                ObservationStage operationFamily observe (level + 1)) =
            restrictAdjacent operationFamily observe increasing level
              (Quotient.mk'' right :
                ObservationStage operationFamily observe (level + 1))) /\
      ((forall level,
          restrictLE operationFamily observe increasing (le_refl level) = id) /\
        forall {coarse middle fine : Nat}
          (first : coarse <= middle) (second : middle <= fine),
          restrictLE operationFamily observe increasing (first.trans second) =
            restrictLE operationFamily observe increasing first ∘
              restrictLE operationFamily observe increasing second) /\
      forall thread : StableObservationSpace operationFamily observe increasing,
        forall level,
          restrictAdjacent operationFamily observe increasing level
              (thread.value (level + 1)) =
            thread.value level := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro level
    exact operation_setoid_antitone_le operationFamily observe increasing
      (Nat.le_succ level)
  · exact restrictAdjacent_mk operationFamily observe increasing
  · intro level left right equivalent
    exact restrictAdjacent_well_defined operationFamily observe increasing
      level equivalent
  · exact restrictLE_refl operationFamily observe increasing
  · intro coarse middle fine first second
    exact restrictLE_trans operationFamily observe increasing first second
  · intro thread level
    exact thread.compatible level

/-- A concrete expanding family: no operation is admitted at level zero, while
the unique operation is admitted from level one onward. -/
def strictOperationFamily (level : Nat) : Set Unit :=
  {_operation | 1 <= level}

/-- The unique concrete operation reads a Boolean state exactly. -/
def strictObservation (_operation : Unit) (state : Bool) : Bool :=
  state

theorem strictOperationFamily_increasing : IsIncreasing strictOperationFamily := by
  intro level operation admitted
  change 1 <= level at admitted
  change 1 <= level + 1
  exact admitted.trans (Nat.le_succ level)

/-- The concrete operational equivalence chain strictly decreases from level
zero to level one: the empty family identifies the two Boolean states, while
the newly admitted identity observation separates them. -/
theorem strict_observation_refinement_witness :
    operationSetoid strictOperationFamily strictObservation 1 <
      operationSetoid strictOperationFamily strictObservation 0 := by
  refine lt_of_le_of_ne
    (operation_setoid_antitone_le strictOperationFamily strictObservation
      strictOperationFamily_increasing (Nat.zero_le 1)) ?_
  intro setoidsEqual
  have coarseEquivalent :
      operationSetoid strictOperationFamily strictObservation 0 false true := by
    change operationReadout strictOperationFamily strictObservation 0 false =
      operationReadout strictOperationFamily strictObservation 0 true
    funext operation
    have admitted : 1 <= 0 := by
      simpa only [strictOperationFamily, Set.mem_setOf_eq] using operation.property
    omega
  have fineEquivalent :
      operationSetoid strictOperationFamily strictObservation 1 false true := by
    rw [setoidsEqual]
    exact coarseEquivalent
  change operationReadout strictOperationFamily strictObservation 1 false =
    operationReadout strictOperationFamily strictObservation 1 true at fineEquivalent
  have separated := congrFun fineEquivalent
    (show strictOperationFamily 1 from ⟨(), by simp [strictOperationFamily]⟩)
  exact Bool.false_ne_true separated

#print axioms stable_observation_inverse_limit_laws
#print axioms strict_observation_refinement_witness

end D5.S3.ConceptDynamics.RefinementGeometry.StableObservationInverseLimit
