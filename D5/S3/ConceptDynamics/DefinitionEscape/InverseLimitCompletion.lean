/- GID: D5/S3/ConceptDynamics/DefinitionEscape/InverseLimitCompletion
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A compatible refinement tower identifies states with its inverse-limit threads exactly under separation and completeness. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-23):
   * Existing observer-completion modules construct specialized trajectory and
     prediction quotients.
   * The DECT theory volume describes stable objects as inverse-limit threads, but
     repository search found no general heterogeneous refinement-system carrier,
     no canonical state-to-thread map, and no exact separation/completeness
     criterion for that map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.DefinitionEscape.InverseLimitCompletion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A refinement system is a sequence of readouts with restriction maps from each
finer coordinate level to the preceding coarser level. -/
structure RefinementSystem (X : Type u) where
  Coordinate : Nat → Type v
  readout : (level : Nat) → Concept X (Coordinate level)
  restrict : (level : Nat) → Coordinate (level + 1) → Coordinate level
  compatible : ∀ level state,
    restrict level (readout (level + 1) state) = readout level state

/-- An inverse-limit thread is a coordinate at every level satisfying all
restriction equations. -/
structure InverseThread {X : Type u} (system : RefinementSystem X) where
  value : (level : Nat) → system.Coordinate level
  compatible : ∀ level,
    system.restrict level (value (level + 1)) = value level

/-- Every state determines a canonical compatible thread of all its finite
readouts. -/
def stateThread {X : Type u} (system : RefinementSystem X) :
    X → InverseThread system :=
  fun state =>
    { value := fun level => system.readout level state
      compatible := fun level => system.compatible level state }

@[simp] theorem stateThread_value
    {X : Type u} (system : RefinementSystem X)
    (state : X) (level : Nat) :
    (stateThread system state).value level = system.readout level state := by
  rfl

/-- The tower separates states when agreement at every finite stage forces state
equality. -/
def SeparatesStates {X : Type u} (system : RefinementSystem X) : Prop :=
  ∀ ⦃left right : X⦄,
    (∀ level, system.readout level left = system.readout level right) →
      left = right

/-- The tower is thread-complete when every compatible inverse-limit thread is
realized by a state. -/
def ThreadComplete {X : Type u} (system : RefinementSystem X) : Prop :=
  Function.Surjective (stateThread system)

/-- The canonical state-to-thread map is injective exactly when the finite stages
jointly separate states. -/
theorem stateThread_injective_iff_separates
    {X : Type u} (system : RefinementSystem X) :
    Function.Injective (stateThread system) ↔ SeparatesStates system := by
  constructor
  · intro injective left right stageEqual
    apply injective
    apply InverseThread.ext
    funext level
    exact stageEqual level
  · intro separates left right threadEqual
    apply separates
    intro level
    exact congrArg (fun thread => thread.value level) threadEqual

/-- The canonical state-to-thread map is bijective exactly when the tower is both
thread-complete and state-separating. -/
theorem stateThread_bijective_iff_complete_and_separates
    {X : Type u} (system : RefinementSystem X) :
    Function.Bijective (stateThread system) ↔
      ThreadComplete system ∧ SeparatesStates system := by
  constructor
  · rintro ⟨injective, surjective⟩
    exact ⟨surjective,
      (stateThread_injective_iff_separates system).1 injective⟩
  · rintro ⟨complete, separates⟩
    exact ⟨(stateThread_injective_iff_separates system).2 separates,
      complete⟩

/-- Under completeness and separation, the state space is canonically equivalent
to the inverse limit of its finite readout stages. -/
noncomputable def stateEquivInverseLimit
    {X : Type u} (system : RefinementSystem X)
    (complete : ThreadComplete system)
    (separates : SeparatesStates system) :
    X ≃ InverseThread system :=
  Equiv.ofBijective (stateThread system)
    ((stateThread_bijective_iff_complete_and_separates system).2
      ⟨complete, separates⟩)

/-- Any property of states that is constant on all-stage fibers descends through
the inverse-limit embedding whenever the tower separates states. -/
theorem all_stage_agreement_eq_of_separates
    {X : Type u} (system : RefinementSystem X)
    (separates : SeparatesStates system)
    {left right : X}
    (threadValuesEqual : ∀ level,
      (stateThread system left).value level =
        (stateThread system right).value level) :
    left = right := by
  apply separates
  exact threadValuesEqual

private def identitySystem : RefinementSystem Bool where
  Coordinate := fun _ => Bool
  readout := fun _ => id
  restrict := fun _ => id
  compatible := by
    intro level state
    rfl

example : SeparatesStates identitySystem := by
  intro left right stageEqual
  exact stageEqual 0

example : ThreadComplete identitySystem := by
  intro thread
  refine ⟨thread.value 0, ?_⟩
  apply InverseThread.ext
  funext level
  have valueAtLevel : thread.value level = thread.value 0 := by
    induction level with
    | zero => rfl
    | succ level inductionHypothesis =>
        have step : thread.value (level + 1) = thread.value level := by
          simpa [identitySystem] using thread.compatible level
        exact step.trans inductionHypothesis
  exact valueAtLevel.symm

#print axioms stateThread_injective_iff_separates
#print axioms stateThread_bijective_iff_complete_and_separates
#print axioms all_stage_agreement_eq_of_separates

end D5.S3.ConceptDynamics.DefinitionEscape.InverseLimitCompletion
