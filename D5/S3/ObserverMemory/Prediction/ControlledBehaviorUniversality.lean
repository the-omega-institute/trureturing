/- GID: D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite controlled realization maps uniquely onto the complete behavior quotient. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib and Loogle hit `Setoid.quotientKerEquivRange`
     identifies the behavior-kernel quotient with the realized behavior range;
     it is imported and applied in `completionRangeEquiv` below.
   * Exact pinned-Mathlib and Loogle hit `Fintype.card_le_of_surjective`
     gives the final completed-state cardinality bound and is applied below.
   * LeanSearch's shaped quotient-factorization query returned HTTP 404.
   * Repository and pinned-Mathlib searches found no equal or stronger theorem
     packaging the controlled factor, all transition equations, readout equation,
     uniqueness, surjectivity, and cardinality bound. -/

namespace D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Apply an input word from left to right to a controlled state. -/
def runWord {U Y : Type*} (update : U -> Y -> Y) : List U -> Y -> Y
  | [], y => y
  | u :: word, y => runWord update word (update u y)

/-- The readout after every finite input word. -/
def controlledBehavior {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) (y : Y) : List U -> O :=
  fun word => readout (runWord update word y)

/-- States modulo equality of every finite-word readout. -/
abbrev ControlledCompletion {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) :=
  Quotient (Setoid.ker (controlledBehavior update readout))

/-- The canonical projection onto complete controlled behaviors. -/
def completionProjection {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) :
    Y -> ControlledCompletion update readout :=
  Quotient.mk _

/-- A finite controlled carrier has a finite complete behavior quotient. -/
noncomputable instance controlledCompletionFintype {U Y O : Type*}
    [Fintype Y] (update : U -> Y -> Y) (readout : Y -> O) :
    Fintype (ControlledCompletion update readout) := by
  classical
  exact Fintype.ofSurjective (completionProjection update readout)
    Quotient.mk_surjective

/-- The complete behavior quotient is equivalent to the realized behavior
range. -/
noncomputable def completionRangeEquiv {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) :
    ControlledCompletion update readout ≃
      Set.range (controlledBehavior update readout) :=
  Setoid.quotientKerEquivRange (controlledBehavior update readout)

/-- The transition induced on complete controlled behaviors. -/
def completionUpdate {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) (u : U) :
    ControlledCompletion update readout ->
      ControlledCompletion update readout :=
  Quotient.map (update u) (by
    intro y y' h
    funext word
    simpa [controlledBehavior, runWord] using congrFun h (u :: word))

/-- The current readout induced on complete controlled behaviors. -/
def completionReadout {U Y O : Type*}
    (update : U -> Y -> Y) (readout : Y -> O) :
    ControlledCompletion update readout -> O :=
  Quotient.lift readout (by
    intro y y' h
    simpa [controlledBehavior, runWord] using congrFun h [])

private theorem run_word_intertwines {U Y W : Type*}
    (update : U -> Y -> Y) (realizedUpdate : U -> W -> W)
    (realization : Y -> W)
    (updates_commute : forall u,
      realization ∘ update u = realizedUpdate u ∘ realization) :
    forall word y,
      realization (runWord update word y) =
        runWord realizedUpdate word (realization y) := by
  intro word
  induction word with
  | nil => intro y; rfl
  | cons u word ih =>
      intro y
      simp only [runWord]
      exact (ih (update u y)).trans
        (congrArg (runWord realizedUpdate word)
          (congrFun (updates_commute u) y))

/-- Every finite controlled realization factors uniquely and surjectively
through the complete behavior quotient. The factor intertwines every input
transition and the readout, and its surjectivity gives minimal cardinality. -/
theorem controlled_behavior_universal_property
    {Y U O W : Type*} [Fintype Y] [Fintype W]
    (update : U -> Y -> Y) (readout : Y -> O)
    (realization : Y -> W) (realizedUpdate : U -> W -> W)
    (realizedReadout : W -> O)
    (realization_surjective : Function.Surjective realization)
    (updates_commute : forall u,
      realization ∘ update u = realizedUpdate u ∘ realization)
    (readouts_commute : readout = realizedReadout ∘ realization) :
    (ExistsUnique fun factor : W -> ControlledCompletion update readout =>
      Function.Surjective factor /\
        completionProjection update readout = factor ∘ realization /\
        (forall u, factor ∘ realizedUpdate u =
          completionUpdate update readout u ∘ factor) /\
        completionReadout update readout ∘ factor = realizedReadout) /\
      Fintype.card (ControlledCompletion update readout) <= Fintype.card W := by
  classical
  have behavior_constant_on_fibers : forall {y y' : Y},
      realization y = realization y' ->
        controlledBehavior update readout y =
          controlledBehavior update readout y' := by
    intro y y' hyy'
    funext word
    calc
      readout (runWord update word y) =
          realizedReadout (realization (runWord update word y)) := by
        simpa only [Function.comp_apply] using
          congrFun readouts_commute (runWord update word y)
      _ = realizedReadout (runWord realizedUpdate word (realization y)) :=
        congrArg realizedReadout
          (run_word_intertwines update realizedUpdate realization
            updates_commute word y)
      _ = realizedReadout (runWord realizedUpdate word (realization y')) := by
        rw [hyy']
      _ = realizedReadout (realization (runWord update word y')) :=
        congrArg realizedReadout
          (run_word_intertwines update realizedUpdate realization
            updates_commute word y').symm
      _ = readout (runWord update word y') := by
        simpa only [Function.comp_apply] using
          (congrFun readouts_commute (runWord update word y')).symm
  let preimage : W -> Y :=
    Classical.choose realization_surjective.hasRightInverse
  have preimage_right : Function.RightInverse preimage realization :=
    Classical.choose_spec realization_surjective.hasRightInverse
  let factor : W -> ControlledCompletion update readout :=
    fun w => completionProjection update readout (preimage w)
  have projection_factors :
      completionProjection update readout = factor ∘ realization := by
    funext y
    apply Quotient.sound
    exact behavior_constant_on_fibers (preimage_right (realization y)).symm
  have factor_surjective : Function.Surjective factor := by
    intro state
    rcases Quotient.mk_surjective state with ⟨y, rfl⟩
    exact ⟨realization y, (congrFun projection_factors y).symm⟩
  have factor_updates : forall u,
      factor ∘ realizedUpdate u =
        completionUpdate update readout u ∘ factor := by
    intro u
    funext w
    rcases realization_surjective w with ⟨y, rfl⟩
    calc
      factor (realizedUpdate u (realization y)) =
          factor (realization (update u y)) := by
        exact congrArg factor (congrFun (updates_commute u) y).symm
      _ = completionProjection update readout (update u y) :=
        (congrFun projection_factors (update u y)).symm
      _ = completionUpdate update readout u
          (completionProjection update readout y) := rfl
      _ = completionUpdate update readout u (factor (realization y)) :=
        congrArg (completionUpdate update readout u)
          (congrFun projection_factors y)
  have factor_readout :
      completionReadout update readout ∘ factor = realizedReadout := by
    funext w
    rcases realization_surjective w with ⟨y, rfl⟩
    calc
      completionReadout update readout (factor (realization y)) =
          completionReadout update readout
            (completionProjection update readout y) :=
        congrArg (completionReadout update readout)
          (congrFun projection_factors y).symm
      _ = readout y := rfl
      _ = realizedReadout (realization y) := by
        simpa only [Function.comp_apply] using congrFun readouts_commute y
  refine ⟨⟨factor,
    ⟨factor_surjective, projection_factors, factor_updates, factor_readout⟩,
    ?_⟩, Fintype.card_le_of_surjective factor factor_surjective⟩
  intro other hother
  funext w
  rcases realization_surjective w with ⟨y, rfl⟩
  calc
    other (realization y) = completionProjection update readout y :=
      (congrFun hother.2.1 y).symm
    _ = factor (realization y) := congrFun projection_factors y

/-- The hypotheses have a concrete finite inhabited model. -/
example :
    Function.Surjective (id : Unit -> Unit) /\
      (forall _ : Unit,
        (id : Unit -> Unit) ∘ (id : Unit -> Unit) =
          (id : Unit -> Unit) ∘ (id : Unit -> Unit)) /\
      (id : Unit -> Unit) =
        (id : Unit -> Unit) ∘ (id : Unit -> Unit) := by
  exact ⟨Function.surjective_id, fun _ => rfl, rfl⟩

/-- The controlled completion domain is concretely inhabited. -/
example : ControlledCompletion (fun _ : Unit => id) (id : Unit -> Unit) :=
  completionProjection (fun _ : Unit => id) (id : Unit -> Unit) ()

end D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
