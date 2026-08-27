/- GID: D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-horizon prediction escape is exactly readout expansion escape. -/

import Mathlib.Data.Fintype.Basic

/- Library-search audit trail (2026-08-27):
   * Two D5 collision searches for `PredictionEscape`, `ExpansionEscape`,
     `TimeExpansionEscape`, `timeProjection`, `timeIter`, `TimeIndex`, and the
     planned declaration names found no repository definitions or theorem.
   * Pinned Mathlib supplies `Fintype.decidableExistsFintype` and
     `Function.ne_iff`, but no finite-horizon prediction-escape definition or
     theorem. The proof below uses the constructive finite decision procedure.
   * A third-party package search found no declarations with the source names. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape

universe u v w

/-- Iteration of a time transition, with the initial state at time zero. -/
def timeIter {X : Type u} (transition : X -> X) : Nat -> X -> X
  | 0, x => x
  | n + 1, x => transition (timeIter transition n x)

/-- The finite time domain from zero through `N`, inclusive. -/
abbrev TimeIndex (N : Nat) := Fin (N + 1)

/-- The readout along the finite orbit segment from time zero through `N`. -/
def timeProjection {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X) (N : Nat) :
    X -> TimeIndex N -> O :=
  fun x i => readout (timeIter transition i.1 x)

/-- Two states agree under an old readout and disagree under its expansion. -/
def ExpansionEscape
    {X : Type u} {OldReadout : Type v} {NewReadout : Type w}
    (oldReadout : X -> OldReadout) (newReadout : X -> NewReadout)
    (x y : X) : Prop :=
  oldReadout x = oldReadout y /\
    Not (newReadout x = newReadout y)

/-- Two states agree now but differ at some time no later than `N`. -/
def PredictionEscape {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X) (N : Nat)
    (x y : X) : Prop :=
  readout x = readout y /\
    exists k : Nat, k <= N /\
      Not (readout (timeIter transition k x) =
        readout (timeIter transition k y))

/-- The independently defined bounded-witness prediction escape is exactly
escape from the current readout to its finite-time projection. -/
theorem prediction_escape_iff_expansion_escape
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X) (N : Nat) (x y : X) :
    PredictionEscape readout transition N x y <->
      ExpansionEscape readout (timeProjection readout transition N) x y := by
  constructor
  · rintro ⟨hCurrent, k, hk, hDifferent⟩
    refine ⟨hCurrent, ?_⟩
    intro hProjection
    have hAtK := congrFun hProjection
      (⟨k, Nat.lt_succ_iff.mpr hk⟩ : TimeIndex N)
    exact hDifferent (by simpa [timeProjection] using hAtK)
  · rintro ⟨hCurrent, hProjection⟩
    refine ⟨hCurrent, ?_⟩
    let witnessDecision : Decidable
        (exists i : TimeIndex N,
          Not (timeProjection readout transition N x i =
            timeProjection readout transition N y i)) :=
      Fintype.decidableExistsFintype
    cases witnessDecision with
    | isTrue hWitness =>
        obtain ⟨i, hi⟩ := hWitness
        exact ⟨i.1, Nat.le_of_lt_succ i.2,
          by simpa [timeProjection] using hi⟩
    | isFalse hNoWitness =>
        exfalso
        apply hProjection
        funext i
        by_cases hi :
            timeProjection readout transition N x i =
              timeProjection readout transition N y i
        · exact hi
        · exact (hNoWitness ⟨i, hi⟩).elim

/-- A checked inhabited instance in which equal current readouts separate after
one transition, witnessing that the hypotheses and both relations are nonempty. -/
example :
    let readout : Fin 3 -> Bool := fun state =>
      if state = 2 then true else false
    let transition : Fin 3 -> Fin 3 := fun state =>
      if state = 1 then 2 else state
    PredictionEscape readout transition 1 0 1 /\
      ExpansionEscape readout (timeProjection readout transition 1) 0 1 := by
  dsimp
  have hPrediction :
      PredictionEscape
        (fun state : Fin 3 => if state = 2 then true else false)
        (fun state : Fin 3 => if state = 1 then 2 else state)
        1 0 1 := by
    exact ⟨by decide, 1, by decide, by decide⟩
  exact ⟨hPrediction,
    (prediction_escape_iff_expansion_escape _ _ _ _ _).mp hPrediction⟩

#print axioms prediction_escape_iff_expansion_escape

end D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape
