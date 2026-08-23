/- GID: D5/S3/QuantumStates/FiniteRuntimeReductionOnline
   generality: G
   mirror-B: D5/B/S3/QuantumStates/FiniteRuntimeReductionOnline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite runtime semantics reduce to a product state with an online extension. -/

import Mathlib

namespace D5.S3.QuantumStates.FiniteRuntimeReductionOnline

abbrev RuntimeState (C K R M S : Type*) := C × K × R × M × S

abbrev ParameterSlots (N b : Nat) := Fin N → Fin (2 ^ b)

abbrev LearningState (C K R M S Theta Optimizer : Type*) :=
  RuntimeState C K R M S × Theta × Optimizer

structure ObservationSystem (Y O : Type*) where
  transition : Y → Y
  readout : Y → O

/-- Online learning is detected from a state update that changes a parameter or optimizer
and is observable against the same runtime state with the old values frozen. -/
def onlineLearningOccurred
    {C K R M S Theta Optimizer O : Type*}
    (step : LearningState C K R M S Theta Optimizer →
      LearningState C K R M S Theta Optimizer)
    (readout : LearningState C K R M S Theta Optimizer → O) : Prop :=
  ∃ state,
    ((step state).2.1 ≠ state.2.1 ∨ (step state).2.2 ≠ state.2.2) ∧
      readout (step state) ≠
        readout ⟨(step state).1, ⟨state.2.1, state.2.2⟩⟩

/- Library-search audit trail (2026-08-21):
   * Repository search found no exact theorem packaging the five-component runtime product,
     fixed-parameter observation maps, parameter-slot bound, and online-state extension.
   * Pinned-Mathlib exact hits `Fintype.card_prod`, `Fintype.card_fun`, `Fintype.card_fin`,
     and `Fintype.card_le_of_injective` are applied below.
   * The online clause is made falsifiable by requiring an actual parameter/optimizer mutation
     and an observable distinction from the same runtime state with frozen old values; this
     prevents the expanded-state and nonfactorization clauses from becoming vacuous.
   * No external-input channel is represented: deterministic update and readout are ordinary
     functions of the complete state, with no uncounted input argument. -/

/-- Fixed finite precision gives the runtime product; online changes require the expanded state. -/
theorem finite_precision_runtime_reduction_online
    {C K R M S O Theta Optimizer : Type*}
    [Fintype C] [Fintype K] [Fintype R] [Fintype M] [Fintype S] [Finite O]
    [Fintype Theta] [Fintype Optimizer]
    (theta : Theta)
    (update : Theta → RuntimeState C K R M S → RuntimeState C K R M S)
    (readout : Theta → RuntimeState C K R M S → O)
    (N b : Nat)
    (parameterEncoding : Theta → ParameterSlots N b)
    (hParameterInjective : Function.Injective parameterEncoding)
    (onlineUpdate : LearningState C K R M S Theta Optimizer →
      LearningState C K R M S Theta Optimizer)
    (onlineReadout : LearningState C K R M S Theta Optimizer → O) :
    ∃ system : ObservationSystem (RuntimeState C K R M S) O,
      system.transition = update theta ∧
      system.readout = readout theta ∧
      Fintype.card (RuntimeState C K R M S) =
        Fintype.card C * Fintype.card K * Fintype.card R *
          Fintype.card M * Fintype.card S ∧
      Fintype.card Theta ≤ 2 ^ (b * N) ∧
      (onlineLearningOccurred onlineUpdate onlineReadout →
        (∃ onlineSystem : ObservationSystem
            (LearningState C K R M S Theta Optimizer) O,
          onlineSystem.transition = onlineUpdate ∧
          onlineSystem.readout = onlineReadout ∧
          Fintype.card (LearningState C K R M S Theta Optimizer) =
            Fintype.card (RuntimeState C K R M S) * Fintype.card Theta *
              Fintype.card Optimizer ∧
          ∃ state,
            (onlineUpdate state).2.1 ≠ state.2.1 ∨
              (onlineUpdate state).2.2 ≠ state.2.2) ∧
        ¬ ∃ fixedReadout : RuntimeState C K R M S → O,
            ∀ state, fixedReadout state.1 = onlineReadout state) := by
  refine ⟨{ transition := update theta, readout := readout theta }, rfl, rfl, ?_, ?_, ?_⟩
  · simp [RuntimeState, Fintype.card_prod, Nat.mul_assoc]
  · have hCard := Fintype.card_le_of_injective parameterEncoding hParameterInjective
    simpa [ParameterSlots, Fintype.card_fun, Nat.pow_mul] using hCard
  · intro hOnline
    rcases hOnline with ⟨state, hchanged, hdist⟩
    refine ⟨⟨{ transition := onlineUpdate, readout := onlineReadout }, rfl, rfl, ?_,
      ⟨state, hchanged⟩⟩, ?_⟩
    · simp [LearningState, RuntimeState, Fintype.card_prod, Nat.mul_assoc]
    · intro hFixed
      rcases hFixed with ⟨fixedReadout, hfactor⟩
      apply hdist
      calc
        onlineReadout (onlineUpdate state) =
            fixedReadout (onlineUpdate state).1 := (hfactor (onlineUpdate state)).symm
        _ = fixedReadout (⟨(onlineUpdate state).1,
            ⟨state.2.1, state.2.2⟩⟩ : LearningState C K R M S Theta Optimizer).1 := rfl
        _ = onlineReadout ⟨(onlineUpdate state).1,
            ⟨state.2.1, state.2.2⟩⟩ := hfactor _

#print axioms finite_precision_runtime_reduction_online

end D5.S3.QuantumStates.FiniteRuntimeReductionOnline
