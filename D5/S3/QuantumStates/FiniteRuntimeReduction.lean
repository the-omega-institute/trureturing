/- GID: D5/S3/QuantumStates/FiniteRuntimeReduction
   generality: G
   mirror-B: D5/B/S3/QuantumStates/FiniteRuntimeReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite deterministic runtime semantics reduce to a product-state observation system with parameter bounds. -/

import Mathlib

namespace D5.S3.QuantumStates.FiniteRuntimeReduction

/-- The complete runtime state assembled from the five source state components. -/
abbrev RuntimeState (C K R M S : Type*) := C × K × R × M × S

/-- A finite b-bit slot encoding for a configuration with N parameter slots. -/
abbrev ParameterSlots (N b : Nat) := Fin N → Fin (2 ^ b)

/-- A deterministic observation system exposes its transition and readout maps. -/
structure ObservationSystem (Y O : Type*) where
  transition : Y → Y
  readout : Y → O

/- Library-search audit trail (2026-08-20):
   * Repository search found no theorem packaging the five-component runtime product,
     fixed-parameter observation maps, and the parameter-slot count together.
   * The nearest repository result is `D5.S3.ObserverMemory.Prediction.
     FiniteInputGeneratorPeriodicity`, which proves eventual periodicity only after
     a finite product system is already supplied; it does not cover this reduction.
   * Pinned-Mathlib exact hits `Fintype.card_prod`, `Fintype.card_fun`,
     `Fintype.card_fin`, and `Fintype.card_le_of_injective` are applied below.
   * The source's absence of uncounted external inputs is represented by an empty
     external-input type and by transition/readout functions whose only runtime
     argument is the complete product state. -/

/-- A fixed deterministic runtime has the finite product state and the stated
parameter bound; online learning extends that state with parameters and optimizer state. -/
theorem finite_precision_runtime_reduction
    {C K R M S O Theta External : Type*}
    [Fintype C] [Fintype K] [Fintype R] [Fintype M] [Fintype S] [Fintype O]
    [Fintype Theta] [IsEmpty External]
    (theta : Theta)
    (update : Theta → RuntimeState C K R M S → RuntimeState C K R M S)
    (readout : Theta → RuntimeState C K R M S → O)
    (N b : Nat)
    (parameterEncoding : Theta → ParameterSlots N b)
    (hParameterInjective : Function.Injective parameterEncoding)
    (onlineLearning : Prop) :
    ∃ system : ObservationSystem (RuntimeState C K R M S) O,
      system.transition = update theta ∧
      system.readout = readout theta ∧
      Fintype.card (RuntimeState C K R M S) =
        Fintype.card C * Fintype.card K * Fintype.card R *
          Fintype.card M * Fintype.card S ∧
      Fintype.card Theta ≤ 2 ^ (b * N) ∧
      (onlineLearning →
        ∀ (Optimizer : Type*) [Fintype Optimizer],
          Fintype.card (RuntimeState C K R M S × Theta × Optimizer) =
            Fintype.card (RuntimeState C K R M S) *
              Fintype.card Theta * Fintype.card Optimizer) := by
  refine ⟨{ transition := update theta, readout := readout theta }, rfl, rfl, ?_, ?_, ?_⟩
  · simp [RuntimeState, Fintype.card_prod, Nat.mul_assoc]
  · have hCard := Fintype.card_le_of_injective parameterEncoding hParameterInjective
    simpa [ParameterSlots, Fintype.card_fun, Nat.pow_mul] using hCard
  · intro _ Optimizer _
    simp [RuntimeState, Fintype.card_prod, Nat.mul_assoc]

example :
    ∃ system : ObservationSystem (RuntimeState Bool Bool Bool Bool Bool) Bool,
      system.transition = (fun state => state) ∧
      system.readout = (fun state : RuntimeState Bool Bool Bool Bool Bool => state.1) := by
  let idTransition : RuntimeState Bool Bool Bool Bool Bool →
      RuntimeState Bool Bool Bool Bool Bool := fun state => state
  let firstReadout : RuntimeState Bool Bool Bool Bool Bool → Bool := fun state => state.1
  refine ⟨{ transition := idTransition, readout := firstReadout }, rfl, rfl⟩

#print axioms finite_precision_runtime_reduction

end D5.S3.QuantumStates.FiniteRuntimeReduction
