import D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (d : ℕ) : Prop :=
  ∀ [NeZero d] (c b : ZMod d → ℂ), 2 ≤ d →
    (∑ j, ‖c j‖ ^ 2) = 1 → (∑ k, ‖b k‖ ^ 2) = 1 →
    averageEl1 d c b ≤ El1 d c * El1 d b / ((d : ℝ) - 1)

private theorem witness_exists : ∃ d : ℕ, ¬ predicate d := by
  classical
  exact not_forall.mp result

private def embed : Fin 1 → ℕ := fun _ => Classical.choose witness_exists

private def decision : ∀ witness : Fin 1, Decidable (predicate (embed witness)) :=
  fun _ => .isFalse (Classical.choose_spec witness_exists)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩

private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩

private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law

private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation.result
  in arena readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

end
end Reg.D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation
