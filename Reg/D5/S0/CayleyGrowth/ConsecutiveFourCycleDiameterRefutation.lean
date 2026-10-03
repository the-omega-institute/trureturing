import D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (n : ℕ) : Prop :=
  6 ≤ n → ∃ d : ℕ, (graph n).ediam = (d : ℕ∞) ∧ (d : ℚ) = formula n

private theorem failedPoint : ∃ n : ℕ, ¬ predicate n :=
  not_forall.mp result

private def embed : Fin 1 → ℕ := fun _ => Classical.choose failedPoint

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failedPoint)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ
  (fun n => 6 ≤ n → ∃ d : ℕ, (graph n).ediam = (d : ℕ∞) ∧ (d : ℚ) = formula n)
  embed decision
private def reads := arena.realization

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) arena.check)
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

end
end Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
