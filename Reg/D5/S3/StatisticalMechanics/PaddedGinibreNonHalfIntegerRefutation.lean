import D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

noncomputable section

open LeanInformationAudit Matrix Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def predicate (η : ℝ) : Prop :=
  0 < η → ∀ (n q L : ℕ) (A : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (ρ : (Fin n → ℤ) →+ (Fin L → ZMod 2)),
    0 < q → (∀ j, (A j).PosSemidef) → (∑ j, A j).PosDef →
    ∀ (m : ℕ) (V : Fin m → Fin n → ℕ) (ε : Fin m → ℤ) (u : Fin n → ℕ),
      evenIndex ρ (Matrix.vecMul (fun _ => 1) V) → (∀ i, ε i = 1 ∨ ε i = -1) →
      (∀ j, 0 < u j) → evenIndex ρ u → 0 ≤ pggSum A ρ V ε u η

private theorem failure : ∃ η, ¬ predicate η := not_forall.mp result

private noncomputable def embed : Fin 1 → ℝ := fun _ => Classical.choose failure

private noncomputable def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure)

private noncomputable def arena := WitnessArena.ofCarrier (Fin 1) ℝ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Real) escape continues (open)

end

end Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation
