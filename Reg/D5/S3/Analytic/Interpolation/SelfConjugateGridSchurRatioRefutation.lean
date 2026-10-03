import D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (k : ℕ) : Prop :=
  ∀ n t : ℕ, k < n → n ≤ t → ∀ z : Fin n → ℂ,
    selfConjugate z → (∀ i, ‖z i‖ ≤ 1) →
      ‖Q t n k (z + 1)‖ ≤ 1 ∧
        ((∀ i, 0 ≤ (z i).re) →
          ‖schurHook (t - n) (n - k - 1) z‖ ≤ (t.choose n : ℝ) * ‖e (n - k) z‖)

private theorem failure_exists : ∃ k, ¬ predicate k := by
  classical
  exact not_forall.mp result

private def embed : Fin 1 → ℕ := fun _ => Classical.choose failure_exists

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure_exists)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

end

end Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
