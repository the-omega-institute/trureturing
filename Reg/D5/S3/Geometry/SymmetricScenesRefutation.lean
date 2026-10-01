import D5.S3.Geometry.SymmetricScenesRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Geometry.SymmetricScenesRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Geometry.SymmetricScenesRefutation
open OriginalSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The complete original telescope after its outer dimension binder. -/
private def predicate (d : ℕ) : Prop :=
  ∀ (G P L : Type) [Group G] [Fintype G] [Fintype P] [Fintype L]
    (S : IncidenceGeometry d G P L) (A : Symmetry d G) (C : S.GainChart),
    S.globalCount A → S.subsetCounts A C →
      ∀ x : P → Space d, S.genericPicture A C x → S.minimallyFlat A x

private theorem failure : ∃ d : ℕ, ¬ predicate d := not_forall.mp result

/-- Select a failed original dimension; every geometry, action and picture remains quantified. -/
private def embed : Fin 1 → ℕ := fun _ => Classical.choose failure

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ liftingSufficiency) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.D5.S3.Geometry.SymmetricScenesRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

#print axioms failure
#print axioms bridge
#print axioms variation
#print axioms sensitivity

end

end Reg.D5.S3.Geometry.SymmetricScenesRefutation
