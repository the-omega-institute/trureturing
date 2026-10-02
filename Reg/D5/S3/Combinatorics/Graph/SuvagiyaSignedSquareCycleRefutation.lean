import D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (m : Int) : Prop := 4 ≤ m →
  ∃ r : ℝ, IsGreatest quarticRoots r ∧ IsLeast (radiusValues (8 * m.toNat)) r

private theorem failure : ∃ m : Int, ¬ predicate m := by
  simpa only [claim, predicate, not_forall] using result

private def embed : Fin 1 → Int := fun _ => Classical.choose failure

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure)

private def arena := WitnessArena.ofCarrier (Fin 1) Int
  (fun m => predicate m) (fun w => embed w) (fun w => decision w)
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
  _root_.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) arena.check)
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Int) escape continues (open)

end
end Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
