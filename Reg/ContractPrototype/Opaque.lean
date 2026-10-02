/- L0 原型 -/
import D5.S3.Resource.VandermondeHyperbolicRefutation
import Reg.ContractPrototype.Templates.Counterexample
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

namespace Reg.ContractPrototype.Opaque

open LeanInformationAudit
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Resource.MinimumRetrievalTime
open _root_.D5.S3.Resource.VandermondeHyperbolicRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (model : FiniteFieldModel) : Prop :=
  @hyperbolicBound model.carrier model.field

private theorem witness_exists : ∃ model : FiniteFieldModel, ¬ predicate model := by
  classical
  exact not_forall.mp _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.result

private def embed : Fin 2 → FiniteFieldModel :=
  fun _ => Classical.choose witness_exists

private def decision : ∀ witness : Fin 2, Decidable (predicate (embed witness)) :=
  fun _ => .isFalse (Classical.choose_spec witness_exists)

private def arena := WitnessArena.ofCarrier (Fin 2) FiniteFieldModel predicate embed decision
private opaque hiddenBit : Bool := false
private def reads := counterexampleRealization
  (fun i : Fin 2 => if i = 0 then false else if hiddenBit then true else false)

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 2), rfl⟩

private theorem bridge : WitnessPrimitiveRealization arena
    (¬ _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.claim) reads :=
  ⟨fun _ => _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.result⟩

private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law

private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

def declaration : Registration _root_.D5.S3.Resource.VandermondeHyperbolicRefutation.result
    WitnessArena WitnessArena
    (PrimitiveRealization arena.signature)
    (arena.Law reads ∧ ¬ arena.Law arena.constantTrue)
    (FiniteSlotSensitivity arena.toPrimitiveLawArena) (Type 1) Unit Unit where
  targetName := `D5.S3.Resource.VandermondeHyperbolicRefutation.result
  arena := ⟨``arena, arena⟩
  objectArena := ⟨``arena, arena⟩
  catalog := ``arena
  localNames := true
  realization := .witness arena reads (reads.toPrimitiveBundle) ⟨``bridge, bridge⟩ law
  readout := some (@counterexampleRealization (Fin 2) arena.check)
  variation := some ⟨``variation, variation⟩
  sensitivity := some ⟨``sensitivity, sensitivity⟩
  escapeFrom := some FiniteFieldModel
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := {}
end
end Reg.ContractPrototype.Opaque
