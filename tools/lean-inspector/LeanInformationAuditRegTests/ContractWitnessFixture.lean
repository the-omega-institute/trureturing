import LeanInformationAuditInterface.Contract.Registration

namespace LeanInformationAuditRegTests.ContractWitnessFixture
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape CounterexampleRecord

theorem result : ¬ ∀ n : Nat, n ≠ 0 := fun h => h 0 rfl

def arena : WitnessArena := WitnessArena.ofCarrier (Fin 1) Nat
  (fun n => n ≠ 0) (fun _ => 0) (fun _ => .isFalse (fun h => h rfl))

def actual := arena.realization

theorem positive : arena.Law actual := ⟨(⟨0, by decide⟩ : arena.State), rfl⟩
theorem bridge : WitnessPrimitiveRealization arena (¬ ∀ n : Nat, n ≠ 0) actual :=
  ⟨arena.law_refutes⟩
theorem variation : arena.Law actual ∧ ¬ arena.Law arena.constantTrue := arena.variation positive
theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena := arena.sensitivity positive

local instance : DecidableEq arena.State := arena.stateDecidableEq

def registration : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result WitnessArena WitnessArena (PrimitiveRealization arena.signature)
    (arena.Law actual ∧ ¬ arena.Law arena.constantTrue)
    (FiniteSlotSensitivity arena.toPrimitiveLawArena) (Type) Unit Unit := {
  targetName := `LeanInformationAuditRegTests.ContractWitnessFixture.result
  unitName := `ContractTests.witness.unit
  realizationName := `LeanInformationAuditRegTests.ContractWitnessFixture.bridge
  realizationSource := none
  generated := false
  arena := ⟨`LeanInformationAuditRegTests.ContractWitnessFixture.arena, arena⟩
  objectArena := ⟨`LeanInformationAuditRegTests.ContractWitnessFixture.arena, arena⟩
  catalog := `ContractTests.witness
  localNames := true
  realization := .witness arena actual actual.toPrimitiveBundle
    ⟨`LeanInformationAuditRegTests.ContractWitnessFixture.bridge, bridge⟩ positive
  readout := some actual
  variation := some ⟨`LeanInformationAuditRegTests.ContractWitnessFixture.variation, variation⟩
  sensitivity := some ⟨`LeanInformationAuditRegTests.ContractWitnessFixture.sensitivity, sensitivity⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end LeanInformationAuditRegTests.ContractWitnessFixture
