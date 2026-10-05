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

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,_} result (PrimitiveRealization arena.signature) (Type) Unit := {
  unitName := `ContractTests.witness.unit,
  realizationName := `LeanInformationAuditRegTests.ContractWitnessFixture.bridge,
  realizationSource := none,
  generated := false,
  arena := .witness ⟨arena⟩,
  objectArena := .witness ⟨arena⟩,
  catalog := `ContractTests.witness,
  localNames := true,
  realization := .witness arena actual actual.toPrimitiveBundle
    ⟨bridge⟩ positive (.evidence) (.evidence) (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization.toTheoremUnit bridge positive)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some actual,
  variation := {
    positive := .evidence ⟨variation⟩ (by exact (variation).1)
    negative := .evidence ⟨variation⟩ (by exact (variation).2) },
  sensitivity := .evidence ⟨sensitivity⟩ (by exact sensitivity),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


def missingPositive : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,_} result (PrimitiveRealization arena.signature) (Type) Unit := {
  unitName := `ContractTests.witness.missingPositive.unit,
  realizationName := `LeanInformationAuditRegTests.ContractWitnessFixture.bridge,
  realizationSource := none,
  generated := false,
  arena := .witness ⟨arena⟩,
  objectArena := .witness ⟨arena⟩,
  catalog := `ContractTests.witness,
  localNames := true,
  realization := .witness arena actual actual.toPrimitiveBundle
    ⟨bridge⟩ positive (.evidence) (.evidence) (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization.toTheoremUnit bridge positive)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some actual,
  variation := {
    positive := .unknown
    negative := .evidence ⟨variation⟩ (by exact (variation).2) },
  sensitivity := .evidence ⟨sensitivity⟩ (by exact sensitivity),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


def missingNegative : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,_} result (PrimitiveRealization arena.signature) (Type) Unit := {
  unitName := `ContractTests.witness.missingNegative.unit,
  realizationName := `LeanInformationAuditRegTests.ContractWitnessFixture.bridge,
  realizationSource := none,
  generated := false,
  arena := .witness ⟨arena⟩,
  objectArena := .witness ⟨arena⟩,
  catalog := `ContractTests.witness,
  localNames := true,
  realization := .witness arena actual actual.toPrimitiveBundle
    ⟨bridge⟩ positive (.evidence) (.evidence) (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization.toTheoremUnit bridge positive)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some actual,
  variation := {
    positive := .evidence ⟨variation⟩ (by exact (variation).1)
    negative := .absent },
  sensitivity := .evidence ⟨sensitivity⟩ (by exact sensitivity),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


def unsupportedSensitivity : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,_} result (PrimitiveRealization arena.signature) (Type) Unit := {
  unitName := `ContractTests.witness.unsupportedSensitivity.unit,
  realizationName := `LeanInformationAuditRegTests.ContractWitnessFixture.bridge,
  realizationSource := none,
  generated := false,
  arena := .witness ⟨arena⟩,
  objectArena := .witness ⟨arena⟩,
  catalog := `ContractTests.witness,
  localNames := true,
  realization := .witness arena actual actual.toPrimitiveBundle
    ⟨bridge⟩ positive (.evidence) (.evidence) (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization.toTheoremUnit bridge positive)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some actual,
  variation := {
    positive := .evidence ⟨variation⟩ (by exact (variation).1)
    negative := .evidence ⟨variation⟩ (by exact (variation).2) },
  sensitivity := .unsupported `LeanInformationAuditRegTests.ContractWitnessFixture.positive,
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end LeanInformationAuditRegTests.ContractWitnessFixture
