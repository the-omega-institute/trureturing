import Reg.ContractPrototype.Fixtures.Witness
import Reg.ContractPrototype.Templates.Counterexample
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

namespace Reg.ContractPrototype.ValidWitness
open LeanInformationAudit.Contract
open Reg.ContractPrototype.Fixtures.Witness
open D5.S3.ConceptDynamics.InformationEscape CounterexampleRecord EscapeRecord

def resultDeclaration : Registration result
    WitnessArena WitnessArena (PrimitiveRealization arena.signature)
    (arena.Law reads ∧ ¬ arena.Law arena.constantTrue)
    (LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena)
    Type (EscapeResidualWitness residualChain) Unit where
  targetName := `Reg.ContractPrototype.Fixtures.Witness.result
  arena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  objectArena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  catalog := `Reg.ContractPrototype.Fixtures.Witness.arena
  localNames := true
  realization := .witness arena reads reads.toPrimitiveBundle
    ⟨`Reg.ContractPrototype.Fixtures.Witness.bridge, bridge⟩ law
  readout := some (@counterexampleRealization (Fin 2) (fun _ : Fin 2 => false))
  variation := some ⟨`Reg.ContractPrototype.Fixtures.Witness.variation, variation⟩
  sensitivity := some ⟨`Reg.ContractPrototype.Fixtures.Witness.sensitivity, sensitivity⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .evidence ⟨`Reg.ContractPrototype.Fixtures.Witness.residual, residual⟩
  familyRecord := none
  options := {}

def secondDeclaration : Registration second
    WitnessArena WitnessArena (PrimitiveRealization arena.signature)
    (arena.Law reads ∧ ¬ arena.Law arena.constantTrue)
    (LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena)
    Type (EscapeResidualWitness residualChain) Unit where
  targetName := `Reg.ContractPrototype.Fixtures.Witness.second
  arena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  objectArena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  catalog := `Reg.ContractPrototype.Fixtures.Witness.arena
  localNames := true
  realization := .witness arena reads reads.toPrimitiveBundle
    ⟨`Reg.ContractPrototype.Fixtures.Witness.secondBridge, secondBridge⟩ law
  readout := some (@counterexampleRealization (Fin 2) (fun _ : Fin 2 => false))
  variation := some ⟨`Reg.ContractPrototype.Fixtures.Witness.variation, variation⟩
  sensitivity := some ⟨`Reg.ContractPrototype.Fixtures.Witness.sensitivity, sensitivity⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := {}

def thirdDeclaration : Registration third
    WitnessArena WitnessArena (PrimitiveRealization arena.signature)
    (arena.Law reads ∧ ¬ arena.Law arena.constantTrue)
    (LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena)
    Type (EscapeResidualWitness residualChain) Unit where
  targetName := `Reg.ContractPrototype.Fixtures.Witness.third
  arena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  objectArena := ⟨`Reg.ContractPrototype.Fixtures.Witness.arena, arena⟩
  catalog := `Reg.ContractPrototype.Fixtures.Witness.arena
  localNames := true
  realization := .witness arena reads reads.toPrimitiveBundle
    ⟨`Reg.ContractPrototype.Fixtures.Witness.thirdBridge, thirdBridge⟩ law
  readout := none
  variation := some ⟨`Reg.ContractPrototype.Fixtures.Witness.variation, variation⟩
  sensitivity := some ⟨`Reg.ContractPrototype.Fixtures.Witness.sensitivity, sensitivity⟩
  escapeFrom := none
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := {}

private def resultRow : ExpectedOccurrence where
  statement := ¬ claim
  proof := result
  theoremName := `Reg.ContractPrototype.Fixtures.Witness.result
  objectArenaName := `Reg.ContractPrototype.Fixtures.Witness.arena
  statementIdentity := none
  registrationModuleName := `Reg.ContractPrototype.ValidWitness

private def secondRow : ExpectedOccurrence where
  statement := ¬ claim
  proof := second
  theoremName := `Reg.ContractPrototype.Fixtures.Witness.second
  objectArenaName := `Reg.ContractPrototype.Fixtures.Witness.arena
  statementIdentity := none
  registrationModuleName := `Reg.ContractPrototype.ValidWitness

private def thirdRow : ExpectedOccurrence where
  statement := ¬ claim
  proof := third
  theoremName := `Reg.ContractPrototype.Fixtures.Witness.third
  objectArenaName := `Reg.ContractPrototype.Fixtures.Witness.arena
  statementIdentity := none
  registrationModuleName := `Reg.ContractPrototype.ValidWitness

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.ValidWitness
    expected := #[resultRow, secondRow]
    source := #[resultRow, secondRow, thirdRow]
    baseline := #[resultRow]
    companionPrefix := some `Reg.ContractPrototype.ValidWitness }
end Reg.ContractPrototype.ValidWitness
