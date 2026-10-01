import Reg.ContractPrototype.Fixtures.Witness
import Reg.Support.CounterexampleRecord

open Lean LeanInformationAudit
open Reg.ContractPrototype.Fixtures.Witness
open D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord

run_cmd do
  let env ← getEnv
  let row (name : Name) : SnapshotOccurrence := {
    objectArenaName := `Reg.ContractPrototype.Fixtures.Witness.arena
    theoremName := name
    capturedStatement := captureStatement env name
    registrationModuleName := `Reg.ContractPrototype.Controls.Witness }
  RootCatalogs.declare {
    rootId := `Reg.ContractPrototype.Controls.Witness
    expected := #[row `Reg.ContractPrototype.Fixtures.Witness.result,
      row `Reg.ContractPrototype.Fixtures.Witness.second]
    source := #[row `Reg.ContractPrototype.Fixtures.Witness.result,
      row `Reg.ContractPrototype.Fixtures.Witness.second, row `Reg.ContractPrototype.Fixtures.Witness.third]
    baseline := #[row `Reg.ContractPrototype.Fixtures.Witness.result]
    companionPrefix := some `Reg.ContractPrototype.Controls.Witness }


register_information_theorem result in arena
  readout via (@counterexampleRealization (Fin 2) (fun _ : Fin 2 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (Reg.ContractPrototype.Fixtures.Witness.residual)

register_information_theorem second in arena
  readout via (@counterexampleRealization (Fin 2) (fun _ : Fin 2 => false))
  primitives reads.toPrimitiveBundle realization secondBridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

register_information_theorem third in arena
  primitives reads.toPrimitiveBundle realization thirdBridge
  variation variation sensitivity sensitivity
